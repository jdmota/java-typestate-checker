package jatyc.core.adapters

import com.sun.source.tree.*
import com.sun.tools.javac.code.Flags
import com.sun.tools.javac.code.Symbol
import com.sun.tools.javac.code.Type
import com.sun.tools.javac.tree.JCTree
import jatyc.JavaTypestateChecker
import jatyc.core.*
import jatyc.core.cfg.*
import jatyc.utils.JTCUtils
import org.checkerframework.dataflow.analysis.Store
import org.checkerframework.dataflow.cfg.ControlFlowGraph
import org.checkerframework.dataflow.cfg.UnderlyingAST
import org.checkerframework.dataflow.cfg.block.*
import org.checkerframework.dataflow.cfg.node.*
import org.checkerframework.framework.flow.CFCFGBuilder
import org.checkerframework.framework.type.AnnotatedTypeMirror
import org.checkerframework.framework.util.AnnotatedTypes
import org.checkerframework.javacutil.AnnotationUtils
import org.checkerframework.javacutil.ElementUtils
import org.checkerframework.javacutil.TreePathUtil
import org.checkerframework.javacutil.TreeUtils
import org.checkerframework.org.plumelib.util.WeakIdentityHashMap
import java.util.*
import javax.annotation.processing.ProcessingEnvironment
import javax.lang.model.element.ExecutableElement
import javax.lang.model.element.Modifier
import javax.lang.model.element.VariableElement
import javax.lang.model.type.ArrayType
import javax.lang.model.type.TypeMirror

fun Symbol.MethodSymbol.isPublic(): Boolean {
  return flags_field and Flags.AccessFlags.toLong() == Flags.PUBLIC.toLong()
}

fun Symbol.MethodSymbol.isAbstract(): Boolean {
  return flags_field and Flags.ABSTRACT.toLong() != 0L
}

fun Symbol.MethodSymbol.getCorrectReceiverType(): Type {
  // Because this.getReceiverType() might return null
  return ElementUtils.enclosingTypeElement(this)!!.asType() as Type
}

private fun isSideEffectFree(utils: JTCUtils, hierarchy: JavaTypesHierarchy, method: Symbol.MethodSymbol): Boolean {
  /*if (method.isStatic) {
    return utils.factory.isSideEffectFree(method)
  }*/
  val receiver = hierarchy.get(method.getCorrectReceiverType())
  if (method.simpleName.toString() == "<init>") {
    if (receiver.isJavaObject()) {
      // java.lang.Object's constructor is side effect free
      return true
    }
    if (receiver.isJavaEnum()) {
      // java.lang.Enum's constructor is side effect free
      return true
    }
  }
  if (receiver.isImmutable()) {
    return true
  }
  return false // return utils.factory.isSideEffectFree(method)
}

sealed class AdaptResult {
  abstract val code: CodeExpr
  fun set(node: Node?): AdaptResult {
    code.set(node)
    return this
  }

  fun set(tree: Tree?): AdaptResult {
    code.set(tree)
    return this
  }

  fun set(type: TypeMirror?): AdaptResult {
    code.set(type)
    return this
  }

  abstract fun toList(): List<CodeExpr>
}

class SingleAdaptResult(override val code: CodeExpr) : AdaptResult() {
  override fun toList() = listOf(code)
}

class MultipleAdaptResult(val list: List<CodeExpr>) : AdaptResult() {
  override val code = list.last()
  override fun toList() = list
}

class FunctionInterfaces(private val hierarchy: JavaTypesHierarchy, private val transformer: (Symbol.MethodSymbol) -> FuncInterface) {

  private val interfaces = mutableMapOf<MethodSymbolWrapper, FuncInterface>()

  // TODO check thrown exceptions and type parameters
  private inner class MethodSymbolWrapper(val sym: Symbol.MethodSymbol) {
    override fun equals(other: Any?): Boolean {
      if (this === other) return true
      if (other !is MethodSymbolWrapper) return false
      val a = sym
      val b = other.sym
      if (a === b) return true
      return a.name.toString() == b.name.toString() &&
        hierarchy.sameType(a.getCorrectReceiverType(), b.getCorrectReceiverType()) &&
        hierarchy.sameType(a.returnType, b.returnType) &&
        a.params().map { hierarchy.get(it.asType()) } == b.params().map { hierarchy.get(it.asType()) }
    }

    override fun hashCode(): Int {
      return sym.name.toString().hashCode()
    }
  }

  fun transform(sym: ExecutableElement): FuncInterface {
    return interfaces.computeIfAbsent(MethodSymbolWrapper(sym as Symbol.MethodSymbol)) { transformer(it.sym) }
  }
}

class VariableRenamer(private val hierarchy: JavaTypesHierarchy) {

  private var varSymbolsUuid = 1L
  private val varSymbols = mutableMapOf<VarSymbolWrapper, Long>()

  private class VarSymbolWrapper(val sym: Symbol.VarSymbol) {
    override fun equals(other: Any?): Boolean {
      // Adapted from org.checkerframework.dataflow.expression.LocalVariable.sameElement
      return other is VarSymbolWrapper && sym.pos == other.sym.pos
        && sym.name.contentEquals(other.sym.name)
        && sym.owner.toString() == other.sym.owner.toString()
    }

    override fun hashCode(): Int {
      return sym.name.toString().hashCode()
    }
  }

  fun transformLocal(node: LocalVariableNode): Id {
    val sym = VarSymbolWrapper(node.element as Symbol.VarSymbol)
    val id = varSymbols.computeIfAbsent(sym) { varSymbolsUuid++ }
    return Id(node.name, id)
  }

  fun transformThis(typeMirror: TypeMirror): Id {
    val type = hierarchy.get(typeMirror as Type)
    return Id("this", type.id)
  }

  fun transformSelect(obj: CodeExpr, elem: VariableElement): Select {
    val sym = VarSymbolWrapper(elem as Symbol.VarSymbol)
    val id = varSymbols.computeIfAbsent(sym) { varSymbolsUuid++ }
    return Select(obj, elem.simpleName.toString(), id)
  }

  fun transformDecl(tree: VariableTree): IdLHS {
    val sym = VarSymbolWrapper(TreeUtils.elementFromDeclaration(tree) as Symbol.VarSymbol)
    val id = varSymbols.computeIfAbsent(sym) { varSymbolsUuid++ }
    return IdLHS(tree.name.toString(), id)
  }

  fun transformDecl(node: VariableDeclarationNode): IdLHS {
    return transformDecl(node.tree!!)
  }

  fun transformLocalLHS(node: LocalVariableNode): IdLHS {
    val sym = VarSymbolWrapper(node.element as Symbol.VarSymbol)
    val id = varSymbols.computeIfAbsent(sym) { varSymbolsUuid++ }
    return IdLHS(node.name, id)
  }

  fun transformParamLHS(varSym: Symbol.VarSymbol): IdLHS {
    val sym = VarSymbolWrapper(varSym)
    val id = varSymbols.computeIfAbsent(sym) { varSymbolsUuid++ }
    return IdLHS(varSym.simpleName.toString(), id)
  }

  fun transformThisLHS(typeMirror: TypeMirror): IdLHS {
    val type = hierarchy.get(typeMirror as Type)
    return IdLHS("this", type.id)
  }

  fun transformSelectLHS(obj: CodeExpr, elem: VariableElement): SelectLHS {
    val sym = VarSymbolWrapper(elem as Symbol.VarSymbol)
    val id = varSymbols.computeIfAbsent(sym) { varSymbolsUuid++ }
    return SelectLHS(obj, elem.simpleName.toString(), id)
  }

}

private fun checkersFlowRuleToSimpleFlowRule(rule: Store.FlowRule): SimpleFlowRule {
  return when (rule) {
    Store.FlowRule.EACH_TO_EACH -> SimpleFlowRule.EACH_TO_EACH
    Store.FlowRule.THEN_TO_BOTH -> SimpleFlowRule.THEN_TO_BOTH
    Store.FlowRule.ELSE_TO_BOTH -> SimpleFlowRule.ELSE_TO_BOTH
    Store.FlowRule.THEN_TO_THEN -> SimpleFlowRule.THEN_TO_THEN
    Store.FlowRule.ELSE_TO_ELSE -> SimpleFlowRule.ELSE_TO_ELSE
    Store.FlowRule.BOTH_TO_THEN -> SimpleFlowRule.BOTH_TO_THEN
    Store.FlowRule.BOTH_TO_ELSE -> SimpleFlowRule.BOTH_TO_ELSE
  }
}

class CFAdapter(
  val checker: JavaTypestateChecker,
  private val hierarchy: JavaTypesHierarchy,
  private val typeIntroducer: TypeIntroducer
) {
  private val utils get() = checker.utils
  private val processingEnv: ProcessingEnvironment = checker.processingEnvironment
  private lateinit var root: JCTree.JCCompilationUnit

  private var renamer = VariableRenamer(hierarchy)

  private fun shouldBeAnytime(method: Symbol.MethodSymbol): Boolean {
    return when {
      method.simpleName.toString() == "<init>" -> false
      method.isStatic -> true
      !method.isPublic() -> true
      else -> {
        val graph = utils.classUtils.getGraph(method.getCorrectReceiverType())
        if (graph == null) {
          true
        } else {
          val env = graph.getEnv()
          graph.getAllTransitions().none { utils.methodUtils.sameErasedMethod(env, method, it.original) } ||
            AnnotatedTypes.overriddenMethods(utils.elementUtils, utils.factory.getProvider(), method).any { shouldBeAnytime(it.value as Symbol.MethodSymbol) }
        }
      }
    }
  }

  private var funcInterfaces = FunctionInterfaces(hierarchy) {
    val funcName = it.simpleName.toString()
    // Because it.getReceiverType() might return null
    val receiver = it.getCorrectReceiverType()
    val isPublic = it.isPublic()
    val isPure = isSideEffectFree(utils, hierarchy, it)
    val isConstructor = funcName == "<init>"
    val isAbstract = it.isAbstract()
    val isAnytime = shouldBeAnytime(it)
    val thisParam = if (it.isStatic) {
      emptyList()
    } else {
      val thisType = typeIntroducer.getThisType(receiver, isAnytime = isAnytime, isConstructor = isConstructor)
      listOf(FuncParam(renamer.transformThisLHS(receiver), thisType, thisType, isThis = true, hierarchy.get(receiver), hasEnsures = false))
    }
    val params = if (isConstructor && receiver.toString() == "java.lang.Enum<E>") {
      // It seems the java.lang.Enum constructor has more parameters (String, Int), but is called with zero
      // Thus, when defining the functional interface, assume there is only one parameter, the "this"
      thisParam
    } else {
      thisParam.plus(getParamTypes(it))
    }
    FuncInterface(funcName, params, getReturnType(it).first, isPublic = isPublic, isAnytime = isAnytime, isPure = isPure, isAbstract = isAbstract).set(it.asType())
  }

  fun setRoot(root: CompilationUnitTree) {
    this.root = root as JCTree.JCCompilationUnit
    utils.factory.setRoot(root)
  }

  private fun getFieldType(tree: VariableTree): JTCType {
    val type = utils.factory.getAnnotatedType(tree)
    return typeIntroducer.getFieldUpperBound(tree, type)
  }

  private fun getParamTypes(sym: Symbol.MethodSymbol): List<FuncParam> {
    val type = utils.factory.getAnnotatedType(sym) as AnnotatedTypeMirror.AnnotatedExecutableType
    return getParamTypes(type, sym.params())
  }

  private fun getReturnType(tree: JCTree.JCMethodDecl): Pair<JTCType, JavaType> {
    return getReturnType(tree.sym)
  }

  private fun getReturnType(sym: Symbol.MethodSymbol): Pair<JTCType, JavaType> {
    val type = utils.factory.getAnnotatedType(sym) as AnnotatedTypeMirror.AnnotatedExecutableType
    return getReturnType(type)
  }

  private fun getParamTypes(tree: JCTree.JCLambda): List<FuncParam> {
    val type = utils.factory.getFunctionTypeFromTree(tree)
    return getParamTypes(type, tree.params.map { it.sym })
  }

  private fun getReturnType(tree: JCTree.JCLambda): Pair<JTCType, JavaType> {
    val type = utils.factory.getFunctionTypeFromTree(tree)
    return getReturnType(type)
  }

  private fun getParamTypes(type: AnnotatedTypeMirror.AnnotatedExecutableType, names: List<Symbol.VarSymbol>): List<FuncParam> {
    val params = names.iterator()
    val paramTypes = type.parameterTypes.iterator()
    val funcParams = mutableListOf<FuncParam>()
    while (params.hasNext()) {
      val param = params.next()
      val paramType = paramTypes.next()
      funcParams.add(FuncParam(
        renamer.transformParamLHS(param),
        requires = typeIntroducer.get(paramType, TypeIntroOpts(annotation = JTCUtils.jtcRequiresAnno)).toMaybeNullable(typeIntroducer.acceptsNull(type)),
        ensures = typeIntroducer.get(paramType, TypeIntroOpts(annotation = JTCUtils.jtcEnsuresAnno)),
        isThis = false,
        javaType = hierarchy.get(paramType.underlyingType),
        hasEnsures = JTCUtils.hasAnnotation(paramType, JTCUtils.jtcEnsuresAnno)
      ))
    }
    return funcParams
  }

  private fun getReturnType(type: AnnotatedTypeMirror.AnnotatedExecutableType): Pair<JTCType, JavaType> {
    return Pair(
      if (typeIntroducer.terminates(type)) {
        JTCBottomType.SINGLETON
      } else {
        // If the return type has annotations or we are sure we have access to the method's code, the return type is not nullable
        if (type.returnType.annotations.any { AnnotationUtils.annotationName(it) == JTCUtils.jtcEnsuresAnno } || !ElementUtils.isElementFromByteCode(type.element)) {
          typeIntroducer.get(type.returnType, TypeIntroOpts(annotation = JTCUtils.jtcEnsuresAnno))
        } else {
          if (typeIntroducer.returnsNonNull(type)) {
            typeIntroducer.get(type.returnType, typeIntroducer.nonNullableShared)
          } else {
            typeIntroducer.get(type.returnType, typeIntroducer.nullableShared)
          }
        }
      },
      hierarchy.get(type.underlyingType)
    )
  }

  private fun getInitialType(method: Symbol.MethodSymbol): JTCType {
    return typeIntroducer.getInitialType(method.getCorrectReceiverType())
  }

  private val classesStack = Stack<JCTree.JCClassDecl>()
  private val methodsStack = Stack<Tree>()

  private val modifiersIsStatic = { it: ModifiersTree -> it.flags.contains(Modifier.STATIC) }
  private val modifiersIsNotStatic = { it: ModifiersTree -> !it.flags.contains(Modifier.STATIC) }

  private object PosComparator : Comparator<Pair<SimpleCFG, Int>> {
    override fun compare(o1: Pair<SimpleCFG, Int>, o2: Pair<SimpleCFG, Int>): Int {
      return o1.second.compareTo(o2.second)
    }
  }

  private fun transformClass(classTree: JCTree.JCClassDecl, isStatic: Boolean): ClassDecl {
    val filter = if (isStatic) modifiersIsStatic else modifiersIsNotStatic
    val graph = if (isStatic) null else utils.classUtils.visitClassSymbol(classTree.sym)
    val thisRef = if (isStatic) null else Reference.make(renamer.transformThis(classTree.type))

    val fields = mutableListOf<FieldDeclaration>()
    val methods = mutableListOf<FuncDeclaration>()
    val overrides = mutableMapOf<FuncDeclaration, List<FuncInterface>>()
    val publicMethods = mutableListOf<FuncDeclaration>()
    val nonPublicMethods = mutableListOf<FuncDeclaration>()
    val classes = mutableListOf<ClassDeclAndCompanion>()

    // Static fields/initializers are executed when a class is first loaded in textual order
    // Instance fields/initializers are executed when an object is instantiated in textual order
    val initializers = TreeSet(PosComparator)

    // Store the fields information
    // If they have initializers, build their CFG and store them for later
    for (field in classTree.members.filterIsInstance(VariableTree::class.java).filter { filter(it.modifiers) }) {
      if (field.initializer != null) {
        initializers.add(Pair(processCFG(field), (field as JCTree).pos))
      }
      fields.add(FieldDeclaration(
        renamer.transformDecl(field),
        getFieldType(field),
        isPrivate = field.modifiers.flags.contains(Modifier.PRIVATE),
        isProtected = field.modifiers.flags.contains(Modifier.PROTECTED),
        isPublic = field.modifiers.flags.contains(Modifier.PUBLIC),
      ).set(field).set(root).set(checker))
    }

    // Build the blocks CFGs and store them for later
    for (block in classTree.members.filterIsInstance(BlockTree::class.java)) {
      if (if (isStatic) block.isStatic else !block.isStatic) {
        initializers.add(Pair(processCFG(block), (block as JCTree).pos))
      }
    }

    var hasDeclaredConstructor = false

    // Build the CFGs of the methods
    for (method in classTree.members.filterIsInstance(MethodTree::class.java).filter { filter(it.modifiers) }) {
      val sym = (method as JCTree.JCMethodDecl).sym
      val cfg = processCFG(method)
      // If the method is a constructor, we want to include the initialization code
      val func = if (sym.isConstructor) {
        // For performance, mutate "initializers" and then remove the last added item
        val pair = Pair(cfg, Int.MAX_VALUE)
        initializers.add(pair)
        val joinedCfg = joinCFGs(initializers.map { it.first })
        initializers.remove(pair)
        hasDeclaredConstructor = true
        transformMethod(method, joinedCfg)
      } else {
        transformMethod(method, cfg)
      }
      methods.add(func)
      if (sym.modifiers.contains(Modifier.PUBLIC)) {
        publicMethods.add(func)
      } else {
        nonPublicMethods.add(func)
      }

      overrides[func] = AnnotatedTypes.overriddenMethods(utils.elementUtils, utils.factory.getProvider(), sym).map { funcInterfaces.transform(it.value) }
    }

    if (!hasDeclaredConstructor && initializers.isNotEmpty()) {
      if (isStatic) {
        val cfg = joinCFGs(initializers.map { it.first })
        val method = FuncDeclaration("<init>", listOf(), cfg, JTCNullType.SINGLETON, isPublic = true, isAnytime = true, isPure = false, isAbstract = false).set(classTree).set(root).set(checker)
        methods.add(method)
        publicMethods.add(method)
      } else {
        // The Checker Framework should always give us a constructor, but just make sure
        error("Missing constructor in class ${classTree.simpleName}")
      }
    }

    // Transform and store inner classes
    for (tree in classTree.members.filterIsInstance(ClassTree::class.java).filter { filter(it.modifiers) }) {
      classes.add(transformClass(tree as JCTree.JCClassDecl))
    }

    val extensions = mutableListOf<String>()
    if (!isStatic) {
      val extends = classTree.extendsClause
      if (extends != null) {
        val superTypeSymbol = extends.type.asElement()
        extensions.add(superTypeSymbol.qualifiedName.toString())
      }

      for (implementing in classTree.implementing) {
        val typeSymbol = implementing.type.asElement()
        extensions.add(typeSymbol.qualifiedName.toString())
      }
    }

    val clazz = ClassDecl(
      classTree.simpleName.toString(),
      fields,
      methods,
      publicMethods,
      nonPublicMethods,
      classes,
      extensions,
      overrides,
      thisRef,
      graph
    ).set(classTree).set(root).set(checker)
    for (m in methods) {
      m.clazz = clazz
    }
    return clazz
  }

  private val transformedClasses = WeakIdentityHashMap<JCTree.JCClassDecl, ClassDeclAndCompanion>()

  fun transformClass(classTree: JCTree.JCClassDecl): ClassDeclAndCompanion {
    return transformedClasses.computeIfAbsent(classTree) {
      classesStack.push(classTree)
      val staticClass = transformClass(classTree, isStatic = true)
      val nonStaticClass = transformClass(classTree, isStatic = false)
      classesStack.pop()
      ClassDeclAndCompanion(nonStatic = nonStaticClass, static = staticClass).set(classTree).set(root).set(checker)
    }
  }

  private fun transformMethod(method: Symbol.MethodSymbol): FuncInterface {
    return funcInterfaces.transform(method)
  }

  private fun transformMethod(method: JCTree.JCMethodDecl, cfg: SimpleCFG): FuncDeclaration {
    val func = funcInterfaces.transform(method.sym)
    return FuncDeclaration(func.name, func.parameters, cfg, func.returnType, isPublic = func.isPublic, isAnytime = func.isAnytime, isPure = func.isPure, isAbstract = func.isAbstract).set(method).set(root).set(checker)
  }

  private fun treeToAst(tree: Tree, classTree: JCTree.JCClassDecl): UnderlyingAST {
    return when (tree) {
      is VariableTree -> UnderlyingAST.CFGStatement(tree, classTree)
      is BlockTree -> UnderlyingAST.CFGStatement(tree, classTree)
      is MethodTree -> UnderlyingAST.CFGMethod(tree, classTree)
      is LambdaExpressionTree -> {
        val mt = TreePathUtil.enclosingOfKind(utils.getPath(tree, root), Tree.Kind.METHOD) as MethodTree
        UnderlyingAST.CFGLambda(tree, classTree, mt)
      }
      else -> error("Unexpected tree ${tree.javaClass}")
    }
  }

  private fun processCFG(tree: Tree): SimpleCFG {
    if (tree is MethodTree) {
      if (tree.modifiers.flags.contains(Modifier.NATIVE)) {
        return createOneExprCFG(NoOPExpr("native method")) // TODO should be an expression that invalidates the information right?
      } else if (tree.modifiers.flags.contains(Modifier.ABSTRACT) || tree.body == null) {
        // Note that abstract methods in an interface have a null body but do not have an ABSTRACT flag
        return createOneExprCFG(ThrowExpr(null))
      }
    }
    val ast = treeToAst(tree, classesStack.peek())
    methodsStack.push(tree)
    val cfg = checkersCFGtoSimpleCFG(CFCFGBuilder.build(root, ast, processingEnv))
    methodsStack.pop()
    return cfg
  }

  private fun checkersCFGtoSimpleCFG(original: ControlFlowGraph): SimpleCFG {
    val seen = IdentityHashMap<Block, SimpleNode>()
    val cfg = SimpleCFG()
    connect(cfg, seen, cfg.entry, original.entryBlock, SimpleFlowRule.EACH_TO_EACH)
    return cfg
  }

  private fun connect(cfg: SimpleCFG, seen: IdentityHashMap<Block, SimpleNode>, prev: SimpleNode, block: Block, flowRule: Store.FlowRule) {
    return connect(cfg, seen, prev, block, checkersFlowRuleToSimpleFlowRule(flowRule))
  }

  private fun connect(cfg: SimpleCFG, seen: IdentityHashMap<Block, SimpleNode>, prev: SimpleNode, block: Block, flowRule: SimpleFlowRule) {
    if (seen.containsKey(block)) {
      prev.addOutEdge(SimpleEdge(flowRule, seen[block]!!))
      return
    }
    when (block) {
      is RegularBlock -> {
        var first = true
        var last = prev
        var lastFlow = flowRule
        for (n in block.nodes) {
          last = connect(cfg, last, n, lastFlow)
          lastFlow = SimpleFlowRule.EACH_TO_EACH
          if (first) {
            seen[block] = last
            first = false
          }
        }
        block.successor?.let { connect(cfg, seen, last, it, block.flowRule) }
      }
      is ExceptionBlock -> {
        val last = connect(cfg, prev, block.node, flowRule)
        seen[block] = last
        block.successor?.let { connect(cfg, seen, last, it, block.flowRule) }
        // TODO
        /*for ((cause, value) in block.exceptionalSuccessors) {
          for (exceptionSucc in value) {
            connect(cfg, seen, prev, exceptionSucc, SimpleFlowRule.BOTH_TO_BOTH)
          }
        }*/
      }
      is ConditionalBlock -> {
        if (prev is SimpleCodeNode) {
          prev.isCondition = true
        }
        block.thenSuccessor?.let { connect(cfg, seen, prev, it, block.thenFlowRule) }
        block.elseSuccessor?.let { connect(cfg, seen, prev, it, block.elseFlowRule) }
      }
      is SpecialBlock -> {
        block.successor?.let { connect(cfg, seen, prev, it, block.flowRule) }
        when (block.specialType!!) {
          SpecialBlock.SpecialBlockType.ENTRY -> {
          }
          SpecialBlock.SpecialBlockType.EXIT -> {
            prev.addOutEdge(SimpleEdge(flowRule, cfg.exit))
          }
          SpecialBlock.SpecialBlockType.EXCEPTIONAL_EXIT -> {
            // TODO
          }
        }
      }
      else -> throw RuntimeException("Unexpected block type: ${block.type}")
    }
  }

  private val adaptedCache = IdentityHashMap<Node, AdaptResult>()

  private fun connect(cfg: SimpleCFG, prev: SimpleNode, node: Node, flowRule: SimpleFlowRule): SimpleNode {
    return when (val result = adaptedCache.computeIfAbsent(node) { transformHelper(it) }) {
      is MultipleAdaptResult -> {
        var first = true
        var lastNode = prev
        for (c in result.list) {
          val simpleNode = SimpleCodeNode(c)
          c.set(root).set(checker)

          cfg.allNodes.add(simpleNode)
          lastNode.addOutEdge(SimpleEdge(if (first) flowRule else SimpleFlowRule.BOTH_TO_BOTH, simpleNode))
          lastNode = simpleNode
          if (first) {
            first = false
          }
        }
        lastNode
      }
      is SingleAdaptResult -> {
        val simpleNode = SimpleCodeNode(result.code)
        result.code.set(root).set(checker)

        cfg.allNodes.add(simpleNode)
        prev.addOutEdge(SimpleEdge(flowRule, simpleNode))
        simpleNode
      }
    }
  }

  private fun transformLHS(node: Node): LeftHS {
    return when (node) {
      is ThisNode -> renamer.transformThisLHS(node.type).set(node)
      is LocalVariableNode -> renamer.transformLocalLHS(node).set(node)
      is FieldAccessNode -> renamer.transformSelectLHS(getAdapted(node.receiver), node.element).set(node)
      else -> error("Unexpected ${node.javaClass} in LHS - $node")
    }
  }

  private fun getAdapted(node: Node): CodeExpr {
    var code = adaptedCache.computeIfAbsent(node) { transformHelper(it) }.code
    // Prefer the casted expression,
    // except when the type is primitive (in that case the cast is a conversion)
    while (code is CastExpr && code.type !is JTCPrimitiveType) {
      code = code.expr
    }
    return code
  }

  private fun makeTypeRef(type: TypeMirror): SymbolResolveExpr {
    return SymbolResolveExpr(typeIntroducer.getUpperBound(type), hierarchy.get(type as Type))
  }

  private fun makeCast(what: CodeExpr, type: TypeMirror): CastExpr {
    return CastExpr(what, typeIntroducer.getCastType(type), hierarchy.get(type))
  }

  private fun makeAssignment(left: Node, right: CodeExpr, node: Node): AdaptResult {
    return when (left) {
      is ArrayAccessNode -> {
        val type = left.array.type as ArrayType
        val componentType = typeIntroducer.getArrayComponentType(type.componentType)
        val thisType = typeIntroducer.getThisType(type, isAnytime = true, isConstructor = false)
        val params = listOf(
          FuncParam(renamer.transformThisLHS(type), thisType, thisType, isThis = true, hierarchy.get(type), hasEnsures = false),
          FuncParam(IdLHS("index", 0), hierarchy.INTEGER, hierarchy.INTEGER, isThis = false, hierarchy.INTEGER.javaType, hasEnsures = false),
          FuncParam(IdLHS("value", 0), componentType, componentType, isThis = false, hierarchy.get(type.componentType), hasEnsures = false)
        )
        makeCall2(
          FuncInterface("#helpers.arraySet", params, returnType = componentType, isPublic = true, isAnytime = true, isPure = false, isAbstract = false),
          listOf(left.array, left.index).map(::getAdapted).plus(right),
          node
        )
      }
      else -> SingleAdaptResult(Assign(transformLHS(left), right, typeIntroducer.getUpperBound(left.type), hierarchy.get(left.type)).set(node))
    }
  }

  private fun makeReturn(node: Node, result: Node?): CodeExpr {
    val (type, javaType) = when (val enclosing = methodsStack.peek()) {
      is JCTree.JCMethodDecl -> getReturnType(enclosing)
      is JCTree.JCLambda -> getReturnType(enclosing)
      else -> error("Unexpected enclosing method ${enclosing::class.java}")
    }
    return Return(if (result == null) null else getAdapted(result), type, javaType).set(node)
  }

  private fun makeCall2(methodExpr: FuncInterface, parameters: List<CodeExpr>, cfNode: Node): AdaptResult {
    val tree = cfNode.tree
    val isSuperCall = if (tree is MethodInvocationTree) {
      val select = tree.methodSelect
      select is IdentifierTree && select.name.contentEquals("super")
    } else false
    val params = parameters.mapIndexed { i, p -> ParamAssign(i, p).set(p.cfTree).set(p.cfNode) }
    val call = MethodCall(methodExpr, params, isSuperCall).set(cfNode)
    return MultipleAdaptResult(params.plus(call)).set(cfNode)
  }

  private fun makeCall(methodExpr: FuncInterface, parameters: List<Node>, cfNode: Node): AdaptResult {
    return makeCall2(methodExpr, parameters.map(::getAdapted), cfNode)
  }

  // See https://github.com/typetools/checker-framework/tree/master/dataflow/src/main/java/org/checkerframework/dataflow/cfg/node
  private fun transformHelper(node: Node): AdaptResult {
    val t = ::getAdapted
    return when (node) {
      is ArrayAccessNode -> {
        val type = node.array.type as ArrayType
        val componentType = typeIntroducer.getArrayComponentType(type.componentType)
        val thisType = typeIntroducer.getThisType(type, isAnytime = true, isConstructor = false)
        val params = listOf(
          FuncParam(renamer.transformThisLHS(type), thisType, thisType, isThis = true, hierarchy.get(type), hasEnsures = false),
          FuncParam(IdLHS("index", 0), hierarchy.INTEGER, hierarchy.INTEGER, isThis = false, hierarchy.INTEGER.javaType, hasEnsures = false)
        )
        makeCall(
          FuncInterface("#helpers.arrayAccess", params, returnType = componentType, isPublic = true, isAnytime = true, isPure = true, isAbstract = false),
          listOf(node.array, node.index),
          node
        )
      }
      is ArrayCreationNode -> {
        val type = node.type as ArrayType
        val javaType = hierarchy.get(type)
        val javaComponentType = hierarchy.get(type.componentType)
        val componentType = typeIntroducer.getArrayComponentType(type.componentType)
        SingleAdaptResult(if (node.dimensions.isNotEmpty()) {
          NewArrayWithDimensions(JTCSharedType(javaType), javaType, componentType, javaComponentType, node.dimensions.map(t))
        } else {
          NewArrayWithValues(JTCSharedType(javaType), javaType, componentType, javaComponentType, node.initializers.map(t))
        }).set(node)
      }
      is ArrayTypeNode -> error("Unexpected node ${node.javaClass}")
      is AssertionErrorNode -> TODO("assertion not implemented") // makeCall(helperToFuncInterface("#helpers.assertion"), listOf(node.condition, node.detail), node)
      is AssignmentNode -> makeAssignment(node.target, t(node.expression), node)
      is BinaryOperationNode -> {
        val left = t(node.leftOperand)
        val right = t(node.rightOperand)
        val operator = when (node) {
          is BitwiseAndNode -> BinaryOP.BitwiseAnd
          is BitwiseOrNode -> BinaryOP.BitwiseOr
          is BitwiseXorNode -> BinaryOP.BitwiseXor
          is ConditionalAndNode -> BinaryOP.And
          is ConditionalOrNode -> BinaryOP.Or
          is EqualToNode -> BinaryOP.Equal
          is FloatingDivisionNode -> BinaryOP.FloatDivision
          is FloatingRemainderNode -> BinaryOP.FloatRemainder
          is GreaterThanNode -> BinaryOP.GreaterThan
          is GreaterThanOrEqualNode -> BinaryOP.GreaterThanOrEqual
          is IntegerDivisionNode -> BinaryOP.IntDivision
          is IntegerRemainderNode -> BinaryOP.IntRemainder
          is LeftShiftNode -> BinaryOP.LeftShift
          is LessThanNode -> BinaryOP.LessThan
          is LessThanOrEqualNode -> BinaryOP.LessThanOrEqual
          is NotEqualNode -> BinaryOP.NotEqual
          is NumericalAdditionNode -> BinaryOP.Add
          is NumericalMultiplicationNode -> BinaryOP.Mult
          is NumericalSubtractionNode -> BinaryOP.Sub
          is SignedRightShiftNode -> BinaryOP.SignedRightShift
          is StringConcatenateNode -> BinaryOP.StringConcat
          is UnsignedRightShiftNode -> BinaryOP.UnsignedRightShift
          else -> error("Unexpected node ${node.javaClass}")
        }
        SingleAdaptResult(BinaryExpr(left, right, operator).set(node))
      }
      is CaseNode -> SingleAdaptResult(CaseExpr(t(node.caseOperand), t(node.switchOperand)).set(node))
      is ClassDeclarationNode -> SingleAdaptResult(transformClass(node.tree as JCTree.JCClassDecl))
      is ClassNameNode -> SingleAdaptResult(makeTypeRef(node.type).set(node))
      is FieldAccessNode -> SingleAdaptResult(when (node.fieldName) {
        // Handle "className.this"
        "this" -> renamer.transformThis(node.receiver.type).set(node).set(node.receiver.type)
        // Handle "className.class"
        "class" -> Select(makeTypeRef(node.receiver.type).set(node), "class", 0).set(node)
        else -> if (node.isStatic) {
          Select(makeTypeRef(node.receiver.type).set(node), node.fieldName, 0).set(node)
        } else {
          // Make sure the corresponding tree of the receiver is not null
          // This can occur if the receiver is ClassNameNode or ImplicitThisNode
          val adaptedReceiver = t(node.receiver)
          if (adaptedReceiver.cfTree == null) {
            adaptedReceiver.set(node.tree)
          }
          renamer.transformSelect(adaptedReceiver, node.element).set(node)
        }
      })
      is FunctionalInterfaceNode -> when (val tree = node.tree) {
        is MemberReferenceTree -> {
          // TODO Cannot create reference for non-anytime method
          TODO("method references are not supported yet")
        }
        is JCTree.JCLambda -> MultipleAdaptResult(listOf(
          FuncDeclaration(null, getParamTypes(tree), processCFG(tree), getReturnType(tree).first, isPublic = false, isAnytime = true, isPure = false, isAbstract = false).set(node),
          NewObj(typeIntroducer.getInitialType(node.type), hierarchy.get(node.type)).set(node)
        ))
        else -> error("Unexpected tree ${node.javaClass} in FunctionalInterfaceNode")
      }
      is InstanceOfNode -> SingleAdaptResult(BinaryExpr(t(node.operand), makeTypeRef(node.refType), BinaryOP.Is).set(node))
      is LambdaResultExpressionNode -> SingleAdaptResult(makeReturn(node, node.result))
      is LocalVariableNode -> SingleAdaptResult(renamer.transformLocal(node).set(node))
      is MarkerNode -> SingleAdaptResult(NoOPExpr(node.message).set(node))
      /*
      How method calls are interpreted. Take for example
      setC(a.b, a.b)

      1. Check that the receiver object is not null (if the call is non-static)
      2. Access method
      3. Evaluate parameters expressions in order
      4. Call method

      For our purposes, the method call setC(a.b, a.b) would be interpreted like:

      #param1 = a.b
      #param2 = a.b
      call setC
      */
      is MethodAccessNode -> {
        val method = transformMethod(node.method as Symbol.MethodSymbol).set(node)
        val receiver = node.receiver
        if (receiver is ClassNameNode || receiver is ThisNode || receiver is SuperNode) {
          // Make sure the corresponding tree of the receiver is not null
          // This can occur if the receiver is ClassNameNode or ImplicitThisNode
          val adaptedReceiver = t(receiver)
          if (adaptedReceiver.cfTree == null) {
            adaptedReceiver.set(node.tree)
          }
          // No NullPointerException can be thrown
          SingleAdaptResult(method)
        } else {
          // When calling a method on an object,
          // the receiver object is checked to see if it is not null first,
          // before the parameters are evaluated
          MultipleAdaptResult(listOf(
            NullCheck(t(node.receiver), "Cannot call ${method.name} on null").set(node).set(node.tree
              ?: node.receiver.tree),
            method
          ))
        }
      }
      is MethodInvocationNode -> {
        val method = node.target.method as Symbol.MethodSymbol
        val includeThis = !method.isStatic
        makeCall(
          t(node.target) as FuncInterface,
          if (includeThis)
            listOf(node.target.receiver).plus(node.arguments)
          else
            node.arguments,
          node
        )
      }
      is NarrowingConversionNode -> SingleAdaptResult(UnaryExpr(t(node.operand), UnaryOP.Narrowing).set(node))
      is NullChkNode -> SingleAdaptResult(NullCheck(t(node.operand), "Potential null pointer exception").set(node).set(node.operand.tree))
      is ObjectCreationNode -> {
        val methodSym = TreeUtils.elementFromUse(node.tree!!) as Symbol.MethodSymbol
        val method = transformMethod(methodSym).set(node)
        // Transform object creation node "new Object()" into
        // o = new Object; Object.<init>(o); o
        val newObj = NewObj(getInitialType(methodSym), hierarchy.get(methodSym.getCorrectReceiverType())).set(node)
        MultipleAdaptResult(
          (node.classBody?.let { listOf(t(it), newObj) } ?: listOf(newObj)).plus(
            makeCall2(
              method,
              listOf(newObj).plus(node.arguments.map(t)),
              node
            ).toList()
          ).plus(newObj)
        )
      }
      is PackageNameNode -> SingleAdaptResult(makeTypeRef(node.element.asType()).set(node))
      is ParameterizedTypeNode -> SingleAdaptResult(makeTypeRef(node.type).set(node))
      is PrimitiveTypeNode -> error("Unexpected node ${node.javaClass}")
      is ReturnNode -> SingleAdaptResult(makeReturn(node, node.result))
      is StringConcatenateAssignmentNode -> {
        val left = node.leftOperand
        val concatExpr = BinaryExpr(t(left), t(node.rightOperand), BinaryOP.StringConcat).set(node)
        makeAssignment(if (left is StringConversionNode) left.operand else left, concatExpr, node)
      }
      is StringConversionNode -> SingleAdaptResult(UnaryExpr(t(node.operand), UnaryOP.ToString)).set(node)
      is SuperNode -> SingleAdaptResult(renamer.transformThis(classesStack.peek().type).set(node))
      is SynchronizedNode -> SingleAdaptResult((if (node.isStartOfBlock) SynchronizedExprStart(t(node.expression)) else SynchronizedExprEnd(t(node.expression))).set(node))
      is TernaryExpressionNode -> SingleAdaptResult(TernaryExpr(t(node.conditionOperand), t(node.thenOperand), t(node.elseOperand)).set(node))
      is ThisNode -> SingleAdaptResult(when (node) {
        is ExplicitThisNode,
        is ImplicitThisNode -> renamer.transformThis(classesStack.peek().type).set(node)
        else -> error("Unexpected node ${node.javaClass}")
      })
      is ThrowNode -> SingleAdaptResult(ThrowExpr(t(node.expression)).set(node))
      is TypeCastNode -> SingleAdaptResult(makeCast(t(node.operand), node.type).set(node))
      is UnaryOperationNode -> {
        val expr = t(node.operand)
        val operator = when (node) {
          is BitwiseComplementNode -> UnaryOP.BitwiseComplement
          is ConditionalNotNode -> UnaryOP.Not
          is NumericalMinusNode -> UnaryOP.Minus
          is NumericalPlusNode -> UnaryOP.Plus
          else -> error("Unexpected node ${node.javaClass}")
        }
        SingleAdaptResult(UnaryExpr(expr, operator).set(node))
      }
      is ValueLiteralNode -> SingleAdaptResult(when (node) {
        is BooleanLiteralNode -> BooleanLiteral(node.value!!).set(node)
        is CharacterLiteralNode -> CharLiteral(node.value!!).set(node)
        is DoubleLiteralNode -> DoubleLiteral(node.value!!).set(node)
        is FloatLiteralNode -> FloatLiteral(node.value!!).set(node)
        is IntegerLiteralNode -> IntegerLiteral(node.value!!).set(node)
        is LongLiteralNode -> LongLiteral(node.value!!).set(node)
        is NullLiteralNode -> NullLiteral().set(node)
        is ShortLiteralNode -> ShortLiteral(node.value!!).set(node)
        is StringLiteralNode -> StringLiteral(node.value!!).set(node)
        else -> error("Unexpected node ${node.javaClass}")
      })
      is VariableDeclarationNode -> SingleAdaptResult(VarDeclaration(renamer.transformDecl(node), JTCUnknownType.SINGLETON).set(node))
      is WideningConversionNode -> SingleAdaptResult(UnaryExpr(t(node.operand), UnaryOP.Widening).set(node))
      else -> error("Unexpected node ${node.javaClass}")
    }
  }
}
