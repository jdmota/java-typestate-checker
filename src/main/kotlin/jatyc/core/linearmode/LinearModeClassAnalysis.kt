package jatyc.core.linearmode

import jatyc.JavaTypestateChecker
import jatyc.core.*
import jatyc.core.cfg.*
import jatyc.typestate.graph.AbstractState
import jatyc.typestate.graph.DecisionState
import jatyc.typestate.graph.Graph
import jatyc.typestate.graph.State
import java.util.LinkedHashSet

class LinearModeClassAnalysis(
  cfChecker: JavaTypestateChecker,
  hierarchy: JavaTypesHierarchy,
  typeIntroducer: TypeIntroducer,
  private val typecheckUtils: TypecheckUtils,
  val classes: Map<String, ClassDeclAndCompanion>
) {
  val inference = LinearModeInference(cfChecker, hierarchy, typeIntroducer, typecheckUtils, this)

  fun analyze(clazz: ClassDecl) {
    if (clazz.graph == null) {
      analyzeClassWithoutProtocol(clazz)
    } else {
      analyzeClassWithProtocol(clazz, clazz.graph, clazz.thisRef!!)
    }

    // Analyze inner classes
    for (inner in clazz.classes) {
      analyze(inner.nonStatic)
      analyze(inner.static)
    }
  }

  private fun toBottom(store: Store): Store {
    val newStore = store.clone()
    newStore.toBottom()
    return newStore
  }

  private fun nullFields(clazz: ClassDecl): Store {
    val thisRef = clazz.thisRef
    val store = Store()
    if (thisRef != null) {
      for (field in clazz.allFields(classes)) {
        store[Reference.make(thisRef, field)] = JTCNullType.SINGLETON
      }
    }
    return store
  }

  private fun analyzeConstructors(clazz: ClassDecl): Store {
    val nullFields = nullFields(clazz)
    val initialStore = Store()
    for (method in clazz.constructors()) {
      val classThisRef = clazz.thisRef
      val result = analyzeMethod(classThisRef, method, nullFields)
      if (classThisRef != null) {
        for ((ref, info) in result) {
          if (ref.isFieldOf(classThisRef)) {
            initialStore.merge(ref, info.toRegular())
          }
        }
      }
    }
    return initialStore
  }

  private fun getUpperBoundStore(constructorsStore: Store, clazz: ClassDecl): Store {
    val thisRef = clazz.thisRef
    val store = Store()
    if (thisRef != null) {
      for (field in clazz.allFields(classes)) {
        store[Reference.make(thisRef, field)] = field.type
      }
    }
    // Making sure that non-initialized fields have the null type, even if they are not declared with @Nullable
    constructorsStore.propagateTo(store)
    return store
  }

  private fun analyzeClassWithoutProtocol(clazz: ClassDecl) {
    val constructorsStore = analyzeConstructors(clazz)
    val upperBoundStore = getUpperBoundStore(constructorsStore, clazz)
    val upperBoundSharedStore = upperBoundStore.toShared()

    // Since this class has no protocol, all methods are available
    // Since they can be called anytime, assume nothing
    for (method in clazz.nonConstructors()) {
      analyzeMethod(clazz.thisRef, method, upperBoundSharedStore)
    }

    // Ensure completion of objects in fields
    ensureFieldsCompleteness(clazz, upperBoundStore)
  }

  private fun analyzeClassWithProtocol(clazz: ClassDecl, graph: Graph, classThisRef: Reference) {
    val constructorsStore = analyzeConstructors(clazz)
    val methodToStatesCache = mutableMapOf<State, Map<FuncDeclaration, AbstractState<*>>>()
    val env = graph.getEnv()

    fun getMethodToState(state: State): Map<FuncDeclaration, AbstractState<*>> {
      val map = mutableMapOf<FuncDeclaration, AbstractState<*>>()
      for ((methodNode, dest) in state.normalizedTransitions) {
        val func = clazz.protocolMethods(classes).find { typecheckUtils.methodSubtype(env, it, methodNode) }
        if (func != null) {
          map[func] = dest
        }
        // If the declaration of a method is not available, that is fine
        // It means the method comes from a class without protocol (because its source is not available in the project)
        // And thus, it is a method that can always be called
        // Even if it is not pure, it will not modify fields of subclasses since it has no access to them
      }
      return map
    }

    // States lead us to methods that may be called. So we need information about each state.
    val stateToStore = mutableMapOf<State, Store>()
    // States that need recomputing. Use a LinkedHashSet to keep some order and avoid duplicates.
    val stateQueue = LinkedHashSet<State>()

    val emptyStore = toBottom(constructorsStore)

    // Update the state's store. Queue the state again if it changed.
    fun mergeStateStore(state: State, store: Store) {
      val currStore = stateToStore.computeIfAbsent(state) { emptyStore }
      val newStore = Store.mergeFieldsToNew(currStore, store, classThisRef)
      if (currStore != newStore) {
        stateToStore[state] = newStore
        stateQueue.add(state)
      }
    }

    stateToStore[graph.getInitialState()] = constructorsStore
    stateQueue.add(graph.getInitialState())

    while (stateQueue.isNotEmpty()) {
      val state = stateQueue.first()
      stateQueue.remove(state)

      val store = stateToStore[state]!!
      val methodToStates = methodToStatesCache.computeIfAbsent(state, ::getMethodToState)

      for ((method, destState) in methodToStates) {
        // To analyze each method, we use the store of the state we are analyzing.
        // Previous versions of the class analysis would merge the stores of states that lead to a given method
        // and use that as the pre-store to analyze the method. But this resulted in many issues:
        // 1. a method available in more than one state but with different destination states had a chance
        // that its post-store would not be propagated to all the destination states
        // because it would be analyzed once, and then the analysis would hit the cache and not propagate the post-store;
        // 2. even after fixing (1), because the analysis of each method would mix information from different states,
        // that information would be propagated to different destinations states, resulting in some over-approximation.
        // We now do not check if a method was already analyzed, we only look to states that were not analyzed.
        // This allows us to be more precise by separating the analysis of a method from
        // a given state from the analysis of the same method but from a different state.
        val generalResult = inference.withErrorContext(state, method) { analyzeMethod(classThisRef, method, store) }
        val returnExprs = method.body.allNodes.mapNotNull {
          if (it is SimpleCodeNode && it.code is Return && it.code.expr != null) Pair(it, it.code.expr) else null
        }

        // Merge new exit store with the stores of each destination state
        // Taking into account the possible return values
        if (returnExprs.isEmpty()) {
          when (destState) {
            is State -> mergeStateStore(destState, generalResult.toRegular())
            is DecisionState -> {
              for ((_, dest) in destState.transitions) {
                mergeStateStore(dest, generalResult.toRegular())
              }
            }
          }
        } else {
          for ((cfgNode, returnExpr) in returnExprs) {
            val result = inference.getAssertions(cfgNode).second.fixThis(Reference.makeThis(method)!!, classThisRef)
            when (destState) {
              is State -> mergeStateStore(destState, result.toRegular())
              is DecisionState -> {
                for ((label, dest) in destState.transitions) {
                  if (mayGoToLabel(returnExpr, label.label)) {
                    when (label.label) {
                      "true" -> mergeStateStore(dest, result.withLabel(Reference.returnRef, "true"))
                      "false" -> mergeStateStore(dest, result.withLabel(Reference.returnRef, "false"))
                      else -> mergeStateStore(dest, result.toRegular())
                    }
                  } else {
                    mergeStateStore(dest, emptyStore)
                  }
                }
              }
            }
          }
        }
      }
    }

    // Analyze anytime methods
    val upperBoundSharedStore = getUpperBoundStore(constructorsStore, clazz).toShared()
    for (method in clazz.methods) {
      if (!method.isConstructor && method.isAnytime) {
        analyzeMethod(classThisRef, method, upperBoundSharedStore)
      }
    }

    // Ensure completion of objects in fields
    for ((state, store) in stateToStore) {
      if (state.canDropHere()) {
        ensureFieldsCompleteness(clazz, store)
      }
    }
  }

  private fun ensureFieldsCompleteness(clazz: ClassDecl, store: Store) {
    for ((ref, info) in store) {
      if (!typecheckUtils.canDrop(info.type)) {
        inference.addError(clazz, "[${ref.format()}] did not complete its protocol (found: ${info.type.format()})")
      }
    }
  }

  private fun isConstantBoolean(n: CodeExpr, value: Boolean): Boolean {
    return when (n) {
      is BooleanLiteral -> n.value == value
      is UnaryExpr -> n.operator == UnaryOP.Not && isConstantBoolean(n.expr, !value)
      else -> false
    }
  }

  private fun mayGoToLabel(result: CodeExpr, label: String): Boolean {
    if (isConstantBoolean(result, true)) {
      return label == "true"
    }
    if (isConstantBoolean(result, false)) {
      return label == "false"
    }
    // Handle enumeration values
    if (result is Select) {
      if (result.expr is SymbolResolveExpr) {
        return label == result.id
      }
    }
    return true
  }

  fun analyzeMethod(classThisRef: Reference?, method: FuncDeclaration, initialStore: Store): Store {
    if (classThisRef == null) {
      // Analyze static method
      return inference.analyze(method, initialStore)
    }
    val methodThisRef = Reference.makeThis(method)!!
    // Analyze non-static method
    // Adapt initial store so that the field references have the "this" the method expects
    // Analyze and adapt result so that all references have the same "this"
    return inference.analyze(method, initialStore.fixThis(classThisRef, methodThisRef)).fixThis(methodThisRef, classThisRef)
  }

  fun checkMethods(clazz: ClassDecl) {
    val graph = clazz.graph

    for ((method, overrides) in clazz.overrides) {
      for (override in overrides) {
        checkMethodSubtyping(method, override)
      }
    }

    if (graph != null) {
      val env = graph.getEnv()

      for (t in graph.getAllTransitions()) {
        val method = clazz.allPublicMethods(classes).find { typecheckUtils.methodSubtype(env, it, t) }
        if (method == null) {
          inference.addError(clazz, "Method [${t.name}] is required by the typestate but not implemented")
        } else {
          if (method.isAnytime) {
            inference.addError(clazz, "Method [${t.name}] that is always available should not appear in the protocol")
          }
        }
      }
    }

  }

  private fun checkMethodSubtyping(a: FuncDeclaration, b: FuncInterface) {
    val aParams = a.parameters.iterator()
    val bParams = b.parameters.iterator()

    val aThisParam = aParams.next()
    val bThisParam = bParams.next()

    check(aThisParam.isThis)
    check(bThisParam.isThis)
    check(a.parameters.size == b.parameters.size)
    check(!a.isConstructor)
    check(!b.isConstructor)

    if (b.isAnytime && !a.isAnytime) {
      inference.addError(a, "Method should be available anytime since the overridden method is available anytime")
    }

    if (b.isPure && !a.isPure) {
      inference.addError(a, "Method should be pure since the overridden method is pure")
    }

    if (b.isPublic && !a.isPublic) {
      inference.addError(a, "Method should be public since the overridden method is public")
    }

    while (aParams.hasNext()) {
      val aParam = aParams.next()
      val bParam = bParams.next()
      if (!bParam.requires.isSubtype(aParam.requires)) {
        inference.addError(a, "Parameter [${aParam.id.name}] should require a supertype of ${bParam.requires.format()} (found: ${aParam.requires.format()})")
      }
      if (!aParam.ensures.isSubtype(bParam.ensures)) {
        inference.addError(a, "Parameter [${aParam.id.name}] should ensure a subtype of ${bParam.ensures.format()} (found: ${aParam.ensures.format()})")
      }
    }

    if (!a.returnType.isSubtype(b.returnType)) {
      inference.addError(a, "Return value should be a subtype of ${b.returnType.format()} (found: ${a.returnType.format()})")
    }
  }

}
