package jatyc.core.linearmode

import jatyc.core.*
import jatyc.core.cfg.*
import jatyc.core.typesystem.TypeInfo
import jatyc.typestate.graph.State
import jatyc.utils.JTCUtils
import java.util.*

class LinearModeInference(
  utils: JTCUtils,
  classAnalysis: LinearModeClassAnalysis
) : CfgVisitor<Store>() {
  val inference = Inference(utils, this, classAnalysis)
  private val warnings = mutableMapOf<Pair<State, FuncDeclaration>?, IdentityHashMap<CodeExpr, MutableSet<String>>>()
  private val errors = mutableMapOf<Pair<State, FuncDeclaration>?, IdentityHashMap<CodeExpr, MutableSet<String>>>()
  private var errorContext: Stack<Pair<State, FuncDeclaration>?> = Stack()

  init {
    // Error context stack is never empty to prevent exception when calling "peek"
    errorContext.push(null)
  }

  fun <T> withErrorContext(state: State, func: FuncDeclaration, run: () -> T): T {
    val pair = Pair(state, func)
    errorContext.push(pair)
    errors[pair] = IdentityHashMap() // reset
    val result = run()
    errorContext.pop()
    return result
  }

  // We might analyze a code expression more than once because of loops
  fun resetErrorsAndWarnings(code: CodeExpr) {
    errors.computeIfAbsent(errorContext.peek()) { IdentityHashMap() }.remove(code)
    warnings.computeIfAbsent(errorContext.peek()) { IdentityHashMap() }.remove(code)
  }

  fun addWarning(code: CodeExpr, warning: String) {
    warnings.computeIfAbsent(errorContext.peek()) { IdentityHashMap() }.computeIfAbsent(code) { mutableSetOf() }.add(warning)
  }

  fun addError(code: CodeExpr, error: String) {
    errors.computeIfAbsent(errorContext.peek()) { IdentityHashMap() }.computeIfAbsent(code) { mutableSetOf() }.add(error)
  }

  fun warnings(): Iterator<Map.Entry<CodeExpr, Set<String>>> {
    val all = IdentityHashMap<CodeExpr, MutableSet<String>>()
    for ((_, map) in warnings) {
      for ((codeExpr, set) in map) {
        all.computeIfAbsent(codeExpr) { mutableSetOf() }.addAll(set)
      }
    }
    return all.iterator()
  }

  fun errors(): Iterator<Map.Entry<CodeExpr, Set<String>>> {
    val all = IdentityHashMap<CodeExpr, MutableSet<String>>()
    for ((_, map) in errors) {
      for ((codeExpr, set) in map) {
        all.computeIfAbsent(codeExpr) { mutableSetOf() }.addAll(set)
      }
    }
    return all.iterator()
  }

  fun clearErrorsAndWarnings() {
    warnings.clear()
    errors.clear()
  }

  override fun defaultAssertion(node: SimpleNode): Store {
    return Store()
  }

  override fun makeInitialAssertion(func: FuncDeclaration, cfg: SimpleCFG, initialAssertion: Store): Store {
    val store = initialAssertion.toRegular()
    for (param in func.parameters) {
      store[Reference.make(param.id)] = TypeInfo.make(param.id.javaType, param.requires)
    }
    return store
  }

  override fun analyzeEnd(func: FuncDeclaration, exitAssertion: Store) {
    inference.analyzeEnd(func, exitAssertion)
  }

  override fun propagate(from: SimpleNode, rule: SimpleFlowRule, a: Store, b: Store): Boolean {
    when (from) {
      is SimpleMarkerEntry -> return a.propagateTo(b)
      is SimpleMarkerExit -> return a.propagateTo(b)
      is SimpleCodeNode -> {
      }
    }

    val ref = Reference.make(from.code)
    return when (rule) {
      SimpleFlowRule.ALL -> a.propagateTo(b)
      SimpleFlowRule.THEN -> a.withLabel(ref, "true").addFact(CasePattern(ref, "true", true)).propagateTo(b)
      SimpleFlowRule.ELSE -> a.withLabel(ref, "false").addFact(CasePattern(ref, "true", false)).propagateTo(b)
    }
  }

  override fun analyzeNode(func: FuncDeclaration, pre: Store, node: SimpleNode, post: Store) {
    when (node) {
      is SimpleCodeNode -> analyzeCodeNode(func, pre, node, post)
      is SimpleMarker -> analyzeMarker(pre, node, post)
    }
  }

  private fun analyzeCodeNode(func: FuncDeclaration, pre: Store, node: SimpleCodeNode, post: Store) {
    val code = node.code
    inference.analyzeCode(func, pre, code, post)

    if (node.isCondition) {
      val codeRef = Reference.make(code)
      val bool = inference.getBooleanValue(code)
      if (bool == true) {
        for ((ref, info) in post) {
          post[ref] = StoreInfo.conditional(codeRef, info.type, info.type.toBottom())
        }
      } else if (bool == false) {
        for ((ref, info) in post) {
          post[ref] = StoreInfo.conditional(codeRef, info.type.toBottom(), info.type)
        }
      }
    }
  }

  private fun analyzeMarker(pre: Store, node: SimpleMarker, post: Store) {
    for ((ref, info) in pre) {
      post[ref] = info.toRegular()
    }
  }
}
