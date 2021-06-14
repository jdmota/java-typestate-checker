package jatyc.core.linearmode

import jatyc.JavaTypestateChecker
import jatyc.core.*
import jatyc.core.cfg.*
import java.util.*

class LinearModeInference(
  private val cfChecker: JavaTypestateChecker,
  private val hierarchy: JavaTypesHierarchy,
  private val typeIntroducer: TypeIntroducer,
  private val typecheckUtils: TypecheckUtils,
  private val classAnalysis: LinearModeClassAnalysis
) : CfgVisitor<Store>() {

  val inference = Inference(cfChecker, hierarchy, typeIntroducer, typecheckUtils, this, classAnalysis)
  val warnings = IdentityHashMap<CodeExpr, List<String>>()
  val errors = IdentityHashMap<CodeExpr, String>()
  val completionErrors = IdentityHashMap<CodeExpr, List<String>>()
  val validationErrors = IdentityHashMap<CodeExpr, List<String>>()

  override fun defaultAssertion(node: SimpleNode): Store {
    return Store()
  }

  override fun makeInitialAssertion(func: FuncDeclaration, cfg: SimpleCFG, initialAssertion: Store): Store {
    val store = initialAssertion.toRegular()
    for (param in func.parameters) {
      store[Reference.make(param.id)] = param.requires
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
    var changed = false

    // TODO improve this to support short-circuit of && and ||

    when (rule) {
      SimpleFlowRule.EACH_TO_EACH -> {
        changed = a.propagateTo(b) || changed
      }
      SimpleFlowRule.THEN_TO_BOTH -> {
        changed = a.withLabel(ref, "true").propagateTo(b) || changed
      }
      SimpleFlowRule.ELSE_TO_BOTH -> {
        changed = a.withLabel(ref, "false").propagateTo(b) || changed
      }
      SimpleFlowRule.THEN_TO_THEN -> {
        changed = a.withLabel(ref, "true").propagateTo(b) || changed
      }
      SimpleFlowRule.ELSE_TO_ELSE -> {
        changed = a.withLabel(ref, "false").propagateTo(b) || changed
      }
      SimpleFlowRule.BOTH_TO_THEN -> {
        changed = a.propagateTo(b) || changed
      }
      SimpleFlowRule.BOTH_TO_ELSE -> {
        changed = a.propagateTo(b) || changed
      }
      SimpleFlowRule.BOTH_TO_BOTH -> {
        changed = a.propagateTo(b) || changed // a.withLabel(ref, null).propagateTo(b) || changed
      }
    }

    return changed
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
          post[ref] = ConditionalStoreInfo(codeRef, info.type, JTCBottomType.SINGLETON)
        }
      } else if (bool == false) {
        for ((ref, info) in post) {
          post[ref] = ConditionalStoreInfo(codeRef, JTCBottomType.SINGLETON, info.type)
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
