package jatyc.core

import com.sun.tools.javac.code.Symbol
import com.sun.tools.javac.comp.AttrContext
import com.sun.tools.javac.comp.Env
import jatyc.JavaTypestateChecker
import jatyc.core.cfg.FuncInterface
import jatyc.core.cfg.MethodCall
import jatyc.typestate.graph.DecisionState
import jatyc.typestate.graph.MethodTransition
import jatyc.typestate.graph.State

class TypecheckUtils(private val cfChecker: JavaTypestateChecker, private val typeIntroducer: TypeIntroducer) {
  private val utils get() = cfChecker.utils

  private fun resolveType(env: Env<AttrContext>, type: String): JavaType? {
    return utils.resolver.resolve(env, type)?.let { typeIntroducer.getJavaType(it) }
  }

  private fun isSubtype(a: JavaType?, b: JavaType?): Boolean {
    if (a == null || b == null) return false
    return a.isSubtype(b)
  }

  private fun paramsSubtype(env: Env<AttrContext>, funcInterface: FuncInterface, node: MethodTransition): Boolean {
    val params1 = funcInterface.parameters.dropWhile { it.isThis }
    if (params1.size != node.args.size) {
      return false
    }
    val params2 = node.args.map { resolveType(env, it.getName()) }
    val it2 = params2.iterator()
    for (param1 in params1) {
      // Input contravariance
      if (!isSubtype(it2.next(), param1.javaType)) {
        return false
      }
    }
    return true
  }

  fun methodSubtype(env: Env<AttrContext>, funcInterface: FuncInterface, node: MethodTransition): Boolean {
    // TODO deal with thrownTypes and typeArguments in the future
    return funcInterface.name == node.name &&
      isSubtype(funcInterface.returnJavaType, resolveType(env, node.returnType.getName())) &&
      paramsSubtype(env, funcInterface, node)
  }

  private fun paramsSubtype(env: Env<AttrContext>, params1: List<JavaType>, node: MethodTransition): Boolean {
    val params2 = node.args.map { resolveType(env, it.getName()) }
    if (params1.size != params2.size) {
      return false
    }
    val it2 = params2.iterator()
    for (param1 in params1) {
      // Input contravariance
      if (!isSubtype(it2.next(), param1)) {
        return false
      }
    }
    return true
  }

  fun methodSubtype(env: Env<AttrContext>, sym: Symbol.MethodSymbol, node: MethodTransition): Boolean {
    // TODO deal with thrownTypes and typeArguments in the future
    return sym.name.toString() == node.name &&
      isSubtype(typeIntroducer.getJavaType(sym.type.returnType), resolveType(env, node.returnType.getName())) &&
      paramsSubtype(env, sym.type.parameterTypes.map { typeIntroducer.getJavaType(it) }, node)
  }

  fun check(type: JTCType, call: MethodCall): Boolean {
    val method = call.methodExpr
    return when (type) {
      is JTCUnknownType,
      is JTCPrimitiveType,
      is JTCNullType -> false
      is JTCSharedType,
      is JTCLinearType -> call.methodExpr.isAnytime
      is JTCStateType -> {
        val env = type.graph.getEnv()
        call.methodExpr.isAnytime || type.state.normalizedTransitions.entries.any { methodSubtype(env, method, it.key) }
      }
      is JTCBottomType -> true
      is JTCUnionType -> type.types.all { check(it, call) }
      is JTCIntersectionType -> type.types.any { check(it, call) }
    }
  }

  fun refine(type: JTCType, call: MethodCall, predicate: (String) -> Boolean): JTCType {
    return when (type) {
      is JTCUnknownType -> type
      is JTCPrimitiveType,
      is JTCNullType -> JTCBottomType.SINGLETON
      is JTCSharedType -> if (call.methodExpr.isAnytime) type else JTCBottomType.SINGLETON // TODO in the worst case, we are in a droppable state
      is JTCLinearType -> type
      is JTCStateType -> if (call.methodExpr.isAnytime) type else refineState(type, call, predicate)
      is JTCBottomType -> type
      is JTCUnionType -> JTCType.createUnion(type.types.map { refine(it, call, predicate) })
      is JTCIntersectionType -> JTCType.createIntersection(type.types.map { refine(it, call, predicate) })
    }
  }

  private fun refineState(type: JTCStateType, call: MethodCall, predicate: (String) -> Boolean): JTCType {
    val method = call.methodExpr
    val env = type.graph.getEnv()
    // Given a current state, produce a set of possible destination states
    return when (val dest = type.state.normalizedTransitions.entries.find { methodSubtype(env, method, it.key) }?.value) {
      is State -> JTCStateType(type.javaType, type.graph, dest)
      is DecisionState -> JTCType.createUnion(dest.normalizedTransitions.entries.filter { predicate(it.key.label) }.map { JTCStateType(type.javaType, type.graph, it.value) })
      else -> if (type.javaType.isFinal()) {
        // If the Java class is final, then there is no substate which would allow for this call
        // So return an empty list (representing the bottom type)
        JTCBottomType.SINGLETON
      } else {
        // If the Java class is not final, then there might be a substate which would allow for this call
        // So return an approximation
        JTCLinearType(type.javaType, type.graph)
      }
    }
  }

  fun refineToNonNull(type: JTCType): JTCType {
    return when (type) {
      is JTCNullType -> JTCBottomType.SINGLETON
      is JTCUnionType -> JTCType.createUnion(type.types.map { refineToNonNull(it) })
      else -> type
    }
  }

  fun refineToNull(type: JTCType): JTCType {
    return if (JTCNullType.SINGLETON.isSubtype(type)) JTCNullType.SINGLETON else JTCBottomType.SINGLETON
  }

  fun isInDroppableStateNotEnd(type: JTCType): Boolean {
    return when (type) {
      is JTCUnknownType -> false
      is JTCPrimitiveType -> false
      is JTCNullType -> false
      is JTCSharedType -> false
      // is JTCNoProtocolType -> false
      is JTCLinearType -> false
      is JTCStateType -> type.state.canDropHere() && !type.state.isEnd()
      is JTCBottomType -> false
      is JTCUnionType -> type.types.any { isInDroppableStateNotEnd(it) }
      is JTCIntersectionType -> type.types.any { isInDroppableStateNotEnd(it) }
    }
  }

  fun canDrop(type: JTCType): Boolean {
    return when (type) {
      is JTCUnknownType -> false
      is JTCPrimitiveType -> true
      is JTCNullType -> true
      is JTCSharedType -> true
      // is JTCNoProtocolType -> type.exact
      is JTCLinearType -> false
      is JTCStateType -> type.state.canDropHere()
      is JTCBottomType -> true
      is JTCUnionType -> type.types.all { canDrop(it) }
      is JTCIntersectionType -> type.types.any { canDrop(it) }
    }
  }

  // This returns the least upper bound type possible for a value with a given type
  // This method should not be used to compute the upper bound of a variable/field, only of a specific object!
  fun invariant(type: JTCType): JTCType {
    return when (type) {
      is JTCUnknownType -> type
      is JTCPrimitiveType -> type
      is JTCNullType -> type
      is JTCSharedType -> {
        val javaType = type.javaType
        val graph = javaType.getGraph()
        if (graph == null) {
          JTCSharedType(javaType)//.union(JTCNoProtocolType(javaType, false))
        } else {
          JTCSharedType(javaType).union(JTCLinearType(javaType, graph))
        }
      }
      // is JTCNoProtocolType -> JTCSharedType(type.javaType).union(type)
      is JTCLinearType -> JTCSharedType(type.javaType).union(type)
      is JTCStateType -> JTCSharedType(type.javaType).union(JTCLinearType(type.javaType, type.graph))
      is JTCBottomType -> JTCBottomType.SINGLETON
      is JTCUnionType -> JTCType.createUnion(type.types.map { invariant(it) })
      is JTCIntersectionType -> JTCType.createIntersection(type.types.map { invariant(it) })
    }
  }

  companion object {
    // This method is only used for checking if parameters may require linear types in any way
    fun requiresLinear(ref: Reference, type: JTCType): Boolean {
      return when (type) {
        is JTCUnknownType,
        is JTCSharedType,
        is JTCPrimitiveType,
        is JTCNullType -> false
        is JTCLinearType,
        is JTCStateType,
        is JTCBottomType -> true
        is JTCUnionType -> type.types.any { requiresLinear(ref, it) }
        is JTCIntersectionType -> type.types.any { requiresLinear(ref, it) }
      }
    }
  }
}
