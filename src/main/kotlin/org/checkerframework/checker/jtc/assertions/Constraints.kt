package org.checkerframework.checker.jtc.assertions

import com.microsoft.z3.BoolExpr
import com.sun.tools.javac.code.Symbol
import org.checkerframework.checker.jtc.analysis.*
import org.checkerframework.checker.jtc.typecheck.*
import org.checkerframework.checker.jtc.utils.JTCUtils
import org.checkerframework.dataflow.cfg.node.ObjectCreationNode

private var constraintsUUID = 1L

class ConstraintsSet(val constraint: Constraint) : Iterable<TinyBoolExpr> {

  private val phase1 = mutableListOf<TinyBoolExpr>()
  private val phase1Enforce = mutableListOf<TinyBoolExpr>()
  private val phase2 = mutableListOf<TinyBoolExpr>()
  private val all = mutableListOf<TinyBoolExpr>()

  fun addIn1(expr: TinyBoolExpr): ConstraintsSet {
    phase1.add(expr)
    all.add(expr)
    expr.mainOrigin = constraint
    expr.phase = 1
    return this
  }

  fun addIn1Enforce(expr: TinyBoolExpr): ConstraintsSet {
    phase1Enforce.add(expr)
    all.add(expr)
    expr.mainOrigin = constraint
    expr.phase = 2
    return this
  }

  fun addIn2(expr: TinyBoolExpr): ConstraintsSet {
    phase2.add(expr)
    all.add(expr)
    expr.mainOrigin = constraint
    expr.phase = 3
    return this
  }

  fun phase1It() = phase1.iterator()

  fun phase1EnforceIt() = phase1Enforce.iterator()

  fun phase2It() = phase2.iterator()

  override fun iterator(): Iterator<TinyBoolExpr> {
    return all.iterator()
  }

}

sealed class Constraint {
  val id = constraintsUUID++
  abstract fun build(): ConstraintsSet
}

fun reduce(
  result: ConstraintsSet,
  assertions: NodeAssertions,
  fn: (result: ConstraintsSet, tail: SymbolicAssertion, heads: Set<SymbolicAssertion>) -> Unit
): ConstraintsSet {
  if (assertions.postThen === assertions.postElse) {
    fn(result, assertions.postThen, setOf(assertions.preThen, assertions.preElse))
  } else {
    fn(result, assertions.postThen, setOf(assertions.preThen))
    fn(result, assertions.postElse, setOf(assertions.preElse))
  }
  return result
}

private fun equals(heads: Collection<SymbolicAssertion>, first: Reference, second: Reference): TinyBoolExpr {
  val list = mutableListOf<TinyBoolExpr>()
  var a: Reference? = first
  var b: Reference? = second
  while (a != null && b != null) {
    list.add(Make.S.and(heads.map { Make.S.equals(it, a!!, b!!) }))
    if (false && a is FieldAccess && b is FieldAccess && a.fieldName == b.fieldName) {
      a = a.parent
      b = b.parent
    } else break
  }
  return Make.S.or(list)
}

fun fractionsAccumulation(ref: Reference, heads: Collection<SymbolicAssertion>, tail: SymbolicAssertion, result: ConstraintsSet) {
  val parent = ref.parent
  if (parent == null) {
    result.addIn1(Make.S.eq(
      tail[ref].fraction.expr,
      Make.S.min(heads.map { it[ref].fraction.expr })
    ))
    return
  }

  // "otherParents" includes "parent"
  val otherParents = tail.skeleton.getPossibleEq(parent)
  val addition = Make.S.add(
    otherParents.map { otherParent ->
      val otherRef = ref.replace(parent, otherParent)
      val sub = Make.S.sub(
        Make.S.min(heads.map { it[otherRef].fraction.expr }),
        if (ref == otherRef) Make.ZERO else tail[otherRef].fraction.expr
      )
      Make.S.ite(
        equals(heads, parent, otherParent),
        sub,
        Make.ZERO
      )
    }
  )

  result.addIn1(Make.S.eq(
    tail[ref].fraction.expr,
    addition
  ))

  result.addIn1Enforce(Make.S.implies(
    Make.S.eq(tail[parent].fraction.expr, Make.ZERO),
    Make.S.eq(tail[ref].fraction.expr, Make.ZERO)
  ))
}

// Example:
// x y z
// f1 + f2 + f3 = f4 + f5 + f6
// (f1 - f4) + (f2 - f5) + (f3 - f6) = 0
fun packFractionsAccumulation(ref: Reference, heads: Collection<SymbolicAssertion>, tail: SymbolicAssertion, result: ConstraintsSet) {
  // "others" includes "ref"
  val others = tail.skeleton.getPossibleEq(ref)
  val addition = Make.S.add(
    others.map { other ->
      val sub = Make.S.sub(
        Make.S.min(heads.map { it[other].packFraction.expr }),
        if (ref == other) Make.ZERO else tail[other].packFraction.expr
      )
      Make.S.ite(
        equals(heads, ref, other),
        sub,
        Make.ZERO
      )
    }
  )

  result.addIn1(Make.S.eq(
    tail[ref].packFraction.expr,
    addition
  ))

  result.addIn1Enforce(Make.S.implies(
    Make.S.eq(tail[ref].fraction.expr, Make.ZERO),
    Make.S.eq(tail[ref].packFraction.expr, Make.ZERO)
  ))
}

fun typesAccumulation(ref: Reference, heads: Collection<SymbolicAssertion>, tail: SymbolicAssertion, result: ConstraintsSet) {
  // "others" includes "ref"
  val others = tail.skeleton.getPossibleEq(ref)
  val typeExpr = Make.S.intersection(others.map { other ->
    Make.S.ite(
      equals(heads, ref, other),
      Make.S.union(heads.map { it[other].type.expr }),
      Make.S.type(JTCUnknownType.SINGLETON)
    )
  })

  result.addIn2(Make.S.eq(
    tail[ref].type.expr,
    typeOrUnknown(
      ref,
      tail[ref].fraction.expr,
      tail[ref].packFraction.expr,
      Make.S.union(heads.map { it[ref].type.expr }),
      typeExpr
    )
  ))
}

fun typeOrUnknown(
  ref: Reference,
  fraction: TinyArithExpr,
  packFraction: TinyArithExpr,
  typeBefore: TinyJTCTypeExpr,
  typeAfter: TinyJTCTypeExpr
): TinyJTCTypeExpr {
  return Make.S.ite(
    Make.S.eq(fraction, Make.ZERO),
    // Without permission to the variable/field, nothing can be said
    Make.S.type(JTCUnknownType.SINGLETON),
    if (ref.isPrimitive()) {
      Make.S.type(JTCPrimitiveType.SINGLETON)
    } else {
      Make.S.ite(
        Make.S.eq(packFraction, Make.ZERO),
        // Without permission to the object itself, we can only assert it is an object or null
        Make.S.ite(
          Make.S.subtype(
            Make.S.type(JTCNullType.SINGLETON),
            typeBefore
          ),
          Make.S.type(JTCUnionType.create(listOf(JTCObjectType.SINGLETON, JTCNullType.SINGLETON))),
          Make.S.type(JTCObjectType.SINGLETON)
        ),
        typeAfter
      )
    }
  )
}

fun handleImplies(
  tail: SymbolicAssertion,
  heads: Set<SymbolicAssertion>,
  result: ConstraintsSet
) {
  tail.forEach { ref, _ ->
    fractionsAccumulation(ref, heads, tail, result)
    packFractionsAccumulation(ref, heads, tail, result)
    typesAccumulation(ref, heads, tail, result)
  }

  for ((a, b) in tail.skeleton.allEqualities) {
    // Equality is true in assertion "tail" if present in the other assertions
    // and if there is enough permissions
    result.addIn1(
      Make.S.eq(
        Make.S.equals(tail, a, b),
        Make.S.ite(
          Make.S.or(listOf(
            Make.S.eq(tail[a].fraction.expr, Make.ZERO),
            Make.S.eq(tail[b].fraction.expr, Make.ZERO)
          )),
          Make.FALSE,
          Make.S.and(heads.map { Make.S.equals(it, a, b) })
        )
      )
    )
  }
}

fun handleEquality(
  old: Reference?,
  target: Reference,
  expr: Reference,
  tail: SymbolicAssertion,
  heads: Set<SymbolicAssertion>,
  result: ConstraintsSet
) {
  val unknown = UnknownRef(expr.type)

  val accessReplacements = mutableListOf<Pair<Reference, Reference>>()
  val equalsReplacements = mutableListOf<Pair<Reference, Reference>>()

  if (old != null) {
    accessReplacements.add(Pair(old, target))
  }
  accessReplacements.add(Pair(target, expr))
  accessReplacements.add(Pair(expr, unknown)) // Force permission to go to the target

  if (old != null) {
    equalsReplacements.add(Pair(old, target))
  }
  equalsReplacements.add(Pair(target, expr))
  if (expr is NodeRef) {
    equalsReplacements.add(Pair(expr, unknown)) // Invalidate equalities with nodes
  }

  val changedRefs = setOf(old, target, expr)

  // old = target;
  // target = expr;
  // expr = unknown;

  // (P[E/x] <=> replace x with E)
  // {P[E/x]} x := E {P}

  // {P[unknown/expr][expr/target][target/old]}
  // old := target
  // {P[unknown/expr][expr/target]}
  // target := expr
  // {P[unknown/expr]}
  // expr := unknown;
  // {P}

  fun accessReplace(p: Reference) = accessReplacements.foldRight(p) { (a, b), p -> p.replace(a, b) }
  fun equalsReplace(p: Reference) = equalsReplacements.foldRight(p) { (a, b), p -> p.replace(a, b) }

  tail.forEach { ref, info ->
    val otherRef = accessReplace(ref)

    if (changedRefs.contains(ref)) {
      // The access permission to access the variables/fields that hold the relevant values
      // Remains the same
      result.addIn1(Make.S.eq(
        info.fraction.expr,
        Make.S.min(heads.map { it[ref].fraction.expr })
      ))
    } else {
      result.addIn1(Make.S.eq(
        info.fraction.expr,
        Make.S.min(heads.map { it[otherRef].fraction.expr })
      ))
    }

    result.addIn1(Make.S.eq(
      info.packFraction.expr,
      Make.S.min(heads.map { it[otherRef].packFraction.expr })
    ))

    result.addIn2(Make.S.eq(
      info.type.expr,
      Make.S.union(heads.map { it[otherRef].type.expr })
    ))
  }

  val equalities = tail.skeleton.allEqualities

  for ((a, b) in equalities) {
    val c = equalsReplace(a)
    val d = equalsReplace(b)
    result.addIn1(Make.S.eq(
      Make.S.equals(tail, a, b),
      Make.S.and(heads.map {
        Make.S.equals(it, c, d)
      })
    ))
  }
}

private class ForSureMap<K, V>(private val default: (K) -> V) {
  private val map = mutableMapOf<K, V>()
  operator fun get(key: K) = map.computeIfAbsent(key, default)
  operator fun set(key: K, value: V) {
    map[key] = value
  }

  fun debug() {
    for ((key, value) in map) {
      println("$key = $value")
    }
  }
}

sealed class TypeAfterCall {
  abstract fun toExpr(initial: TinyJTCTypeExpr): TinyJTCTypeExpr
}

class TypeAfterCallSpecific(val type: JTCType) : TypeAfterCall() {
  override fun toExpr(initial: TinyJTCTypeExpr): TinyJTCTypeExpr {
    return Make.S.type(type)
  }
}

class TypeAfterCallTransition(val method: Symbol.MethodSymbol, val map: Map<JTCType, JTCType>) : TypeAfterCall() {
  override fun toExpr(initial: TinyJTCTypeExpr): TinyJTCTypeExpr {
    return Make.S.transition(initial, method, map)
  }
}

fun handleCall(
  callRef: Reference,
  receiverRef: Reference?,
  typeAfterCall: TypeAfterCall?,
  arguments: List<List<Reference>>,
  parameters: List<List<Reference>>,
  methodPre: SymbolicAssertion,
  methodPost: Set<SymbolicAssertion>,
  tail: SymbolicAssertion,
  heads: Set<SymbolicAssertion>,
  result: ConstraintsSet
) {
  val isConstructor = callRef is NodeRef && callRef.node is ObjectCreationNode
  val returnRef = ReturnSpecialVar(callRef.type)
  val thisRef = ThisReference(callRef.type)

  /*println("----")
  println(callRef)
  println(arguments)
  println(parameters)*/

  val requiredFractions = ForSureMap<Reference, TinyArithExpr> { Make.ZERO }
  val requiredPackFractions = ForSureMap<Reference, TinyArithExpr> { Make.ZERO }
  val requiredTypes = ForSureMap<Reference, TinyJTCTypeExpr> { Make.UNKNOWN }

  // Build requirements
  for ((idx, argAndFields) in arguments.withIndex()) {
    for (arg in argAndFields) {
      val argRoot = arguments[idx].first()
      val paramRoot = parameters[idx].first()
      val param = arg.replace(argRoot, paramRoot)
      val requiredInfo = methodPre[param]
      // println("argRoot: $argRoot; paramRoot: $paramRoot; arg: $arg; param: $param")

      requiredFractions[arg] = Make.S.add(requiredFractions[arg], if (arg == argRoot) Make.ZERO else requiredInfo.fraction.expr)
      requiredPackFractions[arg] = Make.S.add(requiredPackFractions[arg], requiredInfo.packFraction.expr)
      requiredTypes[arg] = Make.S.intersection(requiredTypes[arg], requiredInfo.type.expr)
    }
  }

  /*println("Requires")
  requiredFractions.debug()
  requiredPackFractions.debug()
  requiredTypes.debug()*/

  val ensuredFractions = ForSureMap<Reference, TinyArithExpr> { Make.ZERO }
  val ensuredPackFractions = ForSureMap<Reference, TinyArithExpr> { Make.ZERO }
  val ensuredTypes = ForSureMap<Reference, TinyJTCTypeExpr> { Make.UNKNOWN }

  // Build ensures
  for ((idx, argAndFields) in arguments.withIndex()) {
    for (arg in argAndFields) {
      val argRoot = arguments[idx].first()
      val paramRoot = parameters[idx].first()
      val param = arg.replace(argRoot, paramRoot)

      ensuredFractions[arg] = Make.S.add(
        ensuredFractions[arg],
        if (arg == argRoot) Make.ZERO else Make.S.min(methodPost.map { it[param].fraction.expr })
      )
      ensuredPackFractions[arg] = Make.S.add(
        ensuredPackFractions[arg],
        Make.S.min(methodPost.map { it[param].packFraction.expr })
      )
      ensuredTypes[arg] = Make.S.intersection(
        ensuredTypes[arg],
        Make.S.union(methodPost.map { it[param].type.expr })
      )
    }
  }

  /*println("Ensures")
  ensuredFractions.debug()
  ensuredPackFractions.debug()
  ensuredTypes.debug()*/

  /*println("Pre")
  println(methodPre)

  println("Post")
  println(methodPost)*/

  val fractions = ForSureMap<Reference, TinyArithExpr> { arg -> Make.S.min(heads.map { it[arg].fraction.expr }) }
  val packFractions = ForSureMap<Reference, TinyArithExpr> { arg -> Make.S.min(heads.map { it[arg].packFraction.expr }) }
  val types = ForSureMap<Reference, TinyJTCTypeExpr> { arg -> Make.S.union(heads.map { it[arg].type.expr }) }

  // Add constraints
  for (argAndFields in arguments) {
    for (arg in argAndFields) {
      result.addIn1(Make.S.ge(fractions[arg], requiredFractions[arg]))
      result.addIn1(Make.S.ge(packFractions[arg], requiredPackFractions[arg]))
      result.addIn2(Make.S.subtype(types[arg], requiredTypes[arg]))
    }
  }

  tail.forEach { ref, info ->
    if (ref.hasPrefix(callRef)) {
      val otherRef = if (isConstructor) ref.replace(callRef, thisRef) else ref.replace(callRef, returnRef)

      result.addIn1(Make.S.eq(
        info.fraction.expr,
        Make.S.min(methodPost.map { it[otherRef].fraction.expr })
      ))

      result.addIn1(Make.S.eq(
        info.packFraction.expr,
        Make.S.min(methodPost.map { it[otherRef].packFraction.expr })
      ))

      if (isConstructor && ref == callRef && typeAfterCall != null) {
        result.addIn2(Make.S.eq(
          info.type.expr,
          typeAfterCall.toExpr(types[ref])
        ))
      } else {
        result.addIn2(Make.S.eq(
          info.type.expr,
          Make.S.union(methodPost.map { it[otherRef].type.expr })
        ))
      }
    } else {
      fun fractionModified(ref: Reference, list: MutableList<TinyBoolExpr> = mutableListOf()): List<TinyBoolExpr> {
        var parent = ref.parent
        while (parent != null) {
          list.add(Make.S.eq(requiredFractions[parent], Make.ONE))
          parent = parent.parent
        }
        return list
      }

      fun packFractionModified(ref: Reference, list: MutableList<TinyBoolExpr> = mutableListOf()): List<TinyBoolExpr> {
        list.add(Make.S.eq(requiredFractions[ref], Make.ONE))
        return fractionModified(ref, list)
      }

      fun typeModified(ref: Reference, list: MutableList<TinyBoolExpr> = mutableListOf()): List<TinyBoolExpr> {
        list.add(Make.S.eq(requiredPackFractions[ref], Make.ONE))
        return packFractionModified(ref, list)
      }

      result.addIn1(Make.S.eq(
        info.fraction.expr,
        Make.S.ite(
          Make.S.or(fractionModified(ref)),
          ensuredFractions[ref],
          Make.S.add(Make.S.sub(fractions[ref], requiredFractions[ref]), ensuredFractions[ref])
        )
      ))
      result.addIn1(Make.S.eq(
        info.packFraction.expr,
        Make.S.ite(
          Make.S.or(packFractionModified(ref)),
          ensuredPackFractions[ref],
          Make.S.add(Make.S.sub(packFractions[ref], requiredPackFractions[ref]), ensuredPackFractions[ref])
        )
      ))
      if (ref == receiverRef && typeAfterCall != null) {
        result.addIn2(Make.S.eq(
          info.type.expr,
          typeAfterCall.toExpr(types[ref])
        ))
      } else {
        result.addIn2(Make.S.eq(
          info.type.expr,
          Make.S.ite(
            Make.S.or(typeModified(ref)),
            ensuredTypes[ref],
            types[ref]
          )
        ))
      }
    }
  }

  // TODO am I able to track equalities of old values? like after this.item = newItem ??

  fun replace(p: Reference): Reference {
    return if (p.hasPrefix(callRef)) {
      when {
        isConstructor -> p.replace(callRef, thisRef)
        else -> p.replace(callRef, returnRef)
      }
    } else {
      val idx = arguments.indexOfFirst { p.hasPrefix(it.first()) }
      if (idx < 0) {
        p
      } else {
        p.replace(arguments[idx].first(), parameters[idx].first())
      }
    }
  }

  for ((a, b) in tail.skeleton.allEqualities) {
    val c = replace(a)
    val d = replace(b)

    val aNotModified = if (a.hasPrefix(callRef)) Make.FALSE else Make.S.lt(requiredFractions[a], Make.ONE)
    val bNotModified = if (b.hasPrefix(callRef)) Make.FALSE else Make.S.lt(requiredFractions[b], Make.ONE)

    result.addIn1(Make.S.eq(
      Make.S.equals(tail, a, b),
      Make.S.ite(
        Make.S.and(listOf(aNotModified, bNotModified)),
        // Nothing was modified, equality holds if it holds before
        Make.S.and(heads.map {
          Make.S.equals(it, a, b)
        }),
        Make.S.ite(
          aNotModified,
          // B was modified
          Make.S.or(listOf(
            Make.S.equalsTransitive(tail, a, b),
            Make.S.and(methodPost.map {
              Make.S.equals(it, c, d)
            })
          )),
          Make.S.ite(
            bNotModified,
            // A was modified
            Make.S.or(listOf(
              Make.S.equalsTransitive(tail, a, b),
              Make.S.and(methodPost.map {
                Make.S.equals(it, c, d)
              })
            )),
            Make.S.and(methodPost.map {
              Make.S.equals(it, c, d)
            })
          )
        )
      )
    ))
  }
}

fun handleNewVariable(
  tail: SymbolicAssertion,
  heads: Set<SymbolicAssertion>,
  variable: Reference?,
  type: JTCType?,
  result: ConstraintsSet
) {
  tail.forEach { ref, info ->
    if (variable != null && type != null && ref.hasPrefix(variable)) {
      if (ref == variable) {
        result.addIn1(Make.S.eq(
          info.fraction.expr,
          Make.S.real(1)
        ))
        result.addIn1(Make.S.eq(
          info.packFraction.expr,
          Make.S.real(1)
        ))
        result.addIn2(Make.S.eq(
          info.type.expr,
          Make.S.type(type)
        ))
      } else {
        result.addIn1(Make.S.eq(
          info.fraction.expr,
          Make.S.real(0)
        ))
        result.addIn1(Make.S.eq(
          info.packFraction.expr,
          Make.S.real(0)
        ))
        result.addIn2(Make.S.eq(
          info.type.expr,
          Make.S.type(JTCUnknownType.SINGLETON)
        ))
      }
    } else {
      result.addIn1(Make.S.eq(
        info.fraction.expr,
        Make.S.min(heads.map { it[ref].fraction.expr })
      ))
      result.addIn1(Make.S.eq(
        info.packFraction.expr,
        Make.S.min(heads.map { it[ref].packFraction.expr })
      ))
      result.addIn2(Make.S.eq(
        info.type.expr,
        Make.S.union(heads.map { it[ref].type.expr })
      ))
    }
  }

  for ((a, b) in tail.skeleton.allEqualities) {
    if (variable != null && (a.hasPrefix(variable) || b.hasPrefix(variable))) {
      // Although we believe a previous equality would never be true
      // (even if the declaration was in a loop)
      // We invalidate it anyway to be sure
      result.addIn1(
        Make.S.not(Make.S.equals(tail, a, b))
      )
    } else {
      // Equality is true in assertion "tail" if present in the other assertions
      result.addIn1(
        Make.S.eq(
          Make.S.equals(tail, a, b),
          Make.S.and(heads.map {
            Make.S.equals(it, a, b)
          })
        )
      )
    }
  }
}

private class ImpliedAssertion(val tail: SymbolicAssertion) : Constraint() {

  override fun toString(): String {
    return "($id) (${tail.impliedBy().joinToString(" && ")}}) ==> $tail"
  }

  override fun build(): ConstraintsSet {
    val result = ConstraintsSet(this)
    handleImplies(tail, tail.impliedBy(), result)
    return result
  }
}

private class NoSideEffects(val assertions: NodeAssertions) : Constraint() {

  override fun toString(): String {
    return "($id) NoSideEffects"
  }

  override fun build(): ConstraintsSet {
    return reduce(ConstraintsSet(this), assertions) { result, tail, heads ->
      handleNewVariable(tail, heads, null, null, result)
    }
  }
}

private class NewVariable(val assertions: NodeAssertions, val variable: Reference, val type: JTCType) : Constraint() {

  override fun toString(): String {
    return "($id) $variable: $type"
  }

  override fun build(): ConstraintsSet {
    return reduce(ConstraintsSet(this), assertions) { result, tail, heads ->
      handleNewVariable(tail, heads, variable, type, result)
    }
  }
}

private class CallConstraints(
  val assertions: NodeAssertions,
  val callRef: Reference,
  val receiverRef: Reference?,
  val typeAfterCall: TypeAfterCall?,
  val arguments: List<List<Reference>>,
  val parameters: List<List<Reference>>,
  val methodPre: SymbolicAssertion,
  val methodPost: Set<SymbolicAssertion>
) : Constraint() {

  override fun toString(): String {
    return "($id) Call $callRef"
  }

  override fun build(): ConstraintsSet {
    return reduce(ConstraintsSet(this), assertions) { result, tail, heads ->
      handleCall(
        callRef,
        receiverRef,
        typeAfterCall,
        arguments,
        parameters,
        methodPre,
        methodPost,
        tail,
        heads,
        result
      )
    }
  }
}

// Make the reference representing the parameter
// and the corresponding local variable equal
// But start with all the permission on the side of the parameter
private class ParameterAndLocalVariable(
  val assertion: SymbolicAssertion,
  val parameter: ParameterVariable,
  val local: LocalVariable
) : Constraint() {
  override fun toString(): String {
    return "($id) param+local: $parameter $local"
  }

  override fun build(): ConstraintsSet {
    val result = ConstraintsSet(this)

    fun helper(parameter: Reference, local: Reference) {
      val paramInfo = assertion[parameter]
      val localInfo = assertion[local]
      if (local !== this.local) {
        result.addIn1(Make.S.eq(
          localInfo.fraction.expr,
          Make.ZERO
        ))
      }
      result.addIn1(Make.S.eq(
        localInfo.packFraction.expr,
        Make.ZERO
      ))
      result.addIn2(Make.S.eq(
        localInfo.type.expr,
        Make.S.type(JTCUnknownType.SINGLETON)
      ))
      paramInfo.children.forEach { (ref, _) ->
        helper(ref, ref.replace(parameter, local))
      }
    }

    result.addIn1(Make.S.equals(assertion, parameter, local))

    helper(parameter, local)
    return result
  }
}

private class NotEqualityInAssertion(
  val assertion: SymbolicAssertion,
  val a: Reference,
  val b: Reference
) : Constraint() {
  override fun toString(): String {
    return "($id) !eq($a,$b)"
  }

  override fun build(): ConstraintsSet {
    return ConstraintsSet(this).addIn1(Make.S.not(
      Make.S.equals(assertion, a, b)
    ))
  }
}

private class EqualityInAssertion(
  val assertions: NodeAssertions,
  val old: Reference?,
  val target: Reference,
  val expr: Reference
) : Constraint() {

  override fun toString(): String {
    return "($id) $target = $expr;"
  }

  override fun build(): ConstraintsSet {
    return reduce(ConstraintsSet(this), assertions) { result, tail, heads ->
      handleEquality(old, target, expr, tail, heads, result)
    }
  }
}

// access(x, a) ==> access(x, b)
// a >= b
private class SymFractionImpliesSymFraction(val a: SymbolicFraction, val b: SymbolicFraction) : Constraint() {
  override fun toString(): String {
    return "($id) $a ==> $b"
  }

  override fun build(): ConstraintsSet {
    return ConstraintsSet(this).addIn1(Make.S.ge(a.expr, b.expr))
  }
}

private class SymFractionEqSymFraction(val a: SymbolicFraction, val b: Collection<SymbolicFraction>) : Constraint() {
  constructor(a: SymbolicFraction, b: SymbolicFraction) : this(a, listOf(b))

  override fun toString(): String {
    return "($id) $a = $b"
  }

  override fun build(): ConstraintsSet {
    return ConstraintsSet(this).addIn1(Make.S.eq(a.expr, Make.S.min(b.map { it.expr })))
  }
}

// typeof(x, a) ==> typeof(x, b)
// a <: b
// t1 <: t2
private class SymTypeImpliesSymType(val a: SymbolicType, val b: SymbolicType) : Constraint() {
  override fun toString(): String {
    return "($id) $a ==> $b"
  }

  override fun build(): ConstraintsSet {
    return ConstraintsSet(this).addIn2(Make.S.subtype(a.expr, b.expr))
  }
}

private class SymTypeEqSymType(val a: SymbolicType, val b: SymbolicType) : Constraint() {
  override fun toString(): String {
    return "($id) $a = $b"
  }

  override fun build(): ConstraintsSet {
    return ConstraintsSet(this).addIn2(Make.S.eq(a.expr, b.expr))
  }
}

private class SymTypeEqType(val a: SymbolicType, val b: JTCType) : Constraint() {
  override fun toString(): String {
    return "($id) $a = $b"
  }

  override fun build(): ConstraintsSet {
    return ConstraintsSet(this).addIn2(Make.S.eq(a.expr, Make.S.type(b)))
  }
}

private class TypeImpliesSymType(val a: JTCType, val b: SymbolicType) : Constraint() {
  override fun toString(): String {
    return "($id) $a ==> $b"
  }

  override fun build(): ConstraintsSet {
    return ConstraintsSet(this).addIn2(Make.S.subtype(Make.S.type(a), b.expr))
  }
}

private class SymTypeImpliesType(val a: SymbolicType, val b: JTCType) : Constraint() {

  override fun toString(): String {
    return "($id) $a ==> $b"
  }

  override fun build(): ConstraintsSet {
    return ConstraintsSet(this).addIn2(Make.S.subtype(a.expr, Make.S.type(b)))
  }
}

private class SymFractionGt(val a: SymbolicFraction, val b: Int) : Constraint() {
  override fun toString(): String {
    return "($id) $a > $b"
  }

  override fun build(): ConstraintsSet {
    return ConstraintsSet(this).addIn1(Make.S.gt(a.expr, Make.S.real(b)))
  }
}

private class SymFractionLt(val a: SymbolicFraction, val b: Int) : Constraint() {
  override fun toString(): String {
    return "($id) $a < $b"
  }

  override fun build(): ConstraintsSet {
    return ConstraintsSet(this).addIn1(Make.S.lt(a.expr, Make.S.real(b)))
  }
}

private class SymFractionEq(val a: SymbolicFraction, val b: Int) : Constraint() {
  override fun toString(): String {
    return "($id) $a = $b"
  }

  override fun build(): ConstraintsSet {
    return ConstraintsSet(this).addIn1(Make.S.eq(a.expr, Make.S.real(b)))
  }
}

private class OtherConstraint(val fn: (Constraint) -> ConstraintsSet) : Constraint() {
  override fun toString(): String {
    return "($id) other"
  }

  override fun build(): ConstraintsSet {
    return fn(this)
  }
}

class Constraints {

  private var started = false

  private val types = mutableSetOf(
    JTCUnknownType.SINGLETON,
    JTCObjectType.SINGLETON,
    JTCNoProtocolType.SINGLETON,
    JTCEndedType.SINGLETON,
    JTCNullType.SINGLETON,
    JTCPrimitiveType.SINGLETON,
    JTCMovedType.SINGLETON,
    JTCBottomType.SINGLETON,
    JTCUnionType.create(listOf(JTCObjectType.SINGLETON, JTCNullType.SINGLETON))
  )

  fun addType(type: JTCType) {
    if (started) {
      JTCUtils.printStack()
      error("Already started adding constraints to Z3")
    }
    types.add(type)
  }

  private val labelToOrigin = mutableMapOf<String, Pair<TinyBoolExpr, BoolExpr>>()

  fun getConstraintByLabel(label: String): Pair<TinyBoolExpr, BoolExpr> {
    return labelToOrigin[label.subSequence(1, label.lastIndex)]!!
  }

  private lateinit var setup: ConstraintsSetup

  /*
  Goal g4 = ctx.mkGoal(true, false, false);
  g4.add(ctx.mkGt(xr, ctx.mkReal(10, 1)));
  g4.add(ctx.mkEq(yr, ctx.mkAdd(xr, ctx.mkReal(1, 1))));
  g4.add(ctx.mkGt(yr, ctx.mkReal(1, 1)));

  ApplyResult ar = applyTactic(ctx, ctx.mkTactic("simplify"), g4);
  if (ar.getNumSubgoals() == 1
          && (ar.getSubgoals()[0].isDecidedSat() || ar.getSubgoals()[0]
                  .isDecidedUnsat()))
      throw new TestFailedException();

  ar = applyTactic(ctx, ctx.andThen(ctx.mkTactic("simplify"),
          ctx.mkTactic("solve-eqs")), g4);
  if (ar.getNumSubgoals() == 1
          && (ar.getSubgoals()[0].isDecidedSat() || ar.getSubgoals()[0]
                  .isDecidedUnsat()))
      throw new TestFailedException();

  Solver s = ctx.mkSolver();
  for (BoolExpr e : ar.getSubgoals()[0].getFormulas())
      s.add(e);
  Status q = s.check();
  System.out.println("Solver says: " + q);
  System.out.println("Model: \n" + s.getModel());
  if (q != Status.SATISFIABLE)
      throw new TestFailedException();
  */

  private fun buildAllExprs(): Collection<TinyBoolExpr> {
    val constraintsSets = constraints.map { it.build() }
    val allExprs = mutableListOf<TinyBoolExpr>()
    for (set in constraintsSets) {
      for (expr in set) {
        allExprs.add(expr)
      }
    }
    return Simplifier(experimental = true, setEqualsToFalse = false).simplifyAll(allExprs)
  }

  private fun solveIn1Phase(): InferenceResult {
    setup = ConstraintsSetup(types).start()
    val exprs = buildAllExprs()

    for ((idx, expr) in exprs.withIndex()) {
      val label = "$idx"
      val z3expr = expr.toZ3(setup)
      println(expr)
      labelToOrigin[label] = Pair(expr, z3expr)
      setup.addAssert(z3expr, label)
    }

    println("Solving...")
    val result = setup.solve()
    println("Done")

    return when (result) {
      is MiniNoSolution -> NoSolution(result.unsatCore)
      is MiniUnknownSolution -> UnknownSolution(result.reason)
      is MiniSolution -> Solution(setup, result.model, result.model)
    }
  }

  private fun solveIn2Phases(): InferenceResult {
    setup = ConstraintsSetup(types).start()
    val exprs = buildAllExprs()

    // Phase 1...

    for ((idx, expr) in exprs.withIndex()) {
      if (expr.phase == null) throw AssertionError("Bool expr without phase?")
      if (expr.phase == 1) {
        val label = "$idx"
        val z3expr = expr.toZ3(setup)
        println(expr)
        labelToOrigin[label] = Pair(expr, z3expr)
        setup.addAssert(z3expr, label)
      }
    }

    println("Solving (phase 1)...")
    val result1 = setup.solve()
    println("Phase 1 done")

    when (result1) {
      is MiniNoSolution -> return NoSolution(result1.unsatCore)
      is MiniUnknownSolution -> return UnknownSolution(result1.reason)
      is MiniSolution -> {
      }
    }

    // Phase 1 enforcements...

    // setup.push()

    for ((idx, expr) in exprs.withIndex()) {
      if (expr.phase == 2) {
        // val label = "$idx"
        val z3expr = expr.toZ3(setup)
        val simplified = result1.model.eval(z3expr, false).simplify() as BoolExpr
        if (simplified.toString() != "true") {
          println("---")
          println(expr)
          println(simplified)
          println("---")
        }
        // idToConstraint[label] = Triple(constraint, expr, z3expr)
        // setup.addAssert(z3expr, label)
      }
    }

    /*println("Solving (phase 1 enforcements)...")
    result1 = setup.solve()
    println("Phase 1 enforcements done")

    when (result1) {
      is MiniNoSolution -> return NoSolution(result1.unsatCore)
      is MiniUnknownSolution -> return UnknownSolution(result1.reason)
      is MiniSolution -> {
      }
    }*/

    // Phase 2...

    setup.push()

    for ((idx, expr) in exprs.withIndex()) {
      if (expr.phase == 3) {
        val label = "$idx"
        val z3expr = expr.toZ3(setup)
        val simplified = result1.model.eval(z3expr, false).simplify() as BoolExpr
        labelToOrigin[label] = Pair(expr, z3expr)
        setup.addAssert(simplified, label)
      }
    }

    println("Solving (phase 2)...")
    val result2 = setup.solve()
    println("Phase 2 done")

    return when (result2) {
      is MiniNoSolution -> IncompleteSolution(setup, result1.model, result2.unsatCore)
      is MiniUnknownSolution -> IncompleteSolution(setup, result1.model, null)
      is MiniSolution -> Solution(setup, result1.model, result2.model)
    }
  }

  fun solve(): InferenceResult {
    started = true
    // return solveIn1Phase()
    return solveIn2Phases()
  }

  // Inferred constraints
  private val constraints = mutableListOf<Constraint>()

  // Track assertions that are implied by others
  private val impliedAssertions = mutableSetOf<SymbolicAssertion>()

  fun implies(a: SymbolicAssertion, b: SymbolicAssertion) {
    // a ==> b
    a.implies(b)
    if (impliedAssertions.add(b)) {
      constraints.add(ImpliedAssertion(b))
    }
  }

  fun noSideEffects(assertions: NodeAssertions) {
    constraints.add(NoSideEffects(assertions))
  }

  fun newVariable(assertions: NodeAssertions, variable: Reference, type: JTCType) {
    constraints.add(NewVariable(assertions, variable, type))
  }

  fun one(a: SymbolicFraction) {
    // a == 1
    constraints.add(SymFractionEq(a, 1))
  }

  fun notOne(a: SymbolicFraction) {
    // a < 1
    constraints.add(SymFractionLt(a, 1))
  }

  fun notZero(a: SymbolicFraction) {
    // a > 0
    constraints.add(SymFractionGt(a, 0))
  }

  fun same(a: SymbolicFraction, b: SymbolicFraction) {
    // a == b
    constraints.add(SymFractionEqSymFraction(a, b))
  }

  fun same(a: SymbolicFraction, b: Collection<SymbolicFraction>) {
    // a == b
    constraints.add(SymFractionEqSymFraction(a, b))
  }

  fun same(a: SymbolicFraction, value: Int) {
    // a == value
    constraints.add(SymFractionEq(a, value))
  }

  fun same(a: SymbolicType, b: SymbolicType) {
    // a == b
    constraints.add(SymTypeEqSymType(a, b))
  }

  fun same(a: SymbolicType, b: JTCType) {
    // a == b
    addType(b)
    constraints.add(SymTypeEqType(a, b))
  }

  fun subtype(t1: SymbolicType, t2: JTCType) {
    // t1 <: t2
    addType(t2)
    constraints.add(SymTypeImpliesType(t1, t2))
  }

  fun subtype(t1: JTCType, t2: SymbolicType) {
    // t1 <: t2
    addType(t1)
    constraints.add(TypeImpliesSymType(t1, t2))
  }

  fun equality(assertions: NodeAssertions, old: Reference?, target: Reference, expr: Reference) {
    // eq(a, b)
    constraints.add(EqualityInAssertion(assertions, old, target, expr))
  }

  fun notEquality(assertion: SymbolicAssertion, a: Reference, b: Reference) {
    // !eq(a, b)
    constraints.add(NotEqualityInAssertion(assertion, a, b))
  }

  fun paramAndLocalVars(assertion: SymbolicAssertion, parameter: ParameterVariable, local: LocalVariable) {
    constraints.add(ParameterAndLocalVariable(assertion, parameter, local))
  }

  fun call(
    assertions: NodeAssertions,
    callRef: Reference,
    receiverRef: Reference?,
    typeAfterCall: TypeAfterCall?,
    arguments: List<List<Reference>>,
    parameters: List<List<Reference>>,
    methodPre: SymbolicAssertion,
    methodPost: Set<SymbolicAssertion>
  ) {
    when (typeAfterCall) {
      is TypeAfterCallSpecific -> {
        addType(typeAfterCall.type)
      }
      is TypeAfterCallTransition -> {
        for ((a, b) in typeAfterCall.map) {
          addType(a)
          addType(b)
        }
      }
      null -> {
      }
    }
    constraints.add(CallConstraints(
      assertions,
      callRef,
      receiverRef,
      typeAfterCall,
      arguments,
      parameters,
      methodPre,
      methodPost
    ))
  }

  fun other(fn: (Constraint) -> ConstraintsSet) {
    constraints.add(OtherConstraint(fn))
  }

}
