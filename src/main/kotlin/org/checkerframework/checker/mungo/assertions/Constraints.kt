package org.checkerframework.checker.mungo.assertions

import com.microsoft.z3.BoolExpr
import org.checkerframework.checker.mungo.analysis.*
import org.checkerframework.checker.mungo.typecheck.*
import javax.lang.model.type.TypeKind

private var constraintsUUID = 1L

sealed class Constraint {
  val id = constraintsUUID++
  abstract fun toZ3(setup: ConstraintsSetup): BoolExpr
}

fun handle(result: NodeAssertions, fn: (tail: SymbolicAssertion, heads: Set<SymbolicAssertion>) -> Unit) {
  if (result.postThen === result.postElse) {
    fn(result.postThen, setOf(result.preThen, result.preElse))
  } else {
    fn(result.postThen, setOf(result.preThen))
    fn(result.postElse, setOf(result.preElse))
  }
}

fun reduce(setup: ConstraintsSetup, result: NodeAssertions, fn: (tail: SymbolicAssertion, heads: Set<SymbolicAssertion>) -> BoolExpr): BoolExpr {
  return if (result.postThen === result.postElse) {
    fn(result.postThen, setOf(result.preThen, result.preElse))
  } else {
    setup.ctx.mkAnd(
      fn(result.postThen, setOf(result.preThen)),
      fn(result.postElse, setOf(result.preElse))
    )
  }
}

// TODO ensure that certain facts are only asserted with enough permission (i.e. isValid)
// TODO if the fraction is zero, the type should be Unknown instead
// TODO handle primitives, since they can be copied many times

fun handleImplies(tail: SymbolicAssertion, heads: Set<SymbolicAssertion>, setup: ConstraintsSetup, except: Set<Reference>): BoolExpr {
  val exprs = mutableListOf<BoolExpr>()

  tail.forEach { ref, info ->
    if (except.contains(ref)) return@forEach

    exprs.add(setup.ctx.mkEq(
      setup.fractionToExpr(info.fraction),
      setup.min(heads.map { it.getAccess(ref) })
    ))

    // TODO what about the transferring of the type?
    exprs.add(setup.fractionsAccumulation(ref, heads, tail))

    handleTypeImplication(exprs, heads, ref, info.type, setup)
  }

  // TODO equalities only hold if enough permission!
  // TODO equality of fields!
  for ((a, b) in tail.skeleton.equalities) {
    if (except.contains(a) || except.contains(b)) continue
    // Equality is true in assertion "tail" if present in the other assertions
    // and with read access to the variables
    exprs.add(
      setup.ctx.mkEq(
        setup.mkEquals(tail, a, b),
        setup.mkAnd(heads.map {
          setup.mkEquals(it, a, b)
        })
      )
    )
  }

  return setup.mkAnd(exprs)
}

fun handleEquality(
  old: Reference?,
  target: Reference,
  expr: Reference,
  tail: SymbolicAssertion,
  heads: Set<SymbolicAssertion>,
  setup: ConstraintsSetup
): BoolExpr {
  val unknown = UnknownRef(expr.type)

  val assignments1 = if (old == null) {
    listOf(
      Pair(target, expr),
      Pair(expr, unknown)
    )
  } else {
    listOf(
      Pair(old, target),
      Pair(target, expr),
      Pair(expr, unknown)
    )
  }

  val assignments2 = if (old == null) {
    listOf(
      Pair(target, expr)
    )
  } else {
    listOf(
      Pair(old, target),
      Pair(target, expr)
    )
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

  fun accessReplace(p: Reference) = assignments1.foldRight(p) { (a, b), p -> p.replace(a, b) }
  fun equalsReplace(p: Reference) = assignments2.foldRight(p) { (a, b), p -> p.replace(a, b) }

  val exprs = mutableListOf<BoolExpr>()

  tail.forEach { ref, info ->
    val otherRef = accessReplace(ref)

    if (changedRefs.contains(ref)) {
      // The access permission to access the variables/fields that hold the relevant values
      // Remains the same
      exprs.add(setup.ctx.mkEq(
        setup.fractionToExpr(info.fraction),
        setup.min(heads.map { it[ref].fraction })
      ))
    } else {
      exprs.add(setup.ctx.mkEq(
        setup.fractionToExpr(info.fraction),
        setup.min(heads.map { it[otherRef].fraction })
      ))
    }

    exprs.add(setup.ctx.mkEq(
      setup.fractionToExpr(info.packFraction),
      setup.min(heads.map { it[otherRef].packFraction })
    ))

    // Subtyping constraints are more difficult for Z3 to solve
    // If this assertion is only implied by another one,
    // just add a constraint where the two types are the same
    if (heads.size == 1) {
      exprs.add(SymTypeEqSymType(heads.first()[otherRef].type, info.type).toZ3(setup))
    } else {
      for (head in heads) {
        exprs.add(SymTypeImpliesSymType(head[otherRef].type, info.type).toZ3(setup))
      }
    }
  }

  val equalities = tail.skeleton.equalities

  for ((a, b) in equalities) {
    val c = equalsReplace(a)
    val d = equalsReplace(b)
    exprs.add(when {
      c == d -> setup.mkEquals(tail, a, b)
      equalities.contains(Pair(c, d)) -> setup.ctx.mkEq(
        setup.mkEquals(tail, a, b),
        setup.mkAnd(heads.map {
          setup.mkEquals(it, c, d)
        })
      )
      else -> setup.ctx.mkNot(setup.mkEquals(tail, a, b))
    })
  }

  return setup.mkAnd(exprs)
}

fun handleCall(
  callRef: Reference,
  arguments: List<Reference>,
  parameters: List<Reference>,
  methodPre: SymbolicAssertion,
  methodPost: Set<SymbolicAssertion>,
  tail: SymbolicAssertion,
  heads: Set<SymbolicAssertion>,
  setup: ConstraintsSetup
): BoolExpr {
  val returnRef = ReturnSpecialVar(callRef.type)
  val exprs = mutableListOf<BoolExpr>()
  val changedRefs = arguments.toSet().plus(callRef)

  fun replace(p: Reference): Pair<Reference, Set<SymbolicAssertion>> {
    // TODO instead of p == x it should be hasPrefix(p, prefix = x)
    return if (p == callRef) {
      if (callRef.type.kind == TypeKind.VOID) {
        Pair(callRef, heads)
      } else {
        Pair(returnRef, methodPost)
      }
    } else {
      val idx = arguments.indexOf(p)
      if (idx < 0) {
        Pair(p, heads)
      } else {
        Pair(parameters[idx], methodPost)
      }
    }
  }

  // TODO add the fractions that were left in the current context

  tail.forEach { ref, info ->
    val (otherRef, otherHeads) = replace(ref)

    if (changedRefs.contains(ref)) {
      // The access permission to access the variables/fields that hold the relevant values
      // Remains the same
      exprs.add(setup.ctx.mkEq(
        setup.fractionToExpr(info.fraction),
        setup.min(heads.map { it[ref].fraction })
      ))
    } else {
      exprs.add(setup.ctx.mkEq(
        setup.fractionToExpr(info.fraction),
        setup.min(otherHeads.map { it[otherRef].fraction })
      ))
    }

    exprs.add(setup.ctx.mkEq(
      setup.fractionToExpr(info.packFraction),
      setup.min(otherHeads.map { it[otherRef].packFraction })
    ))

    // Subtyping constraints are more difficult for Z3 to solve
    // If this assertion is only implied by another one,
    // just add a constraint where the two types are the same
    if (otherHeads.size == 1) {
      exprs.add(SymTypeEqSymType(otherHeads.first()[otherRef].type, info.type).toZ3(setup))
    } else {
      for (head in otherHeads) {
        exprs.add(SymTypeImpliesSymType(head[otherRef].type, info.type).toZ3(setup))
      }
    }
  }

  // TODO equalities from inside the method that can be tracked outside!

  for ((a, b) in tail.skeleton.equalities) {
    val (c, cHeads) = replace(a)
    val (d, dHeads) = replace(b)
    exprs.add(when {
      c == d -> setup.mkEquals(tail, a, b)
      cHeads === dHeads -> {
        setup.ctx.mkEq(
          setup.mkEquals(tail, a, b),
          setup.mkAnd(cHeads.map {
            setup.mkEquals(it, c, d)
          })
        )
      }
      else -> setup.ctx.mkNot(setup.mkEquals(tail, a, b))
    })
  }

  return setup.mkAnd(exprs)
}

fun handleTypeImplication(exprs: MutableList<BoolExpr>, pres: Set<SymbolicAssertion>, ref: Reference, type: SymbolicType, setup: ConstraintsSetup) {
  // Subtyping constraints are more difficult for Z3 to solve
  // If this assertion is only implied by another one,
  // just add a constraint where the two types are the same
  if (pres.size == 1) {
    exprs.add(SymTypeEqSymType(pres.first().getType(ref), type).toZ3(setup))
  } else {
    for (pre in pres) {
      exprs.add(SymTypeImpliesSymType(pre.getType(ref), type).toZ3(setup))
    }
  }
}

private class ImpliedAssertion(val tail: SymbolicAssertion) : Constraint() {

  override fun toString(): String {
    return "($id) (${tail.impliedBy().joinToString(" && ")}}) ==> $tail"
  }

  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    return handleImplies(tail, tail.impliedBy(), setup, emptySet())
  }
}

private class NoSideEffects(assertions: NodeAssertions) : OnlyEffects(assertions, emptySet())

private open class OnlyEffects(val assertions: NodeAssertions, val except: Set<Reference>) : Constraint() {

  override fun toString(): String {
    return if (except.isEmpty()) "($id) NoSideEffects" else "($id) OnlyEffects {$except}"
  }

  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    return reduce(setup, assertions) { tail, heads ->
      handleImplies(tail, heads, setup, except)
    }
  }
}

// access(x, a) ==> access(x, b)
// a >= b
private class SymFractionImpliesSymFraction(val a: SymbolicFraction, val b: SymbolicFraction) : Constraint() {

  override fun toString(): String {
    return "($id) $a ==> $b"
  }

  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    val expr1 = setup.fractionToExpr(a)
    val expr2 = setup.fractionToExpr(b)
    return setup.ctx.mkGe(expr1, expr2)
  }
}

private class SymFractionEqSymFraction(val a: SymbolicFraction, val b: Collection<SymbolicFraction>) : Constraint() {

  constructor(a: SymbolicFraction, b: SymbolicFraction) : this(a, listOf(b))

  override fun toString(): String {
    return "($id) $a = $b"
  }

  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    return setup.ctx.mkEq(setup.fractionToExpr(a), setup.min(b))
  }
}

// typeof(x, a) ==> typeof(x, b)
// a <: b
// t1 <: t2
private class SymTypeImpliesSymType(val a: SymbolicType, val b: SymbolicType) : Constraint() {

  override fun toString(): String {
    return "($id) $a ==> $b"
  }

  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    val expr1 = setup.typeToExpr(a)
    val expr2 = setup.typeToExpr(b)
    return setup.mkSubtype(expr1, expr2)
  }
}

private class SymTypeEqSymType(val a: SymbolicType, val b: SymbolicType) : Constraint() {

  override fun toString(): String {
    return "($id) $a = $b"
  }

  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    val expr1 = setup.typeToExpr(a)
    val expr2 = setup.typeToExpr(b)
    return setup.ctx.mkEq(expr1, expr2)
  }
}

private class SymTypeEqType(val a: SymbolicType, val b: MungoType) : Constraint() {

  override fun toString(): String {
    return "($id) $a = $b"
  }

  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    val expr1 = setup.typeToExpr(a)
    val expr2 = setup.typeToExpr(b)
    return setup.ctx.mkEq(expr1, expr2)
  }
}

private class TypeImpliesSymType(val a: MungoType, val b: SymbolicType) : Constraint() {

  override fun toString(): String {
    return "($id) $a ==> $b"
  }

  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    val expr1 = setup.typeToExpr(a)
    val expr2 = setup.typeToExpr(b)
    return setup.mkSubtype(expr1, expr2)
  }
}

private class SymTypeImpliesType(val a: SymbolicType, val b: MungoType) : Constraint() {

  override fun toString(): String {
    return "($id) $a ==> $b"
  }

  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    val expr1 = setup.typeToExpr(a)
    val expr2 = setup.typeToExpr(b)
    return setup.mkSubtype(expr1, expr2)
  }
}

private class SymFractionGt(val a: SymbolicFraction, val b: Int) : Constraint() {

  override fun toString(): String {
    return "($id) $a > $b"
  }

  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    return setup.ctx.mkGt(setup.fractionToExpr(a), setup.ctx.mkReal(b))
  }
}

private class SymFractionEq(val a: SymbolicFraction, val b: Int) : Constraint() {

  override fun toString(): String {
    return "($id) $a = $b"
  }

  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    return setup.ctx.mkEq(setup.fractionToExpr(a), setup.ctx.mkReal(b))
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

  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    return setup.ctx.mkNot(setup.mkEquals(assertion, a, b))
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

  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    return reduce(setup, assertions) { tail, heads ->
      handleEquality(old, target, expr, tail, heads, setup)
    }
  }
}

// TODO handle fields
fun handleTransfer(
  resetExpr: Boolean,
  target: Reference,
  expr: Reference,
  tail: SymbolicAssertion,
  heads: Set<SymbolicAssertion>,
  setup: ConstraintsSetup
): BoolExpr {
  val exprs = mutableListOf<BoolExpr>()
  val postTargetInfo = tail[target]

  exprs.add(setup.ctx.mkEq(
    setup.fractionToExpr(postTargetInfo.packFraction),
    setup.min(heads.map { it[expr].packFraction })
  ))

  if (resetExpr) {
    val postExprInfo = tail[expr]
    exprs.add(setup.ctx.mkEq(
      setup.fractionToExpr(postExprInfo.packFraction),
      setup.ctx.mkReal(0)
    ))
  }

  handleTypeImplication(exprs, heads, expr, postTargetInfo.type, setup)

  if (resetExpr) {
    val postExprInfo = tail[expr]
    exprs.add(SymTypeEqType(postExprInfo.type, MungoUnknownType.SINGLETON).toZ3(setup))
  }

  return setup.mkAnd(exprs)
}

private class TransferOfExpressions(
  val resetExpr: Boolean,
  val assertions: NodeAssertions,
  val target: Reference,
  val expr: Reference
) : Constraint() {

  override fun toString(): String {
    return "($id) $target <- $expr;"
  }

  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    return reduce(setup, assertions) { tail, heads ->
      handleTransfer(resetExpr, target, expr, tail, heads, setup)
    }
  }
}

// TODO handle fields as well...
// Make the reference representing the parameter
// and the corresponding local variable equals
// But start with all the permission on the side of the parameter
private class ParameterAndLocalVariable(
  val assertion: SymbolicAssertion,
  val parameter: ParameterVariable,
  val local: LocalVariable
) : Constraint() {

  override fun toString(): String {
    return "($id) param+local: $parameter $local"
  }

  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    // val paramInfo = assertion[parameter]
    val localInfo = assertion[local]
    return setup.ctx.mkAnd(
      setup.mkEquals(assertion, parameter, local),
      setup.ctx.mkEq(
        setup.fractionToExpr(localInfo.packFraction),
        setup.ctx.mkReal(0)
      ),
      SymTypeEqType(localInfo.type, MungoUnknownType.SINGLETON).toZ3(setup)
    )
  }
}

// TODO handle fields as well...
private class PassingParameter(
  val expr: SymbolicInfo,
  val parameter: SymbolicInfo
) : Constraint() {

  override fun toString(): String {
    return "($id) param passing $expr -> $parameter"
  }

  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    return setup.ctx.mkAnd(
      SymFractionGt(expr.fraction, 0).toZ3(setup),
      SymFractionImpliesSymFraction(expr.packFraction, parameter.packFraction).toZ3(setup),
      if (parameter.ref is ThisReference) {
        setup.ctx.mkTrue()
      } else {
        SymTypeImpliesSymType(expr.type, parameter.type).toZ3(setup)
      }
    )
  }
}

// TODO handle fields as well...
private class RestoringParameter(
  val parameter: SymbolicInfo,
  val expr: SymbolicInfo
) : Constraint() {

  override fun toString(): String {
    return "($id) param restoring $expr <- $parameter"
  }

  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    return setup.ctx.mkAnd(
      // SymFractionGt(parameter.fraction, 0).toZ3(setup),
      SymFractionImpliesSymFraction(parameter.packFraction, expr.packFraction).toZ3(setup),
      if (parameter.ref is ThisReference) {
        setup.ctx.mkTrue()
      } else {
        SymTypeImpliesSymType(parameter.type, expr.type).toZ3(setup)
      }
    )
  }
}

private class OtherConstraint(val fn: (ConstraintsSetup) -> BoolExpr) : Constraint() {

  override fun toString(): String {
    return "($id) other"
  }

  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    return fn(setup)
  }
}

class Constraints {

  private lateinit var setup: ConstraintsSetup

  private val types = mutableSetOf(
    MungoUnknownType.SINGLETON,
    MungoObjectType.SINGLETON,
    MungoNoProtocolType.SINGLETON,
    MungoEndedType.SINGLETON,
    MungoNullType.SINGLETON,
    MungoPrimitiveType.SINGLETON,
    MungoMovedType.SINGLETON,
    MungoBottomType.SINGLETON
  )

  fun addType(type: MungoType) {
    types.add(type)
  }

  fun start(): Constraints {
    setup = ConstraintsSetup(types).start()
    return this
  }

  private val idToConstraint = mutableMapOf<String, Constraint>()

  fun labelToString(label: String): String {
    val c = idToConstraint[label.subSequence(1, label.lastIndex)]
    return c?.toString() ?: ""
  }

  fun end(): InferenceResult {
    for (constraint in constraints) {
      val label = "${constraint.id}"
      idToConstraint[label] = constraint
      setup.addAssert(constraint.toZ3(setup), label)
    }

    println("Solving...")
    return setup.end()
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

  fun onlyEffects(assertions: NodeAssertions, except: Set<Reference>) {
    constraints.add(OnlyEffects(assertions, except))
  }

  fun one(a: SymbolicFraction) {
    // a == 1
    constraints.add(SymFractionEq(a, 1))
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

  fun nullType(t: SymbolicType) {
    // t == Null
    addType(MungoNullType.SINGLETON)
    constraints.add(SymTypeEqType(t, MungoNullType.SINGLETON))
  }

  fun same(a: SymbolicType, b: SymbolicType) {
    // a == b
    constraints.add(SymTypeEqSymType(a, b))
  }

  fun same(a: SymbolicType, b: MungoType) {
    // a == b
    constraints.add(SymTypeEqType(a, b))
  }

  fun subtype(t1: SymbolicType, t2: MungoType) {
    // t1 <: t2
    addType(t2)
    constraints.add(SymTypeImpliesType(t1, t2))
  }

  fun subtype(t1: MungoType, t2: SymbolicType) {
    // t1 <: t2
    addType(t1)
    constraints.add(TypeImpliesSymType(t1, t2))
  }

  fun transfer(resetExpr: Boolean, assertions: NodeAssertions, target: Reference, expr: Reference) {
    constraints.add(TransferOfExpressions(resetExpr, assertions, target, expr))
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

  fun passingParameter(expr: SymbolicInfo, parameter: SymbolicInfo) {
    constraints.add(PassingParameter(expr, parameter))
  }

  fun restoringParameter(parameter: SymbolicInfo, expr: SymbolicInfo) {
    constraints.add(RestoringParameter(parameter, expr))
  }

  fun other(fn: (ConstraintsSetup) -> BoolExpr) {
    constraints.add(OtherConstraint(fn))
  }

}
