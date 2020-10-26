package org.checkerframework.checker.mungo.assertions

import com.microsoft.z3.BoolExpr
import org.checkerframework.checker.mungo.analysis.*
import org.checkerframework.checker.mungo.typecheck.*
import org.checkerframework.checker.mungo.utils.MungoUtils
import org.checkerframework.dataflow.cfg.node.ObjectCreationNode

private var constraintsUUID = 1L

sealed class Constraint {
  val id = constraintsUUID++
  abstract fun toZ3(setup: ConstraintsSetup): BoolExpr
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

fun handleImplies(tail: SymbolicAssertion, heads: Set<SymbolicAssertion>, setup: ConstraintsSetup): BoolExpr {
  val exprs = mutableListOf<BoolExpr>()

  tail.forEach { ref, info ->
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
  receiverRef: Reference?,
  overrideType: MungoType?,
  arguments: List<Reference>,
  parameters: List<Reference>,
  methodPre: SymbolicAssertion,
  methodPost: Set<SymbolicAssertion>,
  tail: SymbolicAssertion,
  heads: Set<SymbolicAssertion>,
  setup: ConstraintsSetup
): BoolExpr {
  val isConstructor = callRef is NodeRef && callRef.node is ObjectCreationNode
  val returnRef = ReturnSpecialVar(callRef.type)
  val thisRef = ThisReference(callRef.type)
  val exprs = mutableListOf<BoolExpr>()
  val changedRefs = arguments.toSet().plus(callRef)

  fun replace(p: Reference): Reference {
    return if (p.hasPrefix(callRef)) {
      when {
        isConstructor -> p.replace(callRef, thisRef)
        else -> p.replace(callRef, returnRef)
      }
    } else {
      val idx = arguments.indexOfFirst { p.hasPrefix(it) }
      if (idx < 0) {
        p
      } else {
        p.replace(arguments[idx], parameters[idx])
      }
    }
  }

  tail.forEach { ref, info ->
    val otherRef = replace(ref)

    // newFraction = prevFraction - stolenFraction
    // newFraction = prevFraction - ( fractionInPre - fractionInPost )

    val stolenFraction = if (ref === otherRef || changedRefs.contains(ref)) {
      setup.mkZero()
    } else {
      setup.mkSub(
        setup.fractionToExpr(methodPre[otherRef].fraction),
        setup.min(methodPost.map { it[otherRef].fraction })
      )
    }

    exprs.add(setup.ctx.mkEq(
      setup.fractionToExpr(info.fraction),
      setup.mkSub(
        setup.min(heads.map { it[ref].fraction }),
        stolenFraction
      )
    ))

    val stolenPackedFraction = if (ref === otherRef) {
      setup.mkZero()
    } else {
      setup.mkSub(
        setup.fractionToExpr(methodPre[otherRef].packFraction),
        setup.min(methodPost.map { it[otherRef].packFraction })
      )
    }

    exprs.add(setup.ctx.mkEq(
      setup.fractionToExpr(info.packFraction),
      setup.mkSub(
        setup.min(heads.map { it[ref].packFraction }),
        stolenPackedFraction
      )
    ))

    if (overrideType != null) {
      if (
        (ref == callRef && isConstructor) ||
        (ref == receiverRef)
      ) {
        exprs.add(SymTypeEqType(info.type, overrideType).toZ3(setup))
        return@forEach
      }
    }

    if (ref === otherRef) {
      if (heads.size == 1) {
        exprs.add(SymTypeEqSymType(heads.first()[ref].type, info.type).toZ3(setup))
      } else {
        heads.forEach {
          exprs.add(SymTypeImpliesSymType(it[otherRef].type, info.type).toZ3(setup))
        }
      }
    } else {
      if (methodPost.size == 1) {
        exprs.add(SymTypeEqSymType(methodPost.first()[otherRef].type, info.type).toZ3(setup))
      } else {
        methodPost.forEach {
          exprs.add(SymTypeImpliesSymType(it[otherRef].type, info.type).toZ3(setup))
        }
      }
    }
  }

  // TODO equalities from inside the method that can be tracked outside!

  for ((a, b) in tail.skeleton.equalities) {
    val c = replace(a)
    val d = replace(b)
    exprs.add(when {
      c == d -> setup.mkEquals(tail, a, b)
      a === c && b === d -> {
        setup.ctx.mkEq(
          setup.mkEquals(tail, a, b),
          setup.mkAnd(heads.map {
            setup.mkEquals(it, a, b)
          })
        )
      }
      a !== c && b !== d -> {
        setup.ctx.mkEq(
          setup.mkEquals(tail, a, b),
          setup.mkAnd(methodPost.map {
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
    return handleImplies(tail, tail.impliedBy(), setup)
  }
}

private class NoSideEffects(val assertions: NodeAssertions) : Constraint() {

  override fun toString(): String {
    return "($id) NoSideEffects"
  }

  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    return reduce(setup, assertions) { tail, heads ->
      handleImplies(tail, heads, setup)
    }
  }
}

private class CallConstraints(
  val assertions: NodeAssertions,
  val callRef: Reference,
  val receiverRef: Reference?,
  val receiverType: MungoType?,
  val arguments: List<Reference>,
  val parameters: List<Reference>,
  val methodPre: SymbolicAssertion,
  val methodPost: Set<SymbolicAssertion>
) : Constraint() {

  override fun toString(): String {
    return "($id) Call"
  }

  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    return reduce(setup, assertions) { tail, heads ->
      handleCall(
        callRef,
        receiverRef,
        receiverType,
        arguments,
        parameters,
        methodPre,
        methodPost,
        tail,
        heads,
        setup
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

  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    fun helper(parameter: Reference, local: Reference): BoolExpr {
      val paramInfo = assertion[parameter]
      val localInfo = assertion[local]
      return setup.ctx.mkAnd(
        if (parameter === this.parameter) {
          setup.ctx.mkTrue()
        } else {
          setup.ctx.mkEq(
            setup.fractionToExpr(localInfo.fraction),
            setup.ctx.mkReal(0)
          )
        },
        setup.ctx.mkEq(
          setup.fractionToExpr(localInfo.packFraction),
          setup.ctx.mkReal(0)
        ),
        SymTypeEqType(localInfo.type, MungoUnknownType.SINGLETON).toZ3(setup),
        setup.mkAnd(paramInfo.children.map { (ref, _) ->
          helper(ref, ref.replace(parameter, local))
        })
      )
    }
    return setup.ctx.mkAnd(
      setup.mkEquals(assertion, parameter, local),
      helper(parameter, local)
    )
  }
}

private class PassingParameter(
  val expr: SymbolicInfo,
  val parameter: SymbolicInfo
) : Constraint() {

  override fun toString(): String {
    return "($id) param passing $expr -> $parameter"
  }

  override fun toZ3(setup: ConstraintsSetup): BoolExpr {
    fun helper(expr: SymbolicInfo, parameter: SymbolicInfo): BoolExpr {
      return setup.ctx.mkAnd(
        if (expr === this.expr) {
          SymFractionGt(expr.fraction, 0).toZ3(setup)
        } else {
          SymFractionImpliesSymFraction(expr.fraction, parameter.fraction).toZ3(setup)
        },
        SymFractionImpliesSymFraction(expr.packFraction, parameter.packFraction).toZ3(setup),
        SymTypeImpliesSymType(expr.type, parameter.type).toZ3(setup),
        /*if (parameter.ref is ThisReference) {
          setup.ctx.mkTrue()
        } else {
          SymTypeImpliesSymType(expr.type, parameter.type).toZ3(setup)
        }*/
        setup.mkAnd(expr.children.map { (ref, info) ->
          helper(info, parameter.children[ref.replace(expr.ref, parameter.ref)]!!)
        })
      )
    }
    return helper(expr, parameter)
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
  private var started = false

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
    if (started) {
      MungoUtils.printStack()
      error("Already started adding constraints to Z3")
    }
    types.add(type)
  }

  fun start(): Constraints {
    started = true
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
    same(t, MungoNullType.SINGLETON)
  }

  fun same(a: SymbolicType, b: SymbolicType) {
    // a == b
    constraints.add(SymTypeEqSymType(a, b))
  }

  fun same(a: SymbolicType, b: MungoType) {
    // a == b
    addType(b)
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
    overrideType: MungoType?,
    arguments: List<Reference>,
    parameters: List<Reference>,
    methodPre: SymbolicAssertion,
    methodPost: Set<SymbolicAssertion>
  ) {
    overrideType?.let { addType(it) }
    constraints.add(CallConstraints(
      assertions,
      callRef,
      receiverRef,
      overrideType,
      arguments,
      parameters,
      methodPre,
      methodPost
    ))
  }

  fun passingParameter(expr: SymbolicInfo, parameter: SymbolicInfo) {
    constraints.add(PassingParameter(expr, parameter))
  }

  fun other(fn: (ConstraintsSetup) -> BoolExpr) {
    constraints.add(OtherConstraint(fn))
  }

}
