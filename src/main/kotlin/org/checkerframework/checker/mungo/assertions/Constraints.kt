package org.checkerframework.checker.mungo.assertions

import com.microsoft.z3.BoolExpr
import com.microsoft.z3.Expr
import org.checkerframework.checker.mungo.analysis.*
import org.checkerframework.checker.mungo.typecheck.*
import org.checkerframework.checker.mungo.utils.MungoUtils
import org.checkerframework.dataflow.cfg.node.ObjectCreationNode

private var constraintsUUID = 1L

class Z3Constraints : Iterable<BoolExpr> {

  private val phase1 = mutableListOf<BoolExpr>()
  private val phase2 = mutableListOf<BoolExpr>()
  private val all = mutableListOf<BoolExpr>()

  fun addIn1(expr: BoolExpr): Z3Constraints {
    phase1.add(expr)
    all.add(expr)
    return this
  }

  fun addIn2(expr: BoolExpr): Z3Constraints {
    phase2.add(expr)
    all.add(expr)
    return this
  }

  fun addAll(result: Z3Constraints): Z3Constraints {
    phase1.addAll(result.phase1)
    phase2.addAll(result.phase2)
    all.addAll(result.phase1)
    all.addAll(result.phase2)
    return this
  }

  fun phase1It() = phase1.iterator()

  fun phase2It() = phase2.iterator()

  override fun iterator(): Iterator<BoolExpr> {
    return all.iterator()
  }

}

sealed class Constraint {
  val id = constraintsUUID++
  abstract fun toZ3(setup: ConstraintsSetup): Z3Constraints
}

fun reduce(
  result: Z3Constraints,
  assertions: NodeAssertions,
  fn: (result: Z3Constraints, tail: SymbolicAssertion, heads: Set<SymbolicAssertion>) -> Unit
): Z3Constraints {
  if (assertions.postThen === assertions.postElse) {
    fn(result, assertions.postThen, setOf(assertions.preThen, assertions.preElse))
  } else {
    fn(result, assertions.postThen, setOf(assertions.preThen))
    fn(result, assertions.postElse, setOf(assertions.preElse))
  }
  return result
}

// TODO ensure that certain facts are only asserted with enough permission (i.e. isValid)
// TODO if the fraction is zero, the type should be Unknown instead
// TODO equalities only hold with enough permission

// TODO handle primitives, since they can be copied many times

fun fractionsAccumulation(setup: ConstraintsSetup, ref: FieldAccess, pres: Collection<SymbolicAssertion>, post: SymbolicAssertion): BoolExpr {
  val parent = ref.receiver
  // "otherParents" includes "parent"
  val otherParents = post.skeleton.getPossibleEq(parent)
  val addition = setup.ctx.mkAdd(
    *otherParents.map { otherParent ->
      val otherRef = ref.replace(parent, otherParent)
      val sub = setup.mkSub(
        setup.mkMin(pres.map { it[otherRef].fraction }),
        setup.fractionToExpr(post[otherRef].fraction)
      )
      setup.mkITE(
        setup.mkEquals(post, parent, otherParent),
        sub,
        setup.ctx.mkReal(0)
      )
    }.toTypedArray()
  )
  return setup.ctx.mkEq(addition, setup.ctx.mkReal(0))
}

// Example:
// x y z
// f1 + f2 + f3 = f4 + f5 + f6
// (f1 - f4) + (f2 - f5) + (f3 - f6) = 0
fun packFractionsAccumulation(setup: ConstraintsSetup, ref: Reference, pres: Collection<SymbolicAssertion>, post: SymbolicAssertion): BoolExpr {
  // "others" includes "ref"
  val others = post.skeleton.getPossibleEq(ref)
  val addition = setup.ctx.mkAdd(
    *others.map { other ->
      val sub = setup.mkSub(
        setup.mkMin(pres.map { it[other].packFraction }),
        setup.fractionToExpr(post[other].packFraction)
      )
      setup.mkITE(
        setup.mkEquals(post, ref, other),
        sub,
        setup.ctx.mkReal(0)
      )
    }.toTypedArray()
  )
  return setup.ctx.mkEq(addition, setup.ctx.mkReal(0))
}

fun typesAccumulation(setup: ConstraintsSetup, ref: Reference, pres: Collection<SymbolicAssertion>, post: SymbolicAssertion): Expr {
  // "others" includes "ref"
  val others = post.skeleton.getPossibleEq(ref)
  val typeExpr = setup.mkIntersectionWithExprs(others.map { other ->
    setup.mkITE(
      setup.mkEquals(post, ref, other),
      setup.mkUnion(pres.map { it[other].type }),
      setup.typeToExpr(MungoUnknownType.SINGLETON)
    )
  })
  return setup.ctx.mkITE(
    setup.ctx.mkGt(
      setup.fractionToExpr(post[ref].packFraction),
      setup.ctx.mkReal(0)
    ),
    typeExpr,
    setup.typeToExpr(MungoUnknownType.SINGLETON)
  )
}

fun handleImplies(
  tail: SymbolicAssertion,
  heads: Set<SymbolicAssertion>,
  setup: ConstraintsSetup,
  result: Z3Constraints
) {

  tail.forEach { ref, info ->
    if (ref is FieldAccess) {
      result.addIn1(fractionsAccumulation(setup, ref, heads, tail))
    } else {
      result.addIn1(setup.ctx.mkEq(
        setup.fractionToExpr(info.fraction),
        setup.mkMin(heads.map { it[ref].fraction })
      ))
    }

    result.addIn1(packFractionsAccumulation(setup, ref, heads, tail))

    result.addIn2(setup.ctx.mkEq(
      setup.typeToExpr(info.type),
      // setup.mkUnion(heads.map { it[ref].type })
      typesAccumulation(setup, ref, heads, tail)
    ))
  }

  // TODO equality of fields!
  for ((a, b) in tail.skeleton.equalities) {
    // Equality is true in assertion "tail" if present in the other assertions
    // and with read access to the variables
    result.addIn1(
      setup.ctx.mkEq(
        setup.mkEquals(tail, a, b),
        setup.mkAnd(heads.map {
          setup.mkEquals(it, a, b)
        })
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
  setup: ConstraintsSetup,
  result: Z3Constraints
) {
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

  tail.forEach { ref, info ->
    val otherRef = accessReplace(ref)

    if (changedRefs.contains(ref)) {
      // The access permission to access the variables/fields that hold the relevant values
      // Remains the same
      result.addIn1(setup.ctx.mkEq(
        setup.fractionToExpr(info.fraction),
        setup.mkMin(heads.map { it[ref].fraction })
      ))
    } else {
      result.addIn1(setup.ctx.mkEq(
        setup.fractionToExpr(info.fraction),
        setup.mkMin(heads.map { it[otherRef].fraction })
      ))
    }

    result.addIn1(setup.ctx.mkEq(
      setup.fractionToExpr(info.packFraction),
      setup.mkMin(heads.map { it[otherRef].packFraction })
    ))

    result.addIn2(setup.ctx.mkEq(
      setup.typeToExpr(info.type),
      setup.mkUnion(heads.map { it[otherRef].type })
    ))
  }

  val equalities = tail.skeleton.equalities

  for ((a, b) in equalities) {
    val c = equalsReplace(a)
    val d = equalsReplace(b)
    result.addIn1(setup.ctx.mkEq(
      setup.mkEquals(tail, a, b),
      setup.mkAnd(heads.map {
        setup.mkEquals(it, c, d)
      })
    ))
  }
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
  setup: ConstraintsSetup,
  result: Z3Constraints
) {
  val isConstructor = callRef is NodeRef && callRef.node is ObjectCreationNode
  val returnRef = ReturnSpecialVar(callRef.type)
  val thisRef = ThisReference(callRef.type)
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

    if (ref.hasPrefix(callRef)) {
      result.addIn1(setup.ctx.mkEq(
        setup.fractionToExpr(info.fraction),
        setup.mkMin(methodPost.map { it[otherRef].fraction })
      ))

      result.addIn1(setup.ctx.mkEq(
        setup.fractionToExpr(info.packFraction),
        setup.mkMin(methodPost.map { it[otherRef].packFraction })
      ))
    } else {
      // newFraction = prevFraction - stolenFraction
      // newFraction = prevFraction - ( fractionInPre - fractionInPost )

      val stolenFraction = if (ref === otherRef || changedRefs.contains(ref)) {
        setup.mkZero()
      } else {
        setup.mkSub(
          setup.fractionToExpr(methodPre[otherRef].fraction),
          setup.mkMin(methodPost.map { it[otherRef].fraction })
        )
      }

      result.addIn1(setup.ctx.mkEq(
        setup.fractionToExpr(info.fraction),
        setup.mkSub(
          setup.mkMin(heads.map { it[ref].fraction }),
          stolenFraction
        )
      ))

      val stolenPackedFraction = if (ref === otherRef) {
        setup.mkZero()
      } else {
        setup.mkSub(
          setup.fractionToExpr(methodPre[otherRef].packFraction),
          setup.mkMin(methodPost.map { it[otherRef].packFraction })
        )
      }

      result.addIn1(setup.ctx.mkEq(
        setup.fractionToExpr(info.packFraction),
        setup.mkSub(
          setup.mkMin(heads.map { it[ref].packFraction }),
          stolenPackedFraction
        )
      ))
    }

    if (overrideType != null) {
      if (
        (ref == callRef && isConstructor) ||
        (ref == receiverRef)
      ) {
        result.addAll(SymTypeEqType(info.type, overrideType).toZ3(setup))
        return@forEach
      }
    }

    if (ref === otherRef) {
      result.addIn2(setup.ctx.mkEq(
        setup.typeToExpr(info.type),
        setup.mkUnion(heads.map { it[ref].type })
      ))
    } else {
      result.addIn2(setup.ctx.mkEq(
        setup.typeToExpr(info.type),
        setup.mkUnion(methodPost.map { it[otherRef].type })
      ))
    }
  }

  // TODO am I able to track equalities of old values? like after this.item = newItem ??
  // TODO equalities from inside the method that can be tracked outside!

  for ((a, b) in tail.skeleton.equalities) {
    val c = replace(a)
    val d = replace(b)
    result.addIn1(when {
      c == d -> setup.mkEquals(tail, a, b)
      a === c && b === d -> {
        setup.ctx.mkEq(
          setup.mkEquals(tail, a, b),
          setup.mkAnd(heads.map {
            setup.mkEquals(it, a, b)
          })
        )
        // TODO could be true via transitivity?
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
}

private class ImpliedAssertion(val tail: SymbolicAssertion) : Constraint() {

  override fun toString(): String {
    return "($id) (${tail.impliedBy().joinToString(" && ")}}) ==> $tail"
  }

  override fun toZ3(setup: ConstraintsSetup): Z3Constraints {
    val result = Z3Constraints()
    handleImplies(tail, tail.impliedBy(), setup, result)
    return result
  }
}

private class NoSideEffects(val assertions: NodeAssertions) : Constraint() {

  override fun toString(): String {
    return "($id) NoSideEffects"
  }

  override fun toZ3(setup: ConstraintsSetup): Z3Constraints {
    return reduce(Z3Constraints(), assertions) { result, tail, heads ->
      handleImplies(tail, heads, setup, result)
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
    return "($id) Call $callRef"
  }

  override fun toZ3(setup: ConstraintsSetup): Z3Constraints {
    return reduce(Z3Constraints(), assertions) { result, tail, heads ->
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
        setup,
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

  override fun toZ3(setup: ConstraintsSetup): Z3Constraints {
    val result = Z3Constraints()

    fun helper(parameter: Reference, local: Reference) {
      val paramInfo = assertion[parameter]
      val localInfo = assertion[local]
      if (local !== this.local) {
        result.addIn1(setup.ctx.mkEq(
          setup.fractionToExpr(localInfo.fraction),
          setup.ctx.mkReal(0)
        ))
      }
      result.addIn1(setup.ctx.mkEq(
        setup.fractionToExpr(localInfo.packFraction),
        setup.ctx.mkReal(0)
      ))
      result.addIn2(setup.ctx.mkEq(
        setup.typeToExpr(localInfo.type),
        setup.typeToExpr(MungoUnknownType.SINGLETON)
      ))
      paramInfo.children.map { (ref, _) ->
        helper(ref, ref.replace(parameter, local))
      }
    }

    result.addIn1(setup.mkEquals(assertion, parameter, local))

    helper(parameter, local)
    return result
  }
}

private class PassingParameter(
  val expr: SymbolicInfo,
  val parameter: SymbolicInfo
) : Constraint() {

  override fun toString(): String {
    return "($id) param passing $expr -> $parameter"
  }

  override fun toZ3(setup: ConstraintsSetup): Z3Constraints {
    val result = Z3Constraints()

    fun helper(expr: SymbolicInfo, parameter: SymbolicInfo) {
      result.addAll(if (expr === this.expr) {
        SymFractionGt(expr.fraction, 0).toZ3(setup)
      } else {
        SymFractionImpliesSymFraction(expr.fraction, parameter.fraction).toZ3(setup)
      })
      result.addAll(SymFractionImpliesSymFraction(expr.packFraction, parameter.packFraction).toZ3(setup))
      result.addAll(SymTypeImpliesSymType(expr.type, parameter.type).toZ3(setup))
      expr.children.map { (ref, info) ->
        helper(info, parameter.children[ref.replace(expr.ref, parameter.ref)]!!)
      }
    }

    helper(expr, parameter)
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

  override fun toZ3(setup: ConstraintsSetup): Z3Constraints {
    return Z3Constraints().addIn1(setup.ctx.mkNot(setup.mkEquals(assertion, a, b)))
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

  override fun toZ3(setup: ConstraintsSetup): Z3Constraints {
    return reduce(Z3Constraints(), assertions) { result, tail, heads ->
      handleEquality(old, target, expr, tail, heads, setup, result)
    }
  }
}

// access(x, a) ==> access(x, b)
// a >= b
private class SymFractionImpliesSymFraction(val a: SymbolicFraction, val b: SymbolicFraction) : Constraint() {

  override fun toString(): String {
    return "($id) $a ==> $b"
  }

  override fun toZ3(setup: ConstraintsSetup): Z3Constraints {
    val expr1 = setup.fractionToExpr(a)
    val expr2 = setup.fractionToExpr(b)
    return Z3Constraints().addIn1(setup.ctx.mkGe(expr1, expr2))
  }
}

private class SymFractionEqSymFraction(val a: SymbolicFraction, val b: Collection<SymbolicFraction>) : Constraint() {

  constructor(a: SymbolicFraction, b: SymbolicFraction) : this(a, listOf(b))

  override fun toString(): String {
    return "($id) $a = $b"
  }

  override fun toZ3(setup: ConstraintsSetup): Z3Constraints {
    return Z3Constraints().addIn1(setup.ctx.mkEq(setup.fractionToExpr(a), setup.mkMin(b)))
  }
}

// typeof(x, a) ==> typeof(x, b)
// a <: b
// t1 <: t2
private class SymTypeImpliesSymType(val a: SymbolicType, val b: SymbolicType) : Constraint() {

  override fun toString(): String {
    return "($id) $a ==> $b"
  }

  override fun toZ3(setup: ConstraintsSetup): Z3Constraints {
    val expr1 = setup.typeToExpr(a)
    val expr2 = setup.typeToExpr(b)
    return Z3Constraints().addIn2(setup.mkSubtype(expr1, expr2))
  }
}

private class SymTypeEqSymType(val a: SymbolicType, val b: SymbolicType) : Constraint() {

  override fun toString(): String {
    return "($id) $a = $b"
  }

  override fun toZ3(setup: ConstraintsSetup): Z3Constraints {
    val expr1 = setup.typeToExpr(a)
    val expr2 = setup.typeToExpr(b)
    return Z3Constraints().addIn2(setup.ctx.mkEq(expr1, expr2))
  }
}

private class SymTypeEqType(val a: SymbolicType, val b: MungoType) : Constraint() {

  override fun toString(): String {
    return "($id) $a = $b"
  }

  override fun toZ3(setup: ConstraintsSetup): Z3Constraints {
    val expr1 = setup.typeToExpr(a)
    val expr2 = setup.typeToExpr(b)
    return Z3Constraints().addIn2(setup.ctx.mkEq(expr1, expr2))
  }
}

private class TypeImpliesSymType(val a: MungoType, val b: SymbolicType) : Constraint() {

  override fun toString(): String {
    return "($id) $a ==> $b"
  }

  override fun toZ3(setup: ConstraintsSetup): Z3Constraints {
    val expr1 = setup.typeToExpr(a)
    val expr2 = setup.typeToExpr(b)
    return Z3Constraints().addIn2(setup.mkSubtype(expr1, expr2))
  }
}

private class SymTypeImpliesType(val a: SymbolicType, val b: MungoType) : Constraint() {

  override fun toString(): String {
    return "($id) $a ==> $b"
  }

  override fun toZ3(setup: ConstraintsSetup): Z3Constraints {
    val expr1 = setup.typeToExpr(a)
    val expr2 = setup.typeToExpr(b)
    return Z3Constraints().addIn2(setup.mkSubtype(expr1, expr2))
  }
}

private class SymFractionGt(val a: SymbolicFraction, val b: Int) : Constraint() {

  override fun toString(): String {
    return "($id) $a > $b"
  }

  override fun toZ3(setup: ConstraintsSetup): Z3Constraints {
    return Z3Constraints().addIn1(setup.ctx.mkGt(setup.fractionToExpr(a), setup.ctx.mkReal(b)))
  }
}

private class SymFractionEq(val a: SymbolicFraction, val b: Int) : Constraint() {

  override fun toString(): String {
    return "($id) $a = $b"
  }

  override fun toZ3(setup: ConstraintsSetup): Z3Constraints {
    return Z3Constraints().addIn1(setup.ctx.mkEq(setup.fractionToExpr(a), setup.ctx.mkReal(b)))
  }
}

private class OtherConstraint(val fn: (ConstraintsSetup) -> Z3Constraints) : Constraint() {

  override fun toString(): String {
    return "($id) other"
  }

  override fun toZ3(setup: ConstraintsSetup): Z3Constraints {
    return fn(setup)
  }
}

class Constraints {

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

  private val idToConstraint = mutableMapOf<String, Pair<Constraint, Expr>>()

  fun getConstraintByLabel(label: String): Pair<Constraint, Expr> {
    return idToConstraint[label.subSequence(1, label.lastIndex)]!!
  }

  fun solve(): InferenceResult {
    started = true
    val setup = ConstraintsSetup(types).start()
    val phase2Iterators = mutableListOf<Pair<Constraint, Iterator<BoolExpr>>>()

    for (constraint in constraints) {
      val z3exprs = constraint.toZ3(setup)
      val phase1 = z3exprs.phase1It()
      val phase2 = z3exprs.phase2It()
      phase2Iterators.add(Pair(constraint, phase2))

      for ((idx, z3expr) in phase1.withIndex()) {
        val label = "${constraint.id}-$idx-1"
        idToConstraint[label] = Pair(constraint, z3expr)
        setup.addAssert(z3expr, label)
      }
    }

    println("Solving (phase 1)...")
    val result1 = setup.solve()
    println("Phase 1 done")

    if (result1 !is Solution) {
      return result1
    }

    setup.push()

    for ((constraint, phase2) in phase2Iterators) {
      for ((idx, z3expr) in phase2.withIndex()) {
        val label = "${constraint.id}-$idx-2"
        val simplified = result1.eval(z3expr)
        idToConstraint[label] = Pair(constraint, simplified)
        setup.addAssert(simplified, label)
      }
    }

    println("Solving (phase 2)...")
    val result2 = setup.solve()
    println("Phase 2 done")
    return result2
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

  fun other(fn: (ConstraintsSetup) -> Z3Constraints) {
    constraints.add(OtherConstraint(fn))
  }

}
