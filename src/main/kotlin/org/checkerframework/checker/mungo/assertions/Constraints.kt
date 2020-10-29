package org.checkerframework.checker.mungo.assertions

import com.microsoft.z3.BoolExpr
import com.microsoft.z3.Expr
import org.checkerframework.checker.mungo.analysis.*
import org.checkerframework.checker.mungo.typecheck.*
import org.checkerframework.checker.mungo.utils.MungoUtils
import org.checkerframework.dataflow.cfg.node.ObjectCreationNode

private var constraintsUUID = 1L

class ConstraintsSet(val constraint: Constraint) : Iterable<TinyBoolExpr> {

  private val phase1 = mutableListOf<TinyBoolExpr>()
  private val phase2 = mutableListOf<TinyBoolExpr>()
  private val all = mutableListOf<TinyBoolExpr>()

  fun addIn1(expr: TinyBoolExpr): ConstraintsSet {
    phase1.add(expr)
    all.add(expr)
    return this
  }

  fun addIn2(expr: TinyBoolExpr): ConstraintsSet {
    phase2.add(expr)
    all.add(expr)
    return this
  }

  fun addAll(result: ConstraintsSet): ConstraintsSet {
    phase1.addAll(result.phase1)
    phase2.addAll(result.phase2)
    all.addAll(result.phase1)
    all.addAll(result.phase2)
    return this
  }

  fun phase1It() = phase1.iterator()

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

// TODO ensure that certain facts are only asserted with enough permission (i.e. isValid)
// TODO if the fraction is zero, the type should be Unknown instead
// TODO equalities only hold with enough permission

// TODO handle primitives, since they can be copied many times

// TODO is it possible that Z3 assigns an equality to true, even without support?
// eq(a,b) && eq(b,c) ==> eq(a,c)
// but even though eq(a,b) && eq(b,c) is false, Z3 makes eq(a,c) true, allowing undesirable transferring of permissions?
// Answer: no, since mkEquals() will default to False if we talk about an equality that is not in the assertion skeleton
// TODO but this means that the transitivity is not useful...

fun fractionsAccumulation(ref: FieldAccess, pres: Collection<SymbolicAssertion>, post: SymbolicAssertion): TinyBoolExpr {
  val parent = ref.receiver
  // "otherParents" includes "parent"
  val otherParents = post.skeleton.getPossibleEq(parent)
  val addition = Make.S.add(
    otherParents.map { otherParent ->
      val otherRef = ref.replace(parent, otherParent)
      val sub = Make.S.sub(
        Make.S.min(pres.map { it[otherRef].fraction.expr }),
        post[otherRef].fraction.expr
      )
      Make.S.ite(
        Make.S.equals(post, parent, otherParent),
        sub,
        Make.ZERO
      )
    }
  )
  return Make.S.eq(addition, Make.ZERO)
}

// Example:
// x y z
// f1 + f2 + f3 = f4 + f5 + f6
// (f1 - f4) + (f2 - f5) + (f3 - f6) = 0
fun packFractionsAccumulation(ref: Reference, pres: Collection<SymbolicAssertion>, post: SymbolicAssertion): TinyBoolExpr {
  // "others" includes "ref"
  val others = post.skeleton.getPossibleEq(ref)
  val addition = Make.S.add(
    others.map { other ->
      val sub = Make.S.sub(
        Make.S.min(pres.map { it[other].packFraction.expr }),
        post[other].packFraction.expr
      )
      Make.S.ite(
        Make.S.equals(post, ref, other),
        sub,
        Make.ZERO
      )
    }
  )
  return Make.S.eq(addition, Make.ZERO)
}

// TODO remember that packFraction > 0 only holds if fraction > 0 also holds!
fun typesAccumulation(ref: Reference, pres: Collection<SymbolicAssertion>, post: SymbolicAssertion): TinyMungoTypeExpr {
  // "others" includes "ref"
  val others = post.skeleton.getPossibleEq(ref)
  val typeExpr = Make.S.intersection(others.map { other ->
    Make.S.ite(
      Make.S.equals(post, ref, other),
      Make.S.union(pres.map { it[other].type.expr }),
      Make.S.type(MungoUnknownType.SINGLETON)
    )
  })
  return Make.S.ite(
    Make.S.gt(
      post[ref].packFraction.expr,
      Make.ZERO
    ),
    typeExpr,
    Make.S.type(MungoUnknownType.SINGLETON)
  )
}

fun handleImplies(
  tail: SymbolicAssertion,
  heads: Set<SymbolicAssertion>,
  result: ConstraintsSet
) {
  tail.forEach { ref, info ->
    if (ref is FieldAccess) {
      result.addIn1(fractionsAccumulation(ref, heads, tail))
    } else {
      result.addIn1(Make.S.eq(
        info.fraction.expr,
        Make.S.min(heads.map { it[ref].fraction.expr })
      ))
    }

    result.addIn1(packFractionsAccumulation(ref, heads, tail))

    result.addIn2(Make.S.eq(
      info.type.expr,
      typesAccumulation(ref, heads, tail)
    ))
  }

  // TODO equality of fields!
  for ((a, b) in tail.skeleton.equalities) {
    // Equality is true in assertion "tail" if present in the other assertions
    // and with read access to the variables
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

  val equalities = tail.skeleton.equalities

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
  result: ConstraintsSet
) {
  val isConstructor = callRef is NodeRef && callRef.node is ObjectCreationNode
  val returnRef = ReturnSpecialVar(callRef.type)
  val thisRef = ThisReference(callRef.type)
  val changedRefs = arguments.toSet().plus(callRef)

  // TODO what if use(cell, cell.item) ??

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
      result.addIn1(Make.S.eq(
        info.fraction.expr,
        Make.S.min(methodPost.map { it[otherRef].fraction.expr })
      ))

      result.addIn1(Make.S.eq(
        info.packFraction.expr,
        Make.S.min(methodPost.map { it[otherRef].packFraction.expr })
      ))
    } else {
      // newFraction = prevFraction - stolenFraction
      // newFraction = prevFraction - ( fractionInPre - fractionInPost )

      val stolenFraction = if (ref === otherRef || changedRefs.contains(ref)) {
        Make.ZERO
      } else {
        Make.S.sub(
          methodPre[otherRef].fraction.expr,
          Make.S.min(methodPost.map { it[otherRef].fraction.expr })
        )
      }

      result.addIn1(Make.S.eq(
        info.fraction.expr,
        Make.S.sub(
          Make.S.min(heads.map { it[ref].fraction.expr }),
          stolenFraction
        )
      ))

      val stolenPackedFraction = if (ref === otherRef) {
        Make.ZERO
      } else {
        Make.S.sub(
          methodPre[otherRef].packFraction.expr,
          Make.S.min(methodPost.map { it[otherRef].packFraction.expr })
        )
      }

      result.addIn1(Make.S.eq(
        info.packFraction.expr,
        Make.S.sub(
          Make.S.min(heads.map { it[ref].packFraction.expr }),
          stolenPackedFraction
        )
      ))
    }

    if (overrideType != null) {
      if (
        (ref == callRef && isConstructor) ||
        (ref == receiverRef)
      ) {
        result.addAll(SymTypeEqType(info.type, overrideType).build())
        return@forEach
      }
    }

    if (ref === otherRef) {
      result.addIn2(Make.S.eq(
        info.type.expr,
        Make.S.union(heads.map { it[ref].type.expr })
      ))
    } else {
      result.addIn2(Make.S.eq(
        info.type.expr,
        Make.S.union(methodPost.map { it[otherRef].type.expr })
      ))
    }
  }

  // TODO am I able to track equalities of old values? like after this.item = newItem ??

  fun isMaybeModified(ref: Reference): Boolean {
    return ref.hasPrefix(callRef) || arguments.any { it != ref && ref.hasPrefix(it) }
  }

  for ((a, b) in tail.skeleton.equalities) {
    val c = replace(a)
    val d = replace(b)

    val aWasPassed = isMaybeModified(a)
    val bWasPassed = isMaybeModified(b)

    val aIsNotModified = if (aWasPassed) Make.S.lt(methodPre[c].fraction.expr, Make.ONE) else Make.TRUE
    val bIsNotModified = if (bWasPassed) Make.S.lt(methodPre[d].fraction.expr, Make.ONE) else Make.TRUE

    result.addIn1(Make.S.eq(
      Make.S.equals(tail, a, b),
      Make.S.ite(
        Make.S.and(listOf(aIsNotModified, bIsNotModified)),
        // None is modified, equality holds if it holds before
        Make.S.and(heads.map {
          Make.S.equals(it, a, b)
        }),
        Make.S.ite(
          Make.S.and(listOf(aIsNotModified)),
          // Only b is modified...
          if (aWasPassed) {
            Make.S.and(methodPost.map {
              Make.S.equals(it, c, d)
            })
          } else {
            // This means that "a" did not even go into the method
            Make.S.equalsTransitive(tail, a, b)
          },
          Make.S.ite(
            Make.S.and(listOf(bIsNotModified)),
            // Only a is modified...
            if (bWasPassed) {
              Make.S.and(methodPost.map {
                Make.S.equals(it, c, d)
              })
            } else {
              // This means that "b" did not even go into the method
              Make.S.equalsTransitive(tail, a, b)
            },
            // Both are modified, equality only holds if present in the method post-condition
            Make.S.and(methodPost.map {
              Make.S.equals(it, c, d)
            })
          )
        )
      )
    ))
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
      handleImplies(tail, heads, result)
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

  override fun build(): ConstraintsSet {
    return reduce(ConstraintsSet(this), assertions) { result, tail, heads ->
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
        Make.S.type(MungoUnknownType.SINGLETON)
      ))
      paramInfo.children.map { (ref, _) ->
        helper(ref, ref.replace(parameter, local))
      }
    }

    result.addIn1(Make.S.equals(assertion, parameter, local))

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

  override fun build(): ConstraintsSet {
    val result = ConstraintsSet(this)

    fun helper(expr: SymbolicInfo, parameter: SymbolicInfo) {
      result.addAll(if (expr === this.expr) {
        SymFractionGt(expr.fraction, 0).build()
      } else {
        SymFractionImpliesSymFraction(expr.fraction, parameter.fraction).build()
      })
      result.addAll(SymFractionImpliesSymFraction(expr.packFraction, parameter.packFraction).build())
      result.addAll(SymTypeImpliesSymType(expr.type, parameter.type).build())
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

private class SymTypeEqType(val a: SymbolicType, val b: MungoType) : Constraint() {
  override fun toString(): String {
    return "($id) $a = $b"
  }

  override fun build(): ConstraintsSet {
    return ConstraintsSet(this).addIn2(Make.S.eq(a.expr, Make.S.type(b)))
  }
}

private class TypeImpliesSymType(val a: MungoType, val b: SymbolicType) : Constraint() {
  override fun toString(): String {
    return "($id) $a ==> $b"
  }

  override fun build(): ConstraintsSet {
    return ConstraintsSet(this).addIn2(Make.S.subtype(Make.S.type(a), b.expr))
  }
}

private class SymTypeImpliesType(val a: SymbolicType, val b: MungoType) : Constraint() {
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

  private val idToConstraint = mutableMapOf<String, Triple<Constraint, TinyBoolExpr, BoolExpr>>()

  fun getConstraintByLabel(label: String): Triple<Constraint, TinyBoolExpr, BoolExpr> {
    return idToConstraint[label.subSequence(1, label.lastIndex)]!!
  }

  fun formatExpr(expr: Expr, solution: IncompleteSolution? = null): String {
    val initial = expr.toString().replace("(", "( ").replace(")", " )")
    return initial.split(' ').joinToString(" ") {
      when (val something = setup.keyToSomething[it]) {
        is Reference -> something.toString()
        is String -> if (something.startsWith('f')) {
          solution?.eval(setup.mkFraction(something))?.toString() ?: it
        } else {
          it
        }
        else -> it
      }
    }
  }

  private val splitIn2Phases = true
  private lateinit var setup: ConstraintsSetup

  private fun solveIn1Phase(): InferenceResult {
    setup = ConstraintsSetup(types).start()

    for (constraint in constraints) {
      val set = constraint.build()

      for ((idx, expr) in set.phase1It().withIndex()) {
        val label = "${constraint.id}-$idx-1"
        val z3expr = expr.toZ3(setup)
        idToConstraint[label] = Triple(constraint, expr, z3expr)
        setup.addAssert(z3expr, label)
      }

      for ((idx, expr) in set.phase2It().withIndex()) {
        val label = "${constraint.id}-$idx-2"
        val z3expr = expr.toZ3(setup)
        idToConstraint[label] = Triple(constraint, expr, z3expr)
        setup.addAssert(z3expr, label)
      }
    }

    println("Solving...")
    return setup.solve()
  }

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

  private fun solveIn2Phases(): InferenceResult {
    setup = ConstraintsSetup(types).start()
    val constraintsSets = constraints.map { it.build() }
    val allPhase1Exprs = mutableListOf<Triple<Constraint, TinyBoolExpr, TinyBoolExpr>>()
    val allPhase2Exprs = mutableListOf<Triple<Constraint, TinyBoolExpr, TinyBoolExpr>>()

    // println("Simplifying...")
    /*val simplifier = Simplifier()
    for (set in constraintsSets) {
      for (expr in set) {
        simplifier.track(expr)
      }
    }*/

    // Simplify...
    for (set in constraintsSets) {
      for (expr in set.phase1It()) {
        allPhase1Exprs.add(Triple(set.constraint, expr, expr /*simplifier.simplify(expr)*/))
      }
      for (expr in set.phase2It()) {
        allPhase2Exprs.add(Triple(set.constraint, expr, expr /*simplifier.simplify(expr)*/))
      }
    }

    // Phase 1...

    for ((idx, triple) in allPhase1Exprs.withIndex()) {
      val (constraint, expr, simplifiedExpr) = triple
      val label = "${constraint.id}-$idx-1"
      val z3expr = expr.toZ3(setup)
      idToConstraint[label] = Triple(constraint, expr, z3expr)
      setup.addAssert(z3expr, label)
    }

    println("Solving (phase 1)...")
    val result1 = setup.solve()
    println("Phase 1 done")

    if (result1 !is Solution) {
      return result1
    }

    // Phase 2...

    setup.push()

    for ((idx, triple) in allPhase2Exprs.withIndex()) {
      val (constraint, expr, simplifiedExpr) = triple
      val label = "${constraint.id}-$idx-2"
      val z3expr = expr.toZ3(setup)
      val simplified = result1.eval(z3expr)
      idToConstraint[label] = Triple(constraint, expr, z3expr)
      setup.addAssert(simplified, label)
    }

    println("Solving (phase 2)...")
    val result2 = setup.solve()
    println("Phase 2 done")

    if (result2 !is Solution) {
      return IncompleteSolution(setup, result1.model, if (result2 is NoSolution) result2.unsatCore else null)
    }
    return result2
  }

  fun solve(): InferenceResult {
    started = true
    return if (splitIn2Phases) {
      solveIn2Phases()
    } else {
      solveIn1Phase()
    }
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

  fun other(fn: (Constraint) -> ConstraintsSet) {
    constraints.add(OtherConstraint(fn))
  }

}
