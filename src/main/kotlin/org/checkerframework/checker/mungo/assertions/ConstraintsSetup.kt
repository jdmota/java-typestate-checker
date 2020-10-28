package org.checkerframework.checker.mungo.assertions

import com.microsoft.z3.*
import org.checkerframework.checker.mungo.analysis.Reference
import org.checkerframework.checker.mungo.typecheck.*

// Z3 Tutorial: http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.225.8231&rep=rep1&type=pdf
// Z3 Guide and Playground: https://rise4fun.com/z3/tutorial/guide
// Z3 Java Api: https://z3prover.github.io/api/html/namespacecom_1_1microsoft_1_1z3.html

class ConstraintsSetup(usedTypes: Set<MungoType>) {

  val ctx = Z3Context()

  private val typesWithUnions = run {
    val allTypes = mutableListOf<MungoType>()
    usedTypes.forEach { a ->
      usedTypes.forEach { b ->
        // TODo do not create unions for now...
        // if (a !== b) allTypes.add(MungoUnionType.create(listOf(a, b)))
      }
    }
    allTypes.addAll(usedTypes)
    allTypes.toSet()
  }

  private val labelToType = mutableMapOf<String, MungoType>()

  fun labelToType(label: String) = labelToType[label] ?: error("No type for label $label")

  private fun typeToLabel(type: MungoType): String {
    val label = when (type) {
      is MungoUnionType -> "TU_${type.types.joinToString("_") { typeToLabel(it) }}"
      is MungoStateType -> "TS${type.state.id}"
      is MungoMovedType -> "TMoved"
      is MungoPrimitiveType -> "TPrim"
      is MungoNullType -> "TNull"
      is MungoEndedType -> "TEnded"
      is MungoNoProtocolType -> "TNo"
      is MungoObjectType -> "TObj"
      is MungoUnknownType -> "TUnknown"
      is MungoBottomType -> "TBottom"
    }
    labelToType[label] = type
    return label
  }

  private fun typeToSymbol(type: MungoType): Symbol {
    return ctx.mkSymbol(typeToLabel(type))
  }

  private val setup = object {
    val Bool = ctx.boolSort
    val True = ctx.mkTrue()
    val False = ctx.mkFalse()
    val Zero = ctx.mkReal(0)
    val Real = ctx.realSort
    val Location = ctx.mkUninterpretedSort("Location")

    val typeSymbols = typesWithUnions.map { Pair(it, typeToSymbol(it)) }.toMap()
    val typesArray = typeSymbols.values.toTypedArray()

    val Type = ctx.mkEnumSort(ctx.mkSymbol("Type"), *typesArray)
    val TypeExprs = typeSymbols.map { (type, sym) ->
      Pair(type, ctx.mkApp(Type.getConstDecl(typesArray.indexOf(sym))))
    }.toMap()

    val UnknownExpr = TypeExprs[MungoUnknownType.SINGLETON]!!

    val subtype = ctx.mkRecFuncDecl(ctx.mkSymbol("subtype"), arrayOf(Type, Type), Bool) { _, args ->
      val a = args[0]
      val b = args[1]
      val code = ctx.mkAnd(*TypeExprs.map { (typeA, exprA) ->
        ctx.mkImplies(
          ctx.mkEq(a, exprA),
          ctx.mkAnd(*TypeExprs.map { (typeB, exprB) ->
            ctx.mkImplies(
              ctx.mkEq(b, exprB),
              ctx.mkBool(typeA.isSubtype(typeB))
            )
          }.toTypedArray())
        )
      }.toTypedArray())
      // println(code)
      code
    }

    fun closestUpperBound(type: MungoType) = when {
      TypeExprs.contains(type) -> type
      type.isSubtype(MungoObjectType.SINGLETON) -> MungoObjectType.SINGLETON
      else -> MungoUnknownType.SINGLETON
    }

    val union = ctx.mkRecFuncDecl(ctx.mkSymbol("union"), arrayOf(Type, Type), Type) { _, args ->
      val a = args[0]
      val b = args[1]

      fun helper2(typeA: MungoType, it: Iterator<Map.Entry<MungoType, Expr>>): Expr {
        if (it.hasNext()) {
          val (typeB, exprB) = it.next()
          val union = closestUpperBound(typeA.union(typeB))
          return ctx.mkITE(
            ctx.mkEq(b, exprB),
            TypeExprs[union],
            helper2(typeA, it)
          )
        }
        return UnknownExpr
      }

      fun helper1(it: Iterator<Map.Entry<MungoType, Expr>>): Expr {
        if (it.hasNext()) {
          val (typeA, exprA) = it.next()
          return ctx.mkITE(
            ctx.mkEq(a, exprA),
            helper2(typeA, TypeExprs.iterator()),
            helper1(it)
          )
        }
        return UnknownExpr
      }

      val code = helper1(TypeExprs.iterator())
      // println(code)
      code
    }

    val intersection = ctx.mkRecFuncDecl(ctx.mkSymbol("intersection"), arrayOf(Type, Type), Type) { _, args ->
      val a = args[0]
      val b = args[1]

      fun helper2(typeA: MungoType, it: Iterator<Map.Entry<MungoType, Expr>>): Expr {
        if (it.hasNext()) {
          val (typeB, exprB) = it.next()
          val intersection = closestUpperBound(typeA.intersect(typeB))
          return ctx.mkITE(
            ctx.mkEq(b, exprB),
            TypeExprs[intersection],
            helper2(typeA, it)
          )
        }
        return UnknownExpr
      }

      fun helper1(it: Iterator<Map.Entry<MungoType, Expr>>): Expr {
        if (it.hasNext()) {
          val (typeA, exprA) = it.next()
          return ctx.mkITE(
            ctx.mkEq(a, exprA),
            helper2(typeA, TypeExprs.iterator()),
            helper1(it)
          )
        }
        return UnknownExpr
      }

      val code = helper1(TypeExprs.iterator())
      // println(code)
      code
    }

    val min = ctx.mkRecFuncDecl(ctx.mkSymbol("fMin"), arrayOf(Real, Real), Real) { _, args ->
      val a = args[0] as ArithExpr
      val b = args[1] as ArithExpr
      ctx.mkITE(ctx.mkLe(a, b), a, b)
    }
  }

  fun <T : Expr> mkITE(condition: BoolExpr, a: T, b: T): T = when {
    condition === setup.True -> a
    condition === setup.False -> b
    a === b -> a
    else -> ctx.mkITE(condition, a, b) as T
  }

  fun mkSubtype(a: Expr, b: Expr) = ctx.mkApp(setup.subtype, a, b) as BoolExpr
  fun mkSubtype(a: SymbolicType, b: SymbolicType) = mkSubtype(typeToExpr(a), typeToExpr(b))

  private fun mkEquals(assertion: SymbolicAssertion, a: Expr, b: Expr): BoolExpr =
    if (a === b) {
      setup.True
    } else {
      ctx.mkApp(assertionToEq(assertion), a, b) as BoolExpr
    }

  fun mkEquals(assertion: SymbolicAssertion, a: Reference, b: Reference): BoolExpr =
    when {
      a == b -> setup.True
      assertion.skeleton.equalities.contains(Pair(a, b)) -> mkEquals(assertion, refToExpr(a), refToExpr(b))
      assertion.skeleton.equalities.contains(Pair(b, a)) -> mkEquals(assertion, refToExpr(b), refToExpr(a))
      else -> setup.False
    }

  // exists x :: eq(a, x) && eq(x, b)
  fun mkEqualsTransitive(assertion: SymbolicAssertion, a: Reference, b: Reference): BoolExpr {
    // "a" and "b" are in this set
    val possibleEqualities = assertion.skeleton.getPossibleEq(a)
    val others = possibleEqualities.filterNot { it == a || it == b }

    return mkOr(others.map {
      mkAnd(listOf(
        mkEquals(assertion, a, it),
        mkEquals(assertion, it, b)
      ))
    })
    /*return ctx.mkExists(arrayOf(setup.Location)) { args ->
      val x = args[0]
      ctx.mkAnd(
        mkEquals(assertion, refToExpr(a), x),
        mkEquals(assertion, x, refToExpr(b))
      )
    }*/
  }

  fun mkAnd(b: Collection<BoolExpr>): BoolExpr {
    if (b.contains(setup.False))
      return setup.False

    val bools = b.filterNot { it === setup.True }

    return when {
      bools.isEmpty() -> setup.True
      bools.size == 1 -> bools.first()
      else -> ctx.mkAnd(*bools.toTypedArray())
    }
  }

  fun mkOr(b: Collection<BoolExpr>): BoolExpr {
    if (b.contains(setup.True))
      return setup.True

    val bools = b.filterNot { it === setup.False }

    return when {
      bools.isEmpty() -> setup.False
      bools.size == 1 -> bools.first()
      else -> ctx.mkOr(*bools.toTypedArray())
    }
  }

  fun mkBool(b: Boolean): BoolExpr = if (b) setup.True else setup.False

  fun mkZero(): RatNum = setup.Zero

  fun mkLt(f: SymbolicFraction, num: Int): BoolExpr = ctx.mkLt(fractionToExpr(f), ctx.mkReal(num))

  fun mkSub(a: ArithExpr, b: ArithExpr): ArithExpr {
    return if (b === setup.Zero) {
      a
    } else {
      ctx.mkSub(a, b)
    }
  }

  private fun mkMin(a: ArithExpr, b: ArithExpr) =
    if (a === b) {
      a
    } else {
      ctx.mkApp(setup.min, a, b) as ArithExpr
    }

  fun mkMin(fractions: Collection<SymbolicFraction>): ArithExpr {
    val iterator = fractions.iterator()
    var expr = fractionToExpr(iterator.next())
    while (iterator.hasNext()) {
      expr = mkMin(expr, fractionToExpr(iterator.next()))
    }
    return expr
  }

  private fun mkUnion(a: Expr, b: Expr) =
    if (a === b) {
      a
    } else {
      ctx.mkApp(setup.union, a, b)
    }

  fun mkUnion(types: Collection<SymbolicType>): Expr {
    val iterator = types.iterator()
    var expr = typeToExpr(iterator.next())
    while (iterator.hasNext()) {
      expr = mkUnion(expr, typeToExpr(iterator.next()))
    }
    return expr
  }

  private fun mkIntersection(a: Expr, b: Expr) =
    if (a === b) {
      a
    } else {
      ctx.mkApp(setup.intersection, a, b)
    }

  fun mkIntersectionWithExprs(types: Collection<Expr>): Expr {
    var expr: Expr? = null
    for (t in types.filterNot { it === setup.UnknownExpr }) {
      expr = if (expr == null) t else mkIntersection(expr, t)
    }
    return expr ?: setup.UnknownExpr
  }

  val keyToSomething = mutableMapOf<String, Any>()

  private var eqUuid = 1L
  private val assertionToEq = mutableMapOf<SymbolicAssertion, FuncDecl>()

  // Get "eq" function for a certain assertion
  private fun assertionToEq(a: SymbolicAssertion): FuncDecl {
    return assertionToEq.computeIfAbsent(a) {
      val key = "eq${eqUuid++}"
      // keyToSomething[key] = a

      val fn = ctx.mkFuncDecl(key, arrayOf(setup.Location, setup.Location), setup.Bool)

      // Reflexive
      // (assert (forall ((x Loc)) (eq x x)))
      addAssert(ctx.mkForall(arrayOf(setup.Location)) { args ->
        ctx.mkApp(fn, args[0], args[0]) as BoolExpr
      })

      // Symmetric
      // (assert (forall ((x Loc) (y Loc)) (= (eq x y) (eq y x))))
      addAssert(ctx.mkForall(arrayOf(setup.Location, setup.Location)) { args ->
        ctx.mkEq(
          ctx.mkApp(fn, args[0], args[1]) as BoolExpr,
          ctx.mkApp(fn, args[1], args[0]) as BoolExpr
        )
      })

      // Transitive
      // (assert (forall ((x Loc) (y Loc) (z Loc)) (=> (and (eq x y) (eq y z)) (eq x z))))
      addAssert(ctx.mkForall(arrayOf(setup.Location, setup.Location, setup.Location)) { args ->
        ctx.mkImplies(
          ctx.mkAnd(
            ctx.mkApp(fn, args[0], args[1]) as BoolExpr,
            ctx.mkApp(fn, args[1], args[2]) as BoolExpr
          ),
          ctx.mkApp(fn, args[0], args[2]) as BoolExpr
        )
      })

      fn
    }
  }

  private val symbolicFractionToExpr = mutableMapOf<SymbolicFraction, ArithExpr>()

  // Get an Z3 expression for a symbolic fraction
  fun fractionToExpr(f: SymbolicFraction) = symbolicFractionToExpr.computeIfAbsent(f) {
    val c = ctx.mkConst(f.z3Symbol(), setup.Real) as ArithExpr
    // 0 <= c <= 1
    addAssert(ctx.mkAnd(ctx.mkGe(c, ctx.mkReal(0)), ctx.mkLe(c, ctx.mkReal(1))))
    c
  }

  private val symbolicTypeToExpr = mutableMapOf<SymbolicType, Expr>()

  // Get an Z3 expression for a symbolic type
  fun typeToExpr(t: SymbolicType) = symbolicTypeToExpr.computeIfAbsent(t) {
    ctx.mkConst(t.z3Symbol(), setup.Type)
  }

  // Get an Z3 expression for a type
  fun typeToExpr(t: MungoType): Expr = setup.TypeExprs[t] ?: error("No expression for $t")

  private var refUuid = 1L
  private val refToExpr = mutableMapOf<Reference, Expr>()

  // Get an Z3 expression for a location
  private fun refToExpr(ref: Reference): Expr {
    return refToExpr.computeIfAbsent(ref) {
      val key = "ref${refUuid++}"
      keyToSomething[key] = ref
      ctx.mkConst(key, setup.Location)
    }
  }

  private lateinit var solver: Solver

  fun start(): ConstraintsSetup {
    solver = ctx.mkSolver()
    spec()
    return this
  }

  private fun addAssert(expr: BoolExpr) {
    solver.add(expr)
    // println(expr)
  }

  fun addAssert(expr: BoolExpr, label: String) {
    if (label.isNotEmpty()) {
      solver.assertAndTrack(expr, ctx.mkBoolConst(label))
    } else {
      solver.add(expr)
    }
    // println(expr)
  }

  fun push() {
    solver.push()
  }

  fun solve(): InferenceResult {
    val result = solver.check()
    val hasModel = result == Status.SATISFIABLE
    if (hasModel) {
      return Solution(this, solver.model)
    }
    return if (result == Status.UNSATISFIABLE) {
      NoSolution(solver.unsatCore)
    } else {
      UnknownSolution(solver.reasonUnknown)
    }
  }

  private val proveBasicProperties = false
  private val proveTransitiveProperty = false // This one is slow to prove

  private fun spec() {
    if (proveBasicProperties) {
      // Reflexive
      // (assert (forall ((x Type)) (subtype x x)))
      addAssert(ctx.mkForall(arrayOf(setup.Type)) { args ->
        mkSubtype(args[0], args[0])
      })

      // Antisymmetric
      // (assert (forall ((x Type) (y Type)) (= (and (subtype x y) (subtype y x)) (= x y))))
      addAssert(ctx.mkForall(arrayOf(setup.Type, setup.Type)) { args ->
        ctx.mkEq(
          ctx.mkAnd(
            mkSubtype(args[0], args[1]),
            mkSubtype(args[1], args[0])
          ),
          ctx.mkEq(args[0], args[1])
        )
      })

      // Transitive
      // (assert (forall ((x Type) (y Type) (z Type)) (=> (and (subtype x y) (subtype y z)) (subtype x z))))
      if (proveTransitiveProperty) {
        addAssert(ctx.mkForall(arrayOf(setup.Type, setup.Type, setup.Type)) { args ->
          ctx.mkImplies(
            ctx.mkAnd(
              mkSubtype(args[0], args[1]),
              mkSubtype(args[1], args[2])
            ),
            mkSubtype(args[0], args[2])
          )
        })
      }

      // All subtypes of Unknown
      // (assert (forall ((t Type)) (subtype t Unknown)))
      addAssert(ctx.mkForall(arrayOf(setup.Type)) { args ->
        mkSubtype(args[0], typeToExpr(MungoUnknownType.SINGLETON))
      })

      // Single top
      // (assert (exists ((t Type)) (and (= t Unknown) (forall ((x Type)) (subtype x t)))))
      addAssert(ctx.mkExists(arrayOf(setup.Type)) { args ->
        ctx.mkAnd(
          ctx.mkEq(args[0], typeToExpr(MungoUnknownType.SINGLETON)),
          ctx.mkForall(arrayOf(setup.Type)) { innerArgs ->
            mkSubtype(innerArgs[0], args[0])
          }
        )
      })

      // Bottom subtype of all
      // (assert (forall ((t Type)) (subtype Bottom t)))
      addAssert(ctx.mkForall(arrayOf(setup.Type)) { args ->
        mkSubtype(typeToExpr(MungoBottomType.SINGLETON), args[0])
      })

      // Single bottom
      // (assert (exists ((t Type)) (and (= t Bottom) (forall ((x Type)) (subtype t x)))))
      addAssert(ctx.mkExists(arrayOf(setup.Type)) { args ->
        ctx.mkAnd(
          ctx.mkEq(args[0], typeToExpr(MungoBottomType.SINGLETON)),
          ctx.mkForall(arrayOf(setup.Type)) { innerArgs ->
            mkSubtype(args[0], innerArgs[0])
          }
        )
      })

      val result = solver.check()
      if (result != Status.SATISFIABLE) {
        throw RuntimeException("Could not prove basic properties: $result")
      }
    }
  }

}
