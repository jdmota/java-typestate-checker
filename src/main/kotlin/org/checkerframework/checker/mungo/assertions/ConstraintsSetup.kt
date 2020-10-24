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
        if (a !== b) allTypes.add(MungoUnionType.create(listOf(a, b)))
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
    val Real = ctx.realSort
    val Location = ctx.mkUninterpretedSort("Location")

    val typeSymbols = typesWithUnions.map { Pair(it, typeToSymbol(it)) }.toMap()
    val typesArray = typeSymbols.values.toTypedArray()

    val Type = ctx.mkEnumSort(ctx.mkSymbol("Type"), *typesArray)
    val TypeExprs = typeSymbols.map { (type, sym) ->
      Pair(type, ctx.mkApp(Type.getConstDecl(typesArray.indexOf(sym))))
    }.toMap()

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

    val min = ctx.mkRecFuncDecl(ctx.mkSymbol("fMin"), arrayOf(Real, Real), Real) { _, args ->
      val a = args[0] as ArithExpr
      val b = args[1] as ArithExpr
      ctx.mkITE(ctx.mkLe(a, b), a, b)
    }
  }

  fun <T : Expr> mkITE(condition: BoolExpr, a: T, b: T): T = when (condition) {
    setup.True -> a
    setup.False -> b
    else -> ctx.mkITE(condition, a, b) as T
  }

  fun mkSubtype(a: Expr, b: Expr) = ctx.mkApp(setup.subtype, a, b) as BoolExpr
  fun mkSubtype(a: SymbolicType, b: SymbolicType) = mkSubtype(typeToExpr(a), typeToExpr(b))

  fun mkEquals(assertion: SymbolicAssertion, a: Expr, b: Expr) = if (a === b) {
    setup.True
  } else {
    ctx.mkApp(assertionToEq(assertion), a, b) as BoolExpr
  }

  fun mkEquals(assertion: SymbolicAssertion, a: Reference, b: Reference) = mkEquals(assertion, refToExpr(a), refToExpr(b))

  fun mkMin(a: ArithExpr, b: ArithExpr) = if (a === b) {
    a
  } else {
    ctx.mkApp(setup.min, a, b) as ArithExpr
  }

  private var eqUuid = 1L
  private val assertionToEq = mutableMapOf<SymbolicAssertion, FuncDecl>()

  // Get "eq" function for a certain assertion
  fun assertionToEq(a: SymbolicAssertion): FuncDecl {
    return assertionToEq.computeIfAbsent(a) {
      val fn = ctx.mkFuncDecl("eq${eqUuid++}", arrayOf(setup.Location, setup.Location), setup.Bool)

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
  fun typeToExpr(t: MungoType) = setup.TypeExprs[t] ?: error("No expression for $t")

  private var refUuid = 1L
  private val refToExpr = mutableMapOf<Reference, Expr>()

  // Get an Z3 expression for a location
  fun refToExpr(ref: Reference): Expr {
    return refToExpr.computeIfAbsent(ref) {
      ctx.mkConst("ref${refUuid++}", setup.Location)
    }
  }

  fun min(fraction: Collection<SymbolicFraction>): ArithExpr {
    val iterator = fraction.iterator()
    var expr = fractionToExpr(iterator.next())
    while (iterator.hasNext()) {
      expr = mkMin(expr, fractionToExpr(iterator.next()))
    }
    return expr
  }

  fun fractionsAccumulation(thisRef: Reference, pres: Collection<SymbolicAssertion>, post: SymbolicAssertion): BoolExpr {
    val others = post.skeleton.getPossibleEq(thisRef)
    // Example:
    // x y z
    // f1 + f2 + f3 = f4 + f5 + f6
    // (f1 - f4) + (f2 - f5) + (f3 - f6) = 0
    val thisRefExpr = refToExpr(thisRef)
    val addition = ctx.mkAdd(
      *others.map { ref ->
        val otherRef = refToExpr(ref)
        val sub = ctx.mkSub(
          min(pres.map { it.getAccessDotZero(ref) }),
          fractionToExpr(post.getAccessDotZero(ref))
        )
        mkITE(
          mkEquals(post, thisRefExpr, otherRef),
          sub,
          ctx.mkReal(0)
        )
      }.toTypedArray()
    )
    return ctx.mkEq(addition, ctx.mkReal(0))
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

  fun end(): InferenceResult {
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
