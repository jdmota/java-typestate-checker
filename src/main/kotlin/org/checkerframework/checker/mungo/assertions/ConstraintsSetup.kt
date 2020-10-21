package org.checkerframework.checker.mungo.assertions

import com.microsoft.z3.*
import org.checkerframework.checker.mungo.analysis.Reference
import org.checkerframework.checker.mungo.typecheck.*

// Z3 Tutorial: http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.225.8231&rep=rep1&type=pdf
// Z3 Guide and Playground: https://rise4fun.com/z3/tutorial/guide
// Z3 Java Api: https://z3prover.github.io/api/html/namespacecom_1_1microsoft_1_1z3.html

class ConstraintsSetup(private val types: Set<MungoType>) {

  val ctx = Z3Context()

  private val symbols = object {
    val subtype = ctx.mkSymbol("subtype")
    val Type = ctx.mkSymbol("Type")
    val typeSymbols = types.map { Pair(it, typeToSymbol(it)) }.toMap()
    val typeSymbolsArray = typeSymbols.values.toTypedArray()
  }

  private fun typeToSymbol(type: MungoType): Symbol {
    return ctx.mkSymbol(when (type) {
      is MungoUnionType -> "TU_${type.types.joinToString("_")}"
      is MungoStateType -> "TS${type.state.id}"
      is MungoMovedType -> "TMoved"
      is MungoPrimitiveType -> "TPrim"
      is MungoNullType -> "TNull"
      is MungoEndedType -> "TEnded"
      is MungoNoProtocolType -> "TNo"
      is MungoObjectType -> "TObj"
      is MungoUnknownType -> "TUnknown"
      is MungoBottomType -> "TBottom"
    })
  }

  private val setup = object {
    val Bool = ctx.boolSort
    val Real = ctx.realSort

    val Location = ctx.mkUninterpretedSort("Location")

    val Type = ctx.mkEnumSort(symbols.Type, *symbols.typeSymbolsArray)
    val TypeExprs = symbols.typeSymbols.map { (type, sym) ->
      Pair(type, ctx.mkApp(Type.getConstDecl(symbols.typeSymbolsArray.indexOf(sym))))
    }.toMap()

    val subtype = ctx.mkRecFuncDecl(symbols.subtype, arrayOf(Type, Type), Bool) { _, args ->
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
      }.toTypedArray())//.simplify()
      println(code)
      code
    }
  }

  fun mkSubtype(a: Expr, b: Expr) = mkApp(setup.subtype, a, b)

  fun mkEquals(assertion: SymbolicAssertion, a: Expr, b: Expr) = mkApp(assertionToEq(assertion), a, b)

  private fun mkApp(fn: FuncDecl, a: Expr, b: Expr) = ctx.mkApp(fn, a, b) as BoolExpr

  private var eqUuid = 1L
  private val assertionToEq = mutableMapOf<SymbolicAssertion, FuncDecl>()

  // Get "eq" function for a certain assertion
  fun assertionToEq(a: SymbolicAssertion): FuncDecl {
    return assertionToEq.computeIfAbsent(a) {
      val fn = ctx.mkFuncDecl("eq${eqUuid++}", arrayOf(setup.Location, setup.Location), setup.Bool)

      // Reflexive
      // (assert (forall ((x Loc)) (eq x x)))
      addAssert(ctx.mkForall(arrayOf(setup.Location)) { args ->
        mkApp(fn, args[0], args[0])
      })

      // Transitive
      // (assert (forall ((x Loc) (y Loc) (z Loc)) (=> (and (eq x y) (eq y z)) (eq x z))))
      addAssert(ctx.mkForall(arrayOf(setup.Location, setup.Location, setup.Location)) { args ->
        ctx.mkImplies(
          ctx.mkAnd(
            mkApp(fn, args[0], args[1]),
            mkApp(fn, args[1], args[2])
          ),
          mkApp(fn, args[0], args[2])
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

  // @pre: "ref" is also in "others"
  fun fractionsAccumulation(ref: Reference, others: Set<Reference>, pre: SymbolicAssertion, post: SymbolicAssertion, equals: Boolean): BoolExpr {
    // Example:
    // x y z
    // f1 + f2 + f3 >= f4 + f5 + f6
    // f1 - f4 + f2 - f5 + f3 - f6 >= 0
    val thisRefExpr = refToExpr(ref)
    val addition = ctx.mkAdd(
      *others.map {
        ctx.mkITE(
          mkEquals(pre, thisRefExpr, refToExpr(it)),
          ctx.mkSub(
            fractionToExpr(pre.getAccessDotZero(it)),
            fractionToExpr(post.getAccessDotZero(it))
          ),
          ctx.mkReal(0)
        ) as ArithExpr
      }.toTypedArray()
    )
    return if (equals) ctx.mkEq(addition, ctx.mkReal(0)) else ctx.mkGe(addition, ctx.mkReal(0))
  }

  private lateinit var solver: Solver

  fun start(): ConstraintsSetup {
    solver = ctx.mkSolver()
    spec()
    return this
  }

  fun addAssert(expr: BoolExpr) {
    solver.add(expr)
  }

  fun end(): Solution? {
    val result = solver.check()
    val hasModel = result == Status.SATISFIABLE
    if (hasModel) {
      return Solution(this, solver.model)
    }
    return null
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

/*fun main(args: Array<String>) {
  ConstraintsSetup(setOf(
    MungoNoProtocolType.SINGLETON,
    MungoEndedType.SINGLETON,
    MungoNullType.SINGLETON,
    MungoPrimitiveType.SINGLETON,
    MungoMovedType.SINGLETON
  )).start()
}*/
