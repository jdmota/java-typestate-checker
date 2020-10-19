package org.checkerframework.checker.mungo.assertions

import com.microsoft.z3.*
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

  fun mkSubtype(a: Expr, b: Expr) = ctx.mkApp(setup.subtype, a, b) as BoolExpr

  private val symbolicFractionToExpr = mutableMapOf<SymbolicFraction, ArithExpr>()
  fun fractionToExpr(f: SymbolicFraction) = symbolicFractionToExpr.computeIfAbsent(f) {
    val c = ctx.mkConst("f${f.id}", setup.Real) as ArithExpr
    // 0 <= c <= 1
    addAssert(ctx.mkAnd(ctx.mkGe(c, ctx.mkReal(0)), ctx.mkLe(c, ctx.mkReal(1))))
    c
  }

  private val symbolicTypeToExpr = mutableMapOf<SymbolicType, Expr>()
  fun typeToExpr(t: SymbolicType) = symbolicTypeToExpr.computeIfAbsent(t) {
    ctx.mkConst("t${t.id}", setup.Type)
  }

  fun typeToExpr(t: MungoType) = setup.TypeExprs[t] ?: error("No expression for $t")

  private lateinit var solver: Solver
  private val proveBasicProperties = true

  fun start(): ConstraintsSetup {
    solver = ctx.mkSolver()

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
      /*addAssert(ctx.mkForall(arrayOf(setup.Type, setup.Type, setup.Type)) { args ->
        ctx.mkImplies(
          ctx.mkAnd(
            mkSubtype(args[0], args[1]),
            mkSubtype(args[1], args[2])
          ),
          mkSubtype(args[0], args[2])
        )
      })*/

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

    return this
  }

  fun addAssert(expr: BoolExpr) {
    println(expr)
    solver.add(expr)
  }

  fun end() {
    val result = solver.check()

    val check = when (result) {
      Status.SATISFIABLE -> true
      Status.UNKNOWN -> false
      Status.UNSATISFIABLE -> false
      else -> false
    }

    println("Solved: $result")

    val model = solver.model

    // debugText += result.toString()
    // debugText += "\n"
    debugText += model.toString()
  }

  private var debugText = ""

  fun debug() {
    println(debugText)
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
