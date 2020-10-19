package org.checkerframework.checker.mungo.assertions

import com.microsoft.z3.*
import org.checkerframework.checker.mungo.typecheck.*

// Z3 Tutorial: http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.225.8231&rep=rep1&type=pdf
// Z3 Guide and Playground: https://rise4fun.com/z3/tutorial/guide
// Z3 Java Api: https://z3prover.github.io/api/html/namespacecom_1_1microsoft_1_1z3.html

class ConstraintsSetup(private val singletonTypes: Set<MungoType>) {

  val ctx = Z3Context()

  private val symbols = object {
    val subtype = ctx.mkSymbol("subtype")

    val Bottom = ctx.mkSymbol("Bottom")
    val Unknown = ctx.mkSymbol("Unknown")
    // val Object = ctx.mkSymbol("Object")

    val Type0 = ctx.mkSymbol("Type0")
    val type0Symbols = singletonTypes.map { Pair(it, typeToSymbol(it)) }.toMap()
    val type0SymbolsArray = type0Symbols.values.toTypedArray()
  }

  private fun typeToSymbol(type: MungoType): Symbol {
    return ctx.mkSymbol(when (type) {
      is MungoUnionType -> throw RuntimeException("Unexpected $type")
      is MungoStateType -> "State_${type.state.id}"
      is MungoMovedType -> "Moved"
      is MungoPrimitiveType -> "Primitive"
      is MungoNullType -> "Null"
      is MungoEndedType -> "Ended"
      is MungoNoProtocolType -> "NoProtocol"
      is MungoObjectType -> throw RuntimeException("Unexpected $type")
      is MungoUnknownType -> throw RuntimeException("Unexpected $type")
      is MungoBottomType -> throw RuntimeException("Unexpected $type")
    })
  }

  private val setup = object {
    val Bool = ctx.boolSort
    val False = ctx.mkFalse()
    val True = ctx.mkTrue()

    val Real = ctx.realSort

    // (declare-datatypes () ((Type0 Ended NoProtocol Null Primitive Moved)))
    val Type0 = ctx.mkEnumSort(symbols.Type0, *symbols.type0SymbolsArray)
    val Type0Exprs = symbols.type0Symbols.map { (type, sym) ->
      Pair(type, ctx.mkApp(Type0.getConstDecl(symbols.type0SymbolsArray.indexOf(sym))))
    }.toMap()

    // (define-sort Type () (Array Type0 Bool))
    val Type = ctx.mkArraySort(Type0, Bool)

    val Bottom = ctx.mkConst(symbols.Bottom, Type)
    val Unknown = ctx.mkConst(symbols.Unknown, Type)
    // val Object = ctx.mkConst(symbols.Object, Type)

    val bottomArray = ctx.mkConstArray(Type0, False)
    val unknownArray = ctx.mkConstArray(Type0, True)

    /*
    (define-fun subtype ((a Type) (b Type)) Bool
      (forall ((t Type0)) (=> (select a t) (select b t)))
    )
    */
    /*val subtype = ctx.mkRecFuncDecl(symbols.subtype, arrayOf(Type, Type), Bool) { _, args ->
      ctx.mkForall(arrayOf(Type0)) { forAllArgs ->
        ctx.mkImplies(
          ctx.mkSelect(args[0] as ArrayExpr, forAllArgs[0]) as BoolExpr,
          ctx.mkSelect(args[1] as ArrayExpr, forAllArgs[0]) as BoolExpr
        )
      }
    }*/

    val subtypeOptimized = ctx.mkRecFuncDecl(symbols.subtype, arrayOf(Type, Type), Bool) { _, args ->
      ctx.mkAnd(*Type0Exprs.map { (_, expr) ->
        ctx.mkImplies(
          ctx.mkSelect(args[0] as ArrayExpr, expr) as BoolExpr,
          ctx.mkSelect(args[1] as ArrayExpr, expr) as BoolExpr
        )
      }.toTypedArray())
    }
  }

  fun mkSubtype(a: Expr, b: Expr) = ctx.mkApp(setup.subtypeOptimized, a, b) as BoolExpr

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

  private val typeToExpr = mutableMapOf<MungoType, Expr>()
  fun typeToExpr(type: MungoType): Expr = typeToExpr.computeIfAbsent(type) {
    when (it) {
      is MungoUnionType -> {
        var arr = setup.bottomArray
        for (t in it.types) {
          arr = ctx.mkStore(arr, typeToExpr(t), setup.True)
        }
        arr
      }
      is MungoStateType -> setup.Type0Exprs[it]
      is MungoMovedType -> setup.Type0Exprs[it]
      is MungoPrimitiveType -> setup.Type0Exprs[it]
      is MungoNullType -> setup.Type0Exprs[it]
      is MungoEndedType -> setup.Type0Exprs[it]
      is MungoNoProtocolType -> setup.Type0Exprs[it]
      is MungoObjectType -> null // TODO
      is MungoUnknownType -> setup.unknownArray
      is MungoBottomType -> setup.bottomArray
    } ?: error("Failed to convert $it in a Z3 expression")
  }

  private lateinit var solver: Solver

  fun start(): ConstraintsSetup {
    solver = ctx.mkSolver()
    solver.add(ctx.mkEq(setup.Bottom, setup.bottomArray))
    solver.add(ctx.mkEq(setup.Unknown, setup.unknownArray))
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

fun main(args: Array<String>) {
  ConstraintsSetup(setOf(
    MungoNoProtocolType.SINGLETON,
    MungoEndedType.SINGLETON,
    MungoNullType.SINGLETON,
    MungoPrimitiveType.SINGLETON,
    MungoMovedType.SINGLETON
  )).start()
}
