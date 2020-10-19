package org.checkerframework.checker.mungo.assertions

import com.microsoft.z3.*
import org.checkerframework.checker.mungo.typecheck.*

// Z3 Tutorial: http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.225.8231&rep=rep1&type=pdf
// Z3 Guide and Playground: https://rise4fun.com/z3/tutorial/guide
// Z3 Java Api: https://z3prover.github.io/api/html/namespacecom_1_1microsoft_1_1z3.html

class ConstraintsSetup(private val singletonTypes: Set<MungoType>) {

  private val ctx = Z3Context()
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

    /*
    (define-fun subtype ((a Type) (b Type)) Bool
      (forall ((t Type0)) (=> (select a t) (select b t)))
    )
    */
    val subtype = ctx.mkRecFuncDecl(symbols.subtype, arrayOf(Type, Type), Bool) { _, args ->
      ctx.mkForall(arrayOf(Type0)) { forAllArgs ->
        ctx.mkImplies(
          ctx.mkSelect(args[0] as ArrayExpr, forAllArgs[0]) as BoolExpr,
          ctx.mkSelect(args[1] as ArrayExpr, forAllArgs[0]) as BoolExpr
        )
      }
    }
  }

  fun typeToExpr(type: MungoType) = setup.Type0Exprs[type] ?: error("Missing $type")

  fun makeUnion(types: Set<MungoType>): ArrayExpr {
    var arr = setup.bottomArray
    for (type in types) {
      arr = ctx.mkStore(arr, typeToExpr(type), setup.True)
    }
    return arr
  }

  fun start() {
    val solver = ctx.mkSolver()
    solver.add(ctx.mkEq(setup.Bottom, setup.bottomArray))
    solver.add(ctx.mkEq(setup.Unknown, ctx.mkConstArray(setup.Type0, setup.True)))
    // solver.add(ctx.mkEq(setup.Object, setup.makeUnion(arrayOf(symbols.NoProtocol0, symbols.Ended0))))

    val asserts = mutableListOf<BoolExpr>()
    for (assert in asserts) {
      solver.add(assert)
    }

    val result = solver.check()

    val check = when (result) {
      Status.SATISFIABLE -> true
      Status.UNKNOWN -> false
      Status.UNSATISFIABLE -> false
      else -> false
    }

    val model = solver.model

    println(result)
    println(model)
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
