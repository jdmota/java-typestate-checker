package org.checkerframework.checker.mungo.assertions

import com.microsoft.z3.*

// Z3 Tutorial: http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.225.8231&rep=rep1&type=pdf
// Z3 Guide and Playground: https://rise4fun.com/z3/tutorial/guide
// Z3 Java Api: https://z3prover.github.io/api/html/namespacecom_1_1microsoft_1_1z3.html

// Definitions:
// - Sort: it is like a type
// - Model: gives an interpretation that makes all the formulas true

open class InferrerBase {

  private val ctx = Z3Context()
  private val symbols = object {
    val Type0 = ctx.mkSymbol("Type0")
    val Type = ctx.mkSymbol("Type")
    val Unknown = ctx.mkSymbol("Unknown")
    val Object = ctx.mkSymbol("Object")
    val Ended = ctx.mkSymbol("Ended")
    val NoProtocol = ctx.mkSymbol("NoProtocol")
    val Null = ctx.mkSymbol("Null")
    val Primitive = ctx.mkSymbol("Primitive")
    val Moved = ctx.mkSymbol("Moved")
    val Bottom = ctx.mkSymbol("Bottom")
    val type0Symbols = arrayOf(Unknown, Object, Ended, NoProtocol, Null, Primitive, Moved, Bottom)
    val subtype0 = ctx.mkSymbol("subtype0")
    val subtypeHelper = ctx.mkSymbol("subtype$")
    val subtype = ctx.mkSymbol("subtype")
  }

  private val setup = object {
    val Bool = ctx.boolSort

    // (declare-datatypes () ((Type0 Unknown Object Ended NoProtocol Null Primitive Moved Bottom)))
    val Type0 = ctx.mkEnumSort(symbols.Type0, *symbols.type0Symbols)
    val Type0Exprs = Type0.consts.mapIndexed { index, expr -> Pair(symbols.type0Symbols[index], expr) }.toMap()

    // (define-sort Type () (List Type0))
    val Type = ctx.mkListSort(symbols.Type, Type0)

    /*
    (define-fun subtype0 ((a Type0) (b Type0)) Bool
      (ite (= a Unknown)
        (= a b)
        (ite (or (= a Object) (= a Null) (= a Primitive) (= a Moved))
          (or (= b Unknown) (= a b))
          (ite (or (= a Ended) (= a NoProtocol))
            (or (= b Unknown) (= b Object) (= a b))
            (ite (= a Bottom) true false)
          )
        )
      )
    )
    */
    val subtype0 = ctx.mkRecFuncDecl(symbols.subtype0, arrayOf(Type0, Type0), Bool) { _, args ->
      val a = args[0]
      val b = args[1]
      ctx.mkITE(
        ctx.mkEq(a, Type0Exprs[symbols.Unknown]),
        ctx.mkEq(a, b),
        ctx.mkITE(
          ctx.mkOr(
            ctx.mkEq(a, Type0Exprs[symbols.Object]),
            ctx.mkEq(a, Type0Exprs[symbols.Null]),
            ctx.mkEq(a, Type0Exprs[symbols.Primitive]),
            ctx.mkEq(a, Type0Exprs[symbols.Moved]),
          ),
          ctx.mkOr(
            ctx.mkEq(b, Type0Exprs[symbols.Unknown]),
            ctx.mkEq(a, b)
          ),
          ctx.mkITE(
            ctx.mkOr(
              ctx.mkEq(a, Type0Exprs[symbols.Ended]),
              ctx.mkEq(a, Type0Exprs[symbols.NoProtocol])
            ),
            ctx.mkOr(
              ctx.mkEq(b, Type0Exprs[symbols.Unknown]),
              ctx.mkEq(b, Type0Exprs[symbols.Object]),
              ctx.mkEq(a, b)
            ),
            ctx.mkITE(
              ctx.mkEq(a, Type0Exprs[symbols.Bottom]),
              ctx.mkTrue(),
              ctx.mkFalse()
            )
          )
        )
      )
    }

    /*
    (define-fun-rec subtype$ ((a Type0) (b Type)) Bool
      (ite (= b nil)
        (= a Bottom)
        (ite (subtype0 a (head b)) true (subtype$ a (tail b)) )
      )
    )
    */
    val subtypeHelper = ctx.mkRecFuncDecl(symbols.subtypeHelper, arrayOf(Type0, Type), Bool) { func, args ->
      val a = args[0]
      val b = args[1]
      ctx.mkITE(
        ctx.mkEq(b, Type.nil),
        ctx.mkEq(a, Type0Exprs[symbols.Bottom]),
        ctx.mkITE(
          ctx.mkApp(subtype0, a, ctx.mkApp(Type.headDecl, b)) as BoolExpr,
          ctx.mkTrue(),
          ctx.mkApp(func, a, ctx.mkApp(Type.tailDecl, b)),
        )
      )
    }

    /*
    (define-fun-rec subtype ((a Type) (b Type)) Bool
      (ite (= a nil)
        true
        (and (subtype$ (head a) b) (subtype (tail a) b))
      )
    )
    */
    val subtype = ctx.mkRecFuncDecl(symbols.subtype, arrayOf(Type, Type), Bool) { func, args ->
      val a = args[0]
      val b = args[1]
      ctx.mkITE(
        ctx.mkEq(a, Type.nil),
        ctx.mkTrue(),
        ctx.mkAnd(
          ctx.mkApp(subtypeHelper, ctx.mkApp(Type.headDecl, a), b) as BoolExpr,
          ctx.mkApp(func, ctx.mkApp(Type.tailDecl, a), b) as BoolExpr,
        )
      )
    }
  }

  fun start() {
    val asserts = mutableListOf<BoolExpr>()
    val solver = ctx.mkSolver()
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

/*fun main(args: Array<String>) {
  Inference().start()
}*/
