package org.checkerframework.checker.mungo.assertions

import com.microsoft.z3.*
import org.checkerframework.dataflow.cfg.node.Node

// Z3 Tutorial: http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.225.8231&rep=rep1&type=pdf
// Z3 Guide and Playground: https://rise4fun.com/z3/tutorial/guide
// Z3 Java Api: https://z3prover.github.io/api/html/namespacecom_1_1microsoft_1_1z3.html

// Definitions:
// - Sort: it is like a type
// - Model: gives an interpretation that makes all the formulas true

class Inference {

  private val constraintsInference = ConstraintsInference()
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

  private fun setup(): List<BoolExpr> {
    val Bool = ctx.boolSort
    // (declare-datatypes () ((Type0 Unknown Object Ended NoProtocol Null Primitive Moved Bottom)))
    val Type0 = ctx.mkEnumSort(symbols.Type0, *symbols.type0Symbols)
    val Type0Exprs = Type0.consts.mapIndexed { index, expr -> Pair(symbols.type0Symbols[index], expr) }.toMap()
    // (declare-fun subtype0 (Type0 Type0) Bool)
    val subtype0 = ctx.mkFuncDecl(symbols.subtype0, arrayOf(Type0, Type0), Bool)
    // (define-sort Type () (List Type0))
    val Type = ctx.mkListSort(symbols.Type, Type0)
    /*
    (define-fun-rec subtype$ ((a Type0) (b Type)) Bool
      (ite (= b nil)
        (= a Bottom)
        (ite (subtype0 a (head b)) true (subtype$ a (tail b)) )
      )
    )
    */
    val subtypeHelper = ctx.mkRecFuncDecl(symbols.subtypeHelper, arrayOf(Type0, Type), Bool)
    val subtypeHelperA = ctx.mkBound(0, Type0)
    val subtypeHelperB = ctx.mkBound(1, Type)
    ctx.addRecDef(subtypeHelper, arrayOf(subtypeHelperA, subtypeHelperB), { a: Expr, b: Expr ->
      ctx.mkITE(
        ctx.mkEq(b, Type.nil),
        ctx.mkEq(a, Type0Exprs[symbols.Bottom]),
        ctx.mkITE(
          ctx.mkApp(subtype0, a, ctx.mkApp(Type.headDecl, b)) as BoolExpr,
          ctx.mkTrue(),
          ctx.mkApp(subtypeHelper, a, ctx.mkApp(Type.tailDecl, b)),
        )
      )
    }(subtypeHelperA, subtypeHelperB))
    /*
    (define-fun-rec subtype ((a Type) (b Type)) Bool
      (ite (= a nil)
        true
        (and (subtype$ (head a) b) (subtype (tail a) b))
      )
    )
    */
    val subtype = ctx.mkRecFuncDecl(symbols.subtype, arrayOf(Type, Type), Bool)
    val subtypeA = ctx.mkBound(0, Type)
    val subtypeB = ctx.mkBound(1, Type)
    ctx.addRecDef(subtype, arrayOf(subtypeA, subtypeB), { a: Expr, b: Expr ->
      ctx.mkITE(
        ctx.mkEq(a, Type.nil),
        ctx.mkTrue(),
        ctx.mkAnd(
          ctx.mkApp(subtypeHelper, ctx.mkApp(Type.headDecl, a), b) as BoolExpr,
          ctx.mkApp(subtype, ctx.mkApp(Type.tailDecl, a), b) as BoolExpr,
        )
      )
    }(subtypeA, subtypeB))

    val asserts = mutableListOf<BoolExpr>()

    // (assert (forall ((x Type0)) (subtype0 x x)))
    asserts.add(ctx.mkForall(arrayOf(Type0)) {
      ctx.mkApp(subtype0, it[0], it[0])
    })

    // (assert (forall ((x Type0) (y Type0)) (= (and (subtype0 x y) (subtype0 y x)) (= x y))))
    asserts.add(ctx.mkForall(arrayOf(Type0, Type0)) {
      ctx.mkEq(
        ctx.mkAnd(
          ctx.mkApp(subtype0, it[0], it[1]) as BoolExpr,
          ctx.mkApp(subtype0, it[1], it[0]) as BoolExpr
        ),
        ctx.mkEq(it[0], it[1])
      )
    })

    // (assert (forall ((x Type0) (y Type0) (z Type0)) (=> (and (subtype0 x y) (subtype0 y z)) (subtype0 x z))))
    asserts.add(ctx.mkForall(arrayOf(Type0, Type0, Type0)) {
      ctx.mkImplies(
        ctx.mkAnd(
          ctx.mkApp(subtype0, it[0], it[1]) as BoolExpr,
          ctx.mkApp(subtype0, it[1], it[2]) as BoolExpr
        ),
        ctx.mkApp(subtype0, it[0], it[2]) as BoolExpr
      )
    })

    // (assert (forall ((t Type0)) (subtype0 t Unknown)))
    asserts.add(ctx.mkForall(arrayOf(Type0)) {
      ctx.mkApp(subtype0, it[0], Type0Exprs[symbols.Unknown])
    })

    // (assert (forall ((t Type0)) (subtype0 Bottom t)))
    asserts.add(ctx.mkForall(arrayOf(Type0)) {
      ctx.mkApp(subtype0, Type0Exprs[symbols.Bottom], it[0])
    })

    fun subtypeRelation(a: Symbol, b: Symbol) = ctx.mkApp(subtype0, Type0Exprs[a], Type0Exprs[b]) as BoolExpr

    // (assert (subtype0 Ended Object))
    asserts.add(subtypeRelation(symbols.Ended, symbols.Object))
    // (assert (subtype0 NoProtocol Object))
    asserts.add(subtypeRelation(symbols.NoProtocol, symbols.Object))
    // (assert (not (subtype0 Null Object)))
    asserts.add(ctx.mkNot(subtypeRelation(symbols.Null, symbols.Object)))
    // (assert (not (subtype0 Primitive Object)))
    asserts.add(ctx.mkNot(subtypeRelation(symbols.Primitive, symbols.Object)))
    // (assert (not (subtype0 Moved Object)))
    asserts.add(ctx.mkNot(subtypeRelation(symbols.Moved, symbols.Object)))

    return asserts
  }

  fun start() {
    val asserts = setup()
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

  fun visit(node: Node) {
    node.accept(constraintsInference, null)
  }

}

fun main(args: Array<String>) {
  Inference().start()
}
