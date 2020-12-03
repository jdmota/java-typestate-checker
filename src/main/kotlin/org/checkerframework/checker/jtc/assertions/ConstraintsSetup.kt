package org.checkerframework.checker.jtc.assertions

import com.sun.tools.javac.code.Symbol as JavacSymbol
import com.microsoft.z3.*
import org.checkerframework.checker.jtc.analysis.Reference
import org.checkerframework.checker.jtc.typecheck.*

// Z3 Tutorial: http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.225.8231&rep=rep1&type=pdf
// Z3 Guide and Playground: https://rise4fun.com/z3/tutorial/guide
// Z3 Java Api: https://z3prover.github.io/api/html/namespacecom_1_1microsoft_1_1z3.html

class ConstraintsSetup(usedTypes: Set<JTCType>) {

  val ctx = Z3Context()

  private val typesWithUnions = run {
    val allTypes = mutableListOf<JTCType>()
    usedTypes.forEach { a ->
      usedTypes.forEach { b ->
        // TODO do not create more unions for now...
        // if (a !== b) allTypes.add(JTCUnionType.create(listOf(a, b)))
      }
    }
    allTypes.addAll(usedTypes)
    allTypes.toSet()
  }

  private val labelToType = mutableMapOf<String, JTCType>()

  fun labelToType(label: String) = labelToType[label] ?: error("No type for label $label")

  private fun typeToLabel(type: JTCType): String {
    val label = when (type) {
      is JTCUnionType -> "TU_${type.types.joinToString("_") { typeToLabel(it) }}"
      is JTCStateType -> "TS${type.state.id}"
      is JTCMovedType -> "TMoved"
      is JTCPrimitiveType -> "TPrim"
      is JTCNullType -> "TNull"
      is JTCEndedType -> "TEnded"
      is JTCNoProtocolType -> "TNo"
      is JTCObjectType -> "TObj"
      is JTCUnknownType -> "TUnknown"
      is JTCBottomType -> "TBottom"
    }
    labelToType[label] = type
    return label
  }

  private fun typeToSymbol(type: JTCType): Symbol {
    return ctx.mkSymbol(typeToLabel(type))
  }

  private val setup = object {
    val Bool = ctx.boolSort
    val Real = ctx.realSort

    val typeSymbols = typesWithUnions.map { Pair(it, typeToSymbol(it)) }.toMap()
    val typesArray = typeSymbols.values.toTypedArray()

    val Type = ctx.mkEnumSort(ctx.mkSymbol("Type"), *typesArray)
    val TypeExprs = typeSymbols.map { (type, sym) ->
      Pair(type, ctx.mkApp(Type.getConstDecl(typesArray.indexOf(sym))))
    }.toMap()

    val UnknownExpr = TypeExprs[JTCUnknownType.SINGLETON] ?: error("")

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

    fun closestUpperBound(type: JTCType) = when {
      TypeExprs.contains(type) -> type
      type.isSubtype(JTCObjectType.SINGLETON) -> JTCObjectType.SINGLETON
      else -> JTCUnknownType.SINGLETON
    }

    val union = ctx.mkRecFuncDecl(ctx.mkSymbol("union"), arrayOf(Type, Type), Type) { _, args ->
      val a = args[0]
      val b = args[1]

      fun helper2(typeA: JTCType, it: Iterator<Map.Entry<JTCType, Expr>>): Expr {
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

      fun helper1(it: Iterator<Map.Entry<JTCType, Expr>>): Expr {
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

      fun helper2(typeA: JTCType, it: Iterator<Map.Entry<JTCType, Expr>>): Expr {
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

      fun helper1(it: Iterator<Map.Entry<JTCType, Expr>>): Expr {
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

  private var transitionUuid = 1L
  private val methodToTransitionFunc = mutableMapOf<JavacSymbol.MethodSymbol, FuncDecl>()
  fun methodToTransitionFunc(method: JavacSymbol.MethodSymbol, map: Map<JTCType, JTCType>): FuncDecl {
    return methodToTransitionFunc.computeIfAbsent(method) {
      val key = "trans${transitionUuid++}"
      ctx.mkRecFuncDecl(ctx.mkSymbol(key), arrayOf(setup.Type), setup.Type) { _, args ->
        val a = args[0]

        fun helper(it: Iterator<Map.Entry<JTCType, JTCType>>): Expr {
          if (it.hasNext()) {
            val (initial, destination) = it.next()
            return ctx.mkITE(
              ctx.mkEq(a, setup.TypeExprs[initial]!!),
              setup.TypeExprs[destination]!!,
              helper(it)
            )
          }
          return setup.UnknownExpr
        }

        val code = helper(map.iterator())
        // println(code)
        code
      }
    }
  }

  private var equalsUuid = 1L
  private val equalsToExpr = mutableMapOf<Triple<SymbolicAssertion, Reference, Reference>, BoolExpr>()
  fun mkEquals(assertion: SymbolicAssertion, a: Reference, b: Reference): BoolExpr =
    equalsToExpr.computeIfAbsent(Triple(assertion, a, b)) {
      val key = "eq${equalsUuid++}"
      ctx.mkConst(key, setup.Bool) as BoolExpr
    }

  fun mkSubtype(a: Expr, b: Expr) = ctx.mkApp(setup.subtype, a, b) as BoolExpr

  fun mkMin(a: ArithExpr, b: ArithExpr) =
    if (a === b) {
      a
    } else {
      ctx.mkApp(setup.min, a, b) as ArithExpr
    }

  fun mkUnion(a: Expr, b: Expr): Expr =
    if (a === b) {
      a
    } else {
      ctx.mkApp(setup.union, a, b)
    }

  fun mkIntersection(a: Expr, b: Expr): Expr =
    if (a === b) {
      a
    } else {
      ctx.mkApp(setup.intersection, a, b)
    }

  val keyToSomething = mutableMapOf<String, Any>()

  private val fractionKeyToExpr = mutableMapOf<String, ArithExpr>()
  fun mkFraction(key: String): ArithExpr {
    return fractionKeyToExpr.computeIfAbsent(key) {
      val c = ctx.mkConst(it, setup.Real) as ArithExpr
      keyToSomething[key] = c
      // 0 <= c <= 1
      addAssert(ctx.mkAnd(ctx.mkGe(c, ctx.mkReal(0)), ctx.mkLe(c, ctx.mkReal(1))))
      c
    }
  }

  private val typeKeyToExpr = mutableMapOf<String, Expr>()
  fun mkType(key: String): Expr {
    return typeKeyToExpr.computeIfAbsent(key) {
      val t = ctx.mkConst(it, setup.Type)
      keyToSomething[key] = t
      t
    }
  }

  fun mkType(t: JTCType): Expr = setup.TypeExprs[t] ?: error("No expression for $t")

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

  fun solve(): MiniInferenceResult {
    val result = solver.check()
    val hasModel = result == Status.SATISFIABLE
    if (hasModel) {
      return MiniSolution(solver.model)
    }
    return if (result == Status.UNSATISFIABLE) {
      MiniNoSolution(solver.unsatCore)
    } else {
      MiniUnknownSolution(solver.reasonUnknown)
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
        mkSubtype(args[0], mkType(JTCUnknownType.SINGLETON))
      })

      // Single top
      // (assert (exists ((t Type)) (and (= t Unknown) (forall ((x Type)) (subtype x t)))))
      addAssert(ctx.mkExists(arrayOf(setup.Type)) { args ->
        ctx.mkAnd(
          ctx.mkEq(args[0], mkType(JTCUnknownType.SINGLETON)),
          ctx.mkForall(arrayOf(setup.Type)) { innerArgs ->
            mkSubtype(innerArgs[0], args[0])
          }
        )
      })

      // Bottom subtype of all
      // (assert (forall ((t Type)) (subtype Bottom t)))
      addAssert(ctx.mkForall(arrayOf(setup.Type)) { args ->
        mkSubtype(mkType(JTCBottomType.SINGLETON), args[0])
      })

      // Single bottom
      // (assert (exists ((t Type)) (and (= t Bottom) (forall ((x Type)) (subtype t x)))))
      addAssert(ctx.mkExists(arrayOf(setup.Type)) { args ->
        ctx.mkAnd(
          ctx.mkEq(args[0], mkType(JTCBottomType.SINGLETON)),
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
