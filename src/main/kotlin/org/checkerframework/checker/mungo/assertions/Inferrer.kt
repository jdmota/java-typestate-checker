package org.checkerframework.checker.mungo.assertions

import com.sun.source.tree.ClassTree
import com.sun.source.tree.CompilationUnitTree
import com.sun.source.tree.VariableTree
import com.sun.tools.javac.code.Type
import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.abstract_analysis.*
import org.checkerframework.checker.mungo.analysis.FieldAccess
import org.checkerframework.checker.mungo.analysis.Reference
import org.checkerframework.dataflow.cfg.ControlFlowGraph
import org.checkerframework.dataflow.cfg.node.ImplicitThisLiteralNode
import org.checkerframework.dataflow.cfg.node.Node
import org.checkerframework.framework.type.AnnotatedTypeMirror
import org.checkerframework.javacutil.TreeUtils
import org.checkerframework.org.plumelib.util.WeakIdentityHashMap
import javax.lang.model.type.TypeMirror

/*class AccessLocation(val ref: Reference, val isZero: Boolean) {
  override fun equals(other: Any?): Boolean {
    if (other !is AccessLocation) return false
    return other.ref == ref && other.isZero == isZero
  }

  override fun hashCode(): Int {
    var result = ref.hashCode()
    result = 31 * result + isZero.hashCode()
    return result
  }

  override fun toString(): String {
    return if (isZero) "$ref.0" else "$ref"
  }
}*/

class AnalyzerResult(
  private val inferrer: Inferrer,
  private val thenStore: Store,
  private val elseStore: Store
) : AbstractAnalyzerResult<Store, MutableStore>() {

  private val regularStore = inferrer.storeUtils.merge(thenStore, elseStore)

  constructor(inferrer: Inferrer, thenStore: MutableStore, elseStore: MutableStore) : this(inferrer, thenStore.toImmutable(), elseStore.toImmutable())
  constructor(inferrer: Inferrer, result: MutableAnalyzerResult) : this(inferrer, result.getThen().toImmutable(), result.getElse().toImmutable())

  override fun getThen(): Store = thenStore
  override fun getElse(): Store = elseStore
  override fun getRegular(): Store = regularStore
  override fun isRegular(): Boolean = thenStore === elseStore

  override fun getExceptionalStore(cause: Any): Store? {
    return null // TODO
  }

  override fun toString(): String {
    if (isRegular()) {
      return "Result{store=$thenStore}"
    }
    return "Result{\nthen=$thenStore,\nelse=$elseStore\n}"
  }
}

class MutableAnalyzerResult(
  private var thenStore: MutableStore,
  private var elseStore: MutableStore
) : AbstractMutableAnalyzerResult<Store, MutableStore, AnalyzerResult>() {
  override fun merge(result: AnalyzerResult) {
    thenStore.merge(result.getThen())
    if (!isRegular() || !result.isRegular()) {
      elseStore.merge(result.getElse())
    }
  }

  override fun mergeThenAndElse() {
    thenStore.merge(elseStore)
    elseStore = thenStore
  }

  override fun getThen(): MutableStore = thenStore
  override fun getElse(): MutableStore = elseStore
  override fun isRegular(): Boolean = thenStore === elseStore

  override fun getExceptionalStore(cause: Any): MutableStore? {
    return null // TODO
  }

  override fun toString(): String {
    if (isRegular()) {
      return "Result{store=$thenStore}"
    }
    return "Result{\nthen=$thenStore,\nelse=$elseStore\n}"
  }
}

class MutableAnalyzerResultWithValue(
  private var value: StoreInfo,
  private var thenStore: MutableStore,
  private var elseStore: MutableStore
) : AbstractMutableAnalyzerResultWithValue<StoreInfo, Store, MutableStore, AnalyzerResult>() {
  override fun merge(result: AnalyzerResult) {
    thenStore.merge(result.getThen())
    if (!isRegular() || !result.isRegular()) {
      elseStore.merge(result.getElse())
    }
  }

  override fun mergeThenAndElse() {
    thenStore.merge(elseStore)
    elseStore = thenStore
  }

  override fun getThen(): MutableStore = thenStore
  override fun getElse(): MutableStore = elseStore
  override fun isRegular(): Boolean = thenStore === elseStore

  override fun getExceptionalStore(cause: Any): MutableStore? {
    return null // TODO
  }

  override fun toString(): String {
    if (isRegular()) {
      return "Result{value=$value, store=$thenStore}"
    }
    return "Result{value=$value,\nthen=$thenStore,\nelse=$elseStore\n}"
  }

  override fun getValue() = value
  override fun setValue(v: StoreInfo) {
    value = v
  }
}

class SymbolicFraction(private val inferrer: Inferrer) {
  fun intersect(other: SymbolicFraction): SymbolicFraction {
    return TODO()
  }

  fun leastUpperBound(other: SymbolicFraction): SymbolicFraction {
    inferrer.constraints.implies(other, this)
    // TODO
    return this
  }
}

class SymbolicType(private val inferrer: Inferrer) {
  fun intersect(other: SymbolicType): SymbolicType {
    return TODO()
  }

  fun leastUpperBound(other: SymbolicType): SymbolicType {
    return TODO()
  }
}

class StoreInfo(
  val inferrer: Inferrer,
  val fraction: SymbolicFraction,
  val mungoType: SymbolicType,
  val type: AnnotatedTypeMirror,
  // val packed: Boolean = false,
  // val packingFraction: SymbolicFraction,
) : AbstractStoreInfo() {

  constructor(prevInfo: StoreInfo, newFraction: SymbolicFraction, newType: SymbolicType) : this(prevInfo.inferrer, newFraction, newType, prevInfo.type)

  val underlyingType: TypeMirror = type.underlyingType

  override fun equals(other: Any?): Boolean {
    if (this === other) return true
    if (other !is StoreInfo) return false
    if (fraction != other.fraction) return false
    if (mungoType != other.mungoType) return false
    return inferrer.utils.isSameType(underlyingType, other.underlyingType)
    // TODO infinite loop? return EQUALITY_COMPARER.visit(type, other.type, analyzer)
  }

  override fun hashCode(): Int {
    var result = fraction.hashCode()
    result = 31 * result + mungoType.hashCode()
    return result
  }

  override fun toString(): String {
    return "StoreInfo{$fraction, $mungoType, $type}"
  }
}

class Store(
  private val inferrer: Inferrer,
  private val map: Map<Reference, StoreInfo> = emptyMap(),
  private val equalities: EqualityTracker = EqualityTracker()
) : AbstractStore<Store, MutableStore>() {

  operator fun contains(ref: Reference) = map.contains(ref)
  operator fun get(ref: Reference): StoreInfo? = map[ref]
  operator fun iterator(): Iterator<Map.Entry<Reference, StoreInfo>> = map.iterator()

  override fun equals(other: Any?): Boolean {
    if (this === other) return true
    return other is Store && map == other.map // TODO && equalities == other.equalities
  }

  override fun hashCode(): Int {
    return map.hashCode()
  }

  override fun toString(): String {
    val accessesStr = map.map { (l, i) -> "acc($l,${i.fraction})" }.joinToString(" && ")
    val typeofsStr = map.map { (l, i) -> "typeof($l,${i.type})" }.joinToString(" && ")
    return "$accessesStr && $typeofsStr"
  }

  override fun toMutable(): MutableStore {
    return MutableStore(inferrer, map.toMutableMap(), equalities.toMutable())
  }

  override fun toImmutable(): Store {
    return this
  }
}

class MutableStore(
  private val inferrer: Inferrer,
  private val map: MutableMap<Reference, StoreInfo> = mutableMapOf(),
  private val equalities: MutableEqualityTracker = MutableEqualityTracker()
) : AbstractMutableStore<Store, MutableStore>() {

  operator fun contains(ref: Reference) = map.contains(ref)
  operator fun get(ref: Reference): StoreInfo? = map[ref]
  operator fun iterator(): Iterator<Map.Entry<Reference, StoreInfo>> = map.iterator()

  operator fun set(ref: Reference, info: StoreInfo) {
    map[ref] = info
  }

  override fun equals(other: Any?): Boolean {
    if (this === other) return true
    return other is MutableStore && map == other.map // TODO && equalities == other.equalities
  }

  override fun hashCode(): Int {
    return map.hashCode()
  }

  override fun toString(): String {
    val accessesStr = map.map { (l, i) -> "acc($l,${i.fraction})" }.joinToString(" && ")
    val typeofsStr = map.map { (l, i) -> "typeof($l,${i.type})" }.joinToString(" && ")
    return "$accessesStr && $typeofsStr"
  }

  override fun toMutable(): MutableStore {
    return MutableStore(inferrer, map.toMutableMap(), equalities.toMutable())
  }

  override fun toImmutable(): Store {
    return Store(inferrer, map.toMap(), equalities.toImmutable())
  }

  fun merge(ref: Reference, info: StoreInfo) {
    map.compute(ref) { _, curr -> if (curr == null) info else inferrer.storeInfoUtils.merge(curr, info) }
  }

  override fun merge(other: Store) {
    for ((ref, info) in other) {
      merge(ref, info)
    }
  }

  override fun mergeFields(other: Store) {
    for ((ref, info) in other) {
      if (ref.isThisField()) {
        merge(ref, info)
      }
    }
  }

  override fun merge(other: MutableStore) {
    for ((ref, info) in other) {
      merge(ref, info)
    }
  }

  override fun mergeFields(other: MutableStore) {
    for ((ref, info) in other) {
      if (ref.isThisField()) {
        merge(ref, info)
      }
    }
  }

  fun intersect(ref: Reference, info: StoreInfo) {
    map.compute(ref) { _, curr -> if (curr == null) info else inferrer.storeInfoUtils.intersect(curr, info) }
  }

  fun remove(ref: Reference): StoreInfo? {
    return map.remove(ref)
  }

  override fun toBottom(): MutableStore {
    for ((key, value) in map) {
      val newInfo = StoreInfo(value, SymbolicFraction(inferrer), SymbolicType(inferrer))
      inferrer.constraints.one(newInfo.fraction)
      inferrer.constraints.bottom(newInfo.mungoType)
      map[key] = newInfo
    }
    return this
  }

  override fun invalidate(analyzer: AbstractAnalyzerBase): MutableStore {
    for ((key, value) in map) {
      map[key] = StoreInfo(value, SymbolicFraction(inferrer), SymbolicType(inferrer))
    }
    return this
  }

  override fun invalidateFields(analyzer: AbstractAnalyzerBase): MutableStore {
    for ((key, value) in map) {
      if (key.isThisField()) {
        map[key] = StoreInfo(value, SymbolicFraction(inferrer), SymbolicType(inferrer))
      }
    }
    return this
  }

  override fun invalidatePublicFields(analyzer: AbstractAnalyzerBase): MutableStore {
    for ((key, value) in map) {
      if (key.isThisField() && key is FieldAccess && key.isNonPrivate) {
        map[key] = StoreInfo(value, SymbolicFraction(inferrer), SymbolicType(inferrer))
      }
    }
    return this
  }
}

class StoreUtils(private val inferrer: Inferrer) : AbstractStoreUtils<Store, MutableStore>() {

  private val empty = Store(inferrer, emptyMap())

  override fun emptyStore(): Store {
    return empty
  }

  override fun mutableEmptyStore(): MutableStore {
    return MutableStore(inferrer)
  }
}

class StoreInfoUtils : AbstractStoreInfoUtils<StoreInfo>() {
  override fun merge(a: StoreInfo, b: StoreInfo): StoreInfo {
    val inferrer = a.inferrer
    // TODO val type = inferrer.utils.leastUpperBound(a.underlyingType, b.underlyingType)
    val mostSpecific = inferrer.utils.mostSpecific(a.underlyingType, b.underlyingType)
    return StoreInfo(
      inferrer,
      a.fraction.leastUpperBound(b.fraction),
      a.mungoType.leastUpperBound(b.mungoType),
      if (mostSpecific === a.underlyingType) b.type else a.type
      // TODO this breaks the tests: inferrer.utils.createType(type, a.type.isDeclaration)
    )
  }

  override fun intersect(a: StoreInfo, b: StoreInfo): StoreInfo {
    val inferrer = a.inferrer
    val mostSpecific = inferrer.utils.mostSpecific(a.underlyingType, b.underlyingType)
    return StoreInfo(
      inferrer,
      a.fraction.intersect(b.fraction),
      a.mungoType.intersect(b.mungoType),
      if (mostSpecific === a.underlyingType) a.type else b.type
    )
  }
}

class AnalyzerResultsUtils(private val inferrer: Inferrer) : AbstractAnalyzerResultUtils<StoreInfo, Store, MutableStore, AnalyzerResult, MutableAnalyzerResult, MutableAnalyzerResultWithValue>(inferrer.storeUtils) {
  override fun createAnalyzerResult(thenStore: Store, elseStore: Store): AnalyzerResult {
    return AnalyzerResult(inferrer, thenStore, elseStore)
  }

  override fun createAnalyzerResult(thenStore: MutableStore, elseStore: MutableStore): AnalyzerResult {
    return AnalyzerResult(inferrer, thenStore, elseStore)
  }

  override fun createMutableAnalyzerResult(thenStore: MutableStore, elseStore: MutableStore): MutableAnalyzerResult {
    return MutableAnalyzerResult(thenStore, elseStore)
  }

  override fun createMutableAnalyzerResultWithValue(value: StoreInfo, result: AnalyzerResult): MutableAnalyzerResultWithValue {
    return MutableAnalyzerResultWithValue(value, result.getThen().toMutable(), result.getElse().toMutable())
  }
}

class Inferrer(checker: MungoChecker) : AbstractAnalyzer<
  AnalyzerResult,
  MutableAnalyzerResult,
  MutableAnalyzerResultWithValue,
  StoreInfo,
  Store,
  MutableStore,
  StoreUtils,
  StoreInfoUtils,
  AnalyzerResultsUtils
  >(checker) {
  override fun setup() {
    storeUtils = StoreUtils(this)
    storeInfoUtils = StoreInfoUtils()
    analyzerResultsUtils = AnalyzerResultsUtils(this)
  }

  override fun setRoot(root: CompilationUnitTree) {
    super.setRoot(root)
  }

  private val nodeToInfo = WeakIdentityHashMap<Node, StoreInfo>()

  override fun getInitialInfo(node: Node): StoreInfo {
    return nodeToInfo.computeIfAbsent(node) {
      if (node is ImplicitThisLiteralNode) {
        val annotatedType = utils.factory.createType(node.type, false)
        StoreInfo(
          this,
          SymbolicFraction(this),
          SymbolicType(this),
          annotatedType
        )
      } else {
        val tree = node.tree
        if (tree != null && TreeUtils.canHaveTypeAnnotation(tree)) {
          StoreInfo(this, SymbolicFraction(this), SymbolicType(this), utils.factory.getAnnotatedType(tree))
        } else {
          StoreInfo(this, SymbolicFraction(this), SymbolicType(this), utils.factory.createType(Type.noType, false))
        }
      }
    }
  }

  override fun handleUninitializedField(store: MutableStore, field: VariableTree, ct: ClassTree) {
    TODO("Not yet implemented")
  }

  override fun initialStore(capturedStore: Store, cfg: ControlFlowGraph): Store {
    TODO("Not yet implemented")
  }

  override fun visit(node: Node, mutableResult: MutableAnalyzerResultWithValue) {
    TODO("Not yet implemented")
  }

  val constraints = Constraints()
}
