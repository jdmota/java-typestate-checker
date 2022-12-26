package jatyc.core.typesystem

import jatyc.core.*
import jatyc.core.cfg.MethodCall
import jatyc.utils.JTCUtils

class TypeInfo private constructor(val javaType: JavaType, val jtcType: JTCType) {
  fun debugIsPrimitive(): Boolean {
    return jtcType is JTCPrimitiveType
  }

  fun debugJavaType(javaType: JavaType) {
    if (this.javaType !== javaType) {
      JTCUtils.printStack()
      error("TypeInfo.javaType: expected ${this.javaType} got $javaType")
    }
  }

  fun isSubtype(other: TypeInfo): Boolean {
    return jtcType.isSubtype(other.jtcType)
  }

  fun isSubtype(other: JTCType): Boolean {
    return jtcType.isSubtype(other)
  }

  fun toShared(): TypeInfo {
    return TypeInfo(javaType, jtcType.toShared())
  }

  fun toUnknown(): TypeInfo {
    return TypeInfo(javaType, JTCUnknownType.SINGLETON)
  }

  fun isUnknown(): Boolean {
    return JTCUnknownType.SINGLETON.isSubtype(jtcType)
  }

  fun toBottom(): TypeInfo {
    return TypeInfo(javaType, JTCBottomType.SINGLETON)
  }

  fun isBottom(): Boolean {
    return jtcType.isSubtype(JTCBottomType.SINGLETON)
  }

  fun isNull(): Boolean {
    return jtcType.isSubtype(JTCNullType.SINGLETON)
  }

  fun isNullable(): Boolean {
    return JTCNullType.SINGLETON.isSubtype(jtcType)
  }

  fun intersect(other: JTCType): TypeInfo {
    return TypeInfo(javaType, jtcType.intersect(other))
  }

  fun cast(javaType: JavaType, doUpcast: Boolean): TypeInfo {
    return TypeInfo(javaType, Subtyping.cast(jtcType, javaType, doUpcast))
  }

  fun isInDroppableStateNotEnd(): Boolean {
    return TypecheckUtils.isInDroppableStateNotEnd(jtcType)
  }

  fun canDrop(): Boolean {
    return TypecheckUtils.canDrop(jtcType)
  }

  fun requiresLinear(ref: Reference): Boolean {
    return TypecheckUtils.requiresLinear(ref, jtcType)
  }

  fun invariant(): TypeInfo {
    return TypeInfo(javaType, TypecheckUtils.invariant(jtcType))
  }

  fun refine(utils: TypecheckUtils, call: MethodCall, predicate: (String) -> Boolean): TypeInfo {
    return TypeInfo(javaType, utils.refine(jtcType, call, predicate))
  }

  fun check(utils: TypecheckUtils, call: MethodCall): Boolean {
    return utils.check(jtcType, call)
  }

  fun refineToNonNull(): TypeInfo {
    return TypeInfo(javaType, TypecheckUtils.refineToNonNull(jtcType))
  }

  fun refineToNull(): TypeInfo {
    return TypeInfo(javaType, TypecheckUtils.refineToNull(jtcType))
  }

  fun format(): String {
    return jtcType.format()
  }

  override fun toString(): String {
    return "TypeInfo{$javaType, $jtcType}"
  }

  companion object {
    fun createUnion(javaType: JavaType, list: List<TypeInfo>): TypeInfo {
      list.forEach { it.debugJavaType(javaType) }
      return TypeInfo(javaType, JTCType.createUnion(list.map { it.jtcType }))
    }

    fun make(javaType: JavaType, jtcType: JTCType): TypeInfo {
      return TypeInfo(javaType, jtcType)
    }

    fun make(prim: JTCPrimitiveType): TypeInfo {
      return make(prim.javaType, prim)
    }

    fun make(type: JTCSharedType): TypeInfo {
      return make(type.javaType, type)
    }
  }
}
