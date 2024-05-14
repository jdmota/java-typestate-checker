package jatyc.core

import jatyc.core.cfg.*
import jatyc.utils.JTCUtils

sealed class Reference(val javaType: JavaType) {
  companion object {
    fun make(code: LeftHS): Reference {
      return when (code) {
        is IdLHS -> IdReference(code.name, code.uuid, code.javaType)
        is SelectLHS -> SelectReference(make(code.obj), code.id, code.uuid, code.javaType)
      }
    }

    fun make(code: CodeExpr): Reference {
      return when (code) {
        is Id -> IdReference(code.name, code.uuid, code.javaType)
        is Select -> SelectReference(make(code.expr), code.id, code.uuid, code.javaType)
        else -> {
          val javaType = code.javaType2 ?: JTCUtils.error("no javaType in $code")
          CodeExprReference(code, javaType)
        }
      }
    }

    fun make(thisRef: Reference, field: FieldDeclaration) = SelectReference(thisRef, field.id.name, field.id.uuid, field.javaType)

    fun returnRef(javaType: JavaType) = IdReference("#ret", 0, javaType)

    fun makeFromLHS(assign: Assign) = make(assign.left)
    fun makeFromLHS(assign: ParamAssign) = ParamInReference(assign.call, assign.idx)

    fun makeThis(func: FuncDeclaration) = func.parameters.firstOrNull()?.let { if (it.isThis) make(it.id) else null }
  }

  abstract fun format(): String

  fun isField(): Boolean {
    return this is SelectReference
  }

  fun isFieldOf(thisRef: Reference?): Boolean {
    return this is SelectReference && parent == thisRef
  }

  fun isFieldOf(thisRef: Reference?, id: IdLHS): Boolean {
    return this is SelectReference && parent == thisRef && this.id == id.name && this.uuid == id.uuid
  }

  fun isSwitchVar(): Boolean {
    return this is IdReference && name.startsWith("switch#")
  }

  fun fixThis(from: Reference, to: Reference): Reference {
    return when (this) {
      is IdReference -> if (this == from) to else this
      is SelectReference -> SelectReference(parent.fixThis(from, to), id, uuid, javaType)
      is ParamInReference -> this
      is CodeExprReference -> this
    }
  }
}

class SelectReference(val parent: Reference, val id: String, val uuid: Long, javaType: JavaType) : Reference(javaType) {
  override fun equals(other: Any?): Boolean {
    return other is SelectReference && id == other.id && uuid == other.uuid && parent == other.parent
  }

  override fun hashCode(): Int {
    var result = parent.hashCode()
    result = 31 * result + id.hashCode()
    result = 31 * result + uuid.hashCode()
    return result
  }

  override fun toString(): String {
    return "SelectRef{$parent.$id[$uuid]}"
  }

  override fun format(): String {
    return "${parent.format()}.$id"
  }
}

sealed class RootReference(javaType: JavaType) : Reference(javaType)

class IdReference(val name: String, val uuid: Long, javaType: JavaType) : RootReference(javaType) {
  override fun equals(other: Any?): Boolean {
    return other is IdReference && name == other.name && uuid == other.uuid
  }

  override fun hashCode(): Int {
    var result = name.hashCode()
    result = 31 * result + uuid.hashCode()
    return result
  }

  override fun toString(): String {
    return "IdRef{$name, $uuid}"
  }

  override fun format(): String {
    return name
  }
}

class ParamInReference(val call: MethodCall, val idx: Int) : RootReference(call.methodExpr.parameters[idx].id.javaType) {
  override fun equals(other: Any?): Boolean {
    return other is ParamInReference && idx == other.idx && call == other.call
  }

  override fun hashCode(): Int {
    return idx.hashCode()
  }

  override fun toString(): String {
    return "ParamInRef{$idx}"
  }

  override fun format(): String {
    return "#param$idx"
  }
}

class CodeExprReference(val code: CodeExpr, javaType: JavaType) : RootReference(javaType) {
  override fun equals(other: Any?): Boolean {
    return other is CodeExprReference && code === other.code
  }

  override fun hashCode(): Int {
    return code.hashCode()
  }

  override fun toString(): String {
    return "CodeRef{$code}"
  }

  override fun format(): String {
    return code.format("")
  }
}
