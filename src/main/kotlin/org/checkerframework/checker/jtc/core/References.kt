package org.checkerframework.checker.jtc.core

import org.checkerframework.checker.jtc.core.cfg.*

sealed class ReverseRefComponent

class ReverseRefRoot(val root: RootReference) : ReverseRefComponent() {
  override fun equals(other: Any?): Boolean {
    return other is ReverseRefRoot && root == other.root
  }

  override fun hashCode(): Int {
    return root.hashCode()
  }
}

class ReverseRefId(val id: String) : ReverseRefComponent() {
  override fun equals(other: Any?): Boolean {
    return other is ReverseRefId && id == other.id
  }

  override fun hashCode(): Int {
    return id.hashCode()
  }
}

class ReverseRef(val id: ReverseRefComponent, val rest: ReverseRef?) {
  companion object {
    fun make(initialRef: Reference): ReverseRef {
      var rest: ReverseRef? = null
      var ref: Reference? = initialRef
      while (ref != null) {
        when (ref) {
          is SelectReference -> {
            val select = ref
            ref = select.parent
            rest = ReverseRef(ReverseRefId(select.id), rest)
          }
          is RootReference -> {
            rest = ReverseRef(ReverseRefRoot(ref), rest)
            ref = null
          }
        }
      }
      return rest!!
    }
  }
}

sealed class Reference {
  companion object {
    fun make(code: LeftHS): Reference {
      return when (code) {
        is IdLHS -> IdReference(code.name, code.uuid)
        is SelectLHS -> SelectReference(make(code.obj), code.id, code.uuid)
      }
    }

    fun make(code: CodeExpr): Reference {
      return when (code) {
        is Id -> IdReference(code.name, code.uuid)
        is Select -> SelectReference(make(code.expr), code.id, code.uuid)
        else -> CodeExprReference(code)
      }
    }

    fun make(thisRef: Reference, field: FieldDeclaration) = SelectReference(thisRef, field.id.name, field.id.uuid)

    val returnRef = IdReference("#ret", 0)

    fun makeFromLHS(assign: Assign) = make(assign.left)
    fun makeFromLHS(assign: ParamAssign) = ParamInReference(assign.call, assign.idx)

    fun old(assign: Assign) = OldReference(assign)

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
      is SelectReference -> SelectReference(parent.fixThis(from, to), id, uuid)
      is OldReference -> this
      is ParamInReference -> this
      is CodeExprReference -> this
    }
  }
}

class SelectReference(val parent: Reference, val id: String, val uuid: Long) : Reference() {
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

sealed class RootReference : Reference()

class IdReference(val name: String, val uuid: Long) : RootReference() {
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

class ParamInReference(val call: MethodCall, val idx: Int) : RootReference() {
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

class CodeExprReference(val code: CodeExpr) : RootReference() {
  override fun equals(other: Any?): Boolean {
    return other is CodeExprReference && code === other.code
  }

  override fun hashCode(): Int {
    return code.hashCode()
  }

  override fun toString(): String {
    return "CodeRef{$code,${code.cfNode?.uid}}"
  }

  override fun format(): String {
    return code.format("")
  }
}

class OldReference(val assign: Assign) : RootReference() {
  override fun equals(other: Any?): Boolean {
    return other is OldReference && assign === other.assign
  }

  override fun hashCode(): Int {
    return assign.left.hashCode()
  }

  override fun toString(): String {
    return "OldRef{$assign}"
  }

  override fun format(): String {
    return "#old(${assign.format("")})"
  }
}
