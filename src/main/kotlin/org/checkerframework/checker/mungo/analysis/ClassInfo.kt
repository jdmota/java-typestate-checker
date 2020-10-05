package org.checkerframework.checker.mungo.analysis

import com.sun.source.tree.BlockTree
import com.sun.source.tree.ClassTree
import com.sun.source.tree.MethodTree
import com.sun.source.tree.VariableTree
import org.checkerframework.javacutil.TreeUtils
import javax.lang.model.element.Modifier

fun filterMethods(methods: List<MethodTree>, modifier: Modifier) = methods.filter {
  it.modifiers.flags.contains(modifier)
}

fun filterNotMethods(methods: List<MethodTree>, modifier: Modifier) = methods.filterNot {
  it.modifiers.flags.contains(modifier)
}

fun filterFields(fields: List<VariableTree>, modifier: Modifier) = fields.filter {
  it.modifiers.flags.contains(modifier)
}

fun filterNotFields(fields: List<VariableTree>, modifier: Modifier) = fields.filterNot {
  it.modifiers.flags.contains(modifier)
}

fun filterClasses(classes: List<ClassTree>, modifier: Modifier) = classes.filter {
  it.modifiers.flags.contains(modifier)
}

fun filterNotClasses(classes: List<ClassTree>, modifier: Modifier) = classes.filterNot {
  it.modifiers.flags.contains(modifier)
}

sealed class ClassInfo(
  val static: Boolean,
  val methods: List<MethodTree>,
  val fields: List<VariableTree>,
  val blocks: List<BlockTree>,
  val classes: List<ClassTree>
) {
  val constructorMethods = methods.filter { TreeUtils.isConstructor(it) }
  val nonConstructorMethods = methods.filterNot { TreeUtils.isConstructor(it) }
  val publicMethods = filterMethods(nonConstructorMethods, Modifier.PUBLIC)
  val nonPublicMethods = filterNotMethods(nonConstructorMethods, Modifier.PUBLIC)
  val publicFields = filterFields(fields, Modifier.PUBLIC)
  val nonPublicFields = filterNotFields(fields, Modifier.PUBLIC)
}

class ClassStaticInfo(
  methods: List<MethodTree>,
  fields: List<VariableTree>,
  blocks: List<BlockTree>,
  classes: List<ClassTree>
) : ClassInfo(true, methods, fields, blocks, classes)

class ClassInstanceInfo(
  methods: List<MethodTree>,
  fields: List<VariableTree>,
  blocks: List<BlockTree>,
  classes: List<ClassTree>
) : ClassInfo(false, methods, fields, blocks, classes)

class ClassInfoPair(val static: ClassStaticInfo, val nonStatic: ClassInstanceInfo)

fun prepareClass(classTree: ClassTree): ClassInfoPair {
  // TODO skip abstract and native methods
  // TODO skip abstract methods in an interface, which have a null body but do not have an ABSTRACT flag.
  val methods = classTree.members.filterIsInstance(MethodTree::class.java)
  val fields = classTree.members.filterIsInstance(VariableTree::class.java)
  val blocks = classTree.members.filterIsInstance(BlockTree::class.java)
  // This includes Tree.Kind.CLASS, Tree.Kind.ANNOTATION_TYPE, Tree.Kind.INTERFACE, Tree.Kind.ENUM
  val classes = classTree.members.filterIsInstance(ClassTree::class.java)

  //

  return ClassInfoPair(
    ClassStaticInfo(
      filterMethods(methods, Modifier.STATIC),
      filterFields(fields, Modifier.STATIC),
      blocks.filter { it.isStatic },
      filterClasses(classes, Modifier.STATIC)
    ),
    ClassInstanceInfo(
      filterNotMethods(methods, Modifier.STATIC),
      filterNotFields(fields, Modifier.STATIC),
      blocks.filterNot { it.isStatic },
      filterNotClasses(classes, Modifier.STATIC)
    )
  )
}
