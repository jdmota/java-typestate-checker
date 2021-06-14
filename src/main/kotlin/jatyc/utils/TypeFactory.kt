package jatyc.utils

import com.sun.source.tree.CompilationUnitTree
import com.sun.source.tree.LambdaExpressionTree
import com.sun.source.tree.Tree
import com.sun.tools.javac.code.Symbol
import jatyc.qualifiers.BottomAnno
import jatyc.qualifiers.InternalInfoAnno
import jatyc.qualifiers.UnknownAnno
import org.checkerframework.common.basetype.BaseTypeChecker
import org.checkerframework.dataflow.util.PurityUtils
import org.checkerframework.framework.source.SourceChecker
import org.checkerframework.framework.stub.StubTypes
import org.checkerframework.framework.type.*
import org.checkerframework.framework.util.DefaultAnnotationFormatter
import org.checkerframework.framework.util.PurityUnqualified
import org.checkerframework.javacutil.AnnotationBuilder
import javax.lang.model.element.AnnotationMirror
import javax.lang.model.element.Element
import javax.lang.model.util.Elements

private class FakeBasicTypeChecker(myChecker: SourceChecker) : BaseTypeChecker() {
  init {
    processingEnvironment = myChecker.processingEnvironment
  }
}

class FakeAnnotatedTypeFactory internal constructor(myChecker: SourceChecker) : AnnotatedTypeFactory(FakeBasicTypeChecker(myChecker)) {

  private val typesFromStubFilesField = StubTypes::class.java.getDeclaredField("typesFromStubFiles")
  private val typesFromStubFiles = mutableMapOf<Element, AnnotatedTypeMirror>()

  private val topAnnotation = AnnotationBuilder(checker.processingEnvironment, UnknownAnno::class.java).build()
  private val bottomAnnotation = AnnotationBuilder(checker.processingEnvironment, BottomAnno::class.java).build()

  init {
    typesFromStubFilesField.isAccessible = true
    postInit()
    parseStubFiles()
  }

  private class AnnotationFormatter : DefaultAnnotationFormatter() {
    override fun formatAnnotationString(annos: MutableCollection<out AnnotationMirror>?, printInvisible: Boolean): String {
      return ""
    }

    override fun formatAnnotationMirror(am: AnnotationMirror, sb: StringBuilder) {

    }
  }

  override fun createAnnotatedTypeFormatter(): AnnotatedTypeFormatter {
    val printVerboseGenerics = checker.hasOption("printVerboseGenerics")
    val defaultPrintInvisibleAnnos = printVerboseGenerics || checker.hasOption("printAllQualifiers")
    return DefaultAnnotatedTypeFormatter(
      AnnotationFormatter(),
      printVerboseGenerics, // -AprintVerboseGenerics implies -AprintAllQualifiers
      defaultPrintInvisibleAnnos
    )
  }

  override fun createSupportedTypeQualifiers(): Set<Class<out Annotation>> {
    return setOf(BottomAnno::class.java, InternalInfoAnno::class.java, UnknownAnno::class.java, PurityUnqualified::class.java)
  }

  override fun createQualifierHierarchy(): QualifierHierarchy {
    return FakeQualifierHierarchy(supportedTypeQualifiers, elements)
  }

  private inner class FakeQualifierHierarchy(qualifierClasses: MutableSet<Class<out Annotation>>, elements: Elements) : NoElementQualifierHierarchy(qualifierClasses, elements) {

    override fun createTops(): MutableSet<AnnotationMirror> {
      return mutableSetOf(topAnnotation)
    }

    override fun createBottoms(): MutableSet<AnnotationMirror> {
      return mutableSetOf(bottomAnnotation)
    }

    override fun getTopAnnotation(start: AnnotationMirror?): AnnotationMirror = topAnnotation

    override fun getBottomAnnotation(start: AnnotationMirror?): AnnotationMirror = bottomAnnotation

    override fun isSubtype(subAnno: AnnotationMirror, superAnno: AnnotationMirror): Boolean {
      return true
    }

    override fun findAnnotationInSameHierarchy(annos: MutableCollection<out AnnotationMirror>, annotationMirror: AnnotationMirror): AnnotationMirror? {
      return annos.firstOrNull()
    }
  }

  override fun parseStubFiles() {
    super.parseStubFiles()

    val types = typesFromStubFilesField.get(stubTypes) as MutableMap<*, *>
    for ((element, annotatedType) in types) {
      typesFromStubFiles[element as Element] = annotatedType as AnnotatedTypeMirror
    }
  }

  // So that we get the original AnnotatedTypeMirror, with all the annotations
  // See "isSupportedQualifier" for context
  fun getTypeFromStub(elt: Element) = typesFromStubFiles[elt]

  // Allow all annotations to be added to AnnotatedTypeMirror's
  override fun isSupportedQualifier(a: AnnotationMirror?) = a != null
  override fun isSupportedQualifier(className: String?) = className != null
  override fun isSupportedQualifier(clazz: Class<out Annotation>?) = clazz != null

  override fun shouldWarnIfStubRedundantWithBytecode(): Boolean {
    return true
  }

}

class TypeFactory(checker: SourceChecker) {

  private val fake = FakeAnnotatedTypeFactory(checker)

  fun setRoot(root: CompilationUnitTree) {
    fake.setRoot(root)
  }

  fun getPath(tree: Tree) = fake.getPath(tree)
  fun getProvider() = fake

  fun isSideEffectFree(method: Symbol.MethodSymbol) = PurityUtils.isSideEffectFree(fake, method)

  fun getTypeFromStub(elt: Element) = fake.getTypeFromStub(elt)

  fun getAnnotatedType(elt: Element): AnnotatedTypeMirror = fake.fromElement(elt)
  fun getAnnotatedType(tree: Tree): AnnotatedTypeMirror = fake.getAnnotatedType(tree)

  fun getFunctionTypeFromTree(node: LambdaExpressionTree): AnnotatedTypeMirror.AnnotatedExecutableType = fake.getFunctionTypeFromTree(node)

}
