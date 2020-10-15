package org.checkerframework.checker.mungo.assertions

class InferenceResult(val thenAssertion: SymbolicAssertion, val elseAssertion: SymbolicAssertion) {

  override fun toString(): String {
    if (thenAssertion === elseAssertion) {
      return "$thenAssertion"
    }
    return "then: $thenAssertion; else: $elseAssertion"
  }

}
