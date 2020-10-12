package org.checkerframework.checker.mungo.assertions

class InferenceResult(val thenAssertion: Assertion, val elseAssertion: Assertion) {

  override fun toString(): String {
    if (thenAssertion === elseAssertion) {
      return "$thenAssertion"
    }
    return "then: $thenAssertion; else: $elseAssertion"
  }

}
