package org.checkerframework.checker.mungo.abstract_analysis

// https://en.wikipedia.org/wiki/Greatest_common_divisor#Euclid's_algorithm
private fun gcd(a: Int, b: Int): Int = if (b == 0) a else gcd(b, a % b)

// https://en.wikipedia.org/wiki/Least_common_multiple#Using_the_greatest_common_divisor
private fun lcm(a: Int, b: Int) = if (a > b) (a / gcd(a, b)) * b else (b / gcd(a, b)) * a

// a / b
class Fraction(a: Int, b: Int) {

  val a: Int
  val b: Int

  init {
    if (a < 0) {
      throw AssertionError("fraction: a should be non negative")
    }
    if (b <= 0) {
      throw AssertionError("fraction: b should be positive")
    }
    if (a > b) {
      throw AssertionError("fraction: a should be less than or equal to b")
    }
    // Store fraction always in their simplified form
    val c = gcd(a, b)
    this.a = a / c
    this.b = b / c
  }

  // Look for the lowest common denominator to avoid multiplications that could produce overflow
  fun plus(f: Fraction) = lcm(b, f.b).let { Fraction((a * (it / b)) + (f.a * (it / f.b)), it) }

  fun half() = if (a % 2 == 0) Fraction(a / 2, b) else Fraction(a, b * 2)

  override fun equals(other: Any?): Boolean {
    if (other !is Fraction) return false
    if (this === other) return true
    return a == other.a && b == other.b
  }

  override fun hashCode(): Int {
    return 31 * a.hashCode() + b.hashCode()
  }

}
