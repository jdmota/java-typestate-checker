package jatyc.core.typesystem

import jatyc.typestate.graph.*

class ProtocolSyncSubtyping {

  companion object {
    private val cache: MutableMap<Pair<AbstractState<*>, AbstractState<*>>, Boolean> = mutableMapOf()

    fun isSubtype(sub: AbstractState<*>, sup: AbstractState<*>): Boolean {
      val pair = Pair(sub, sup)
      var value = cache[pair]
      if (value == null) {
        cache[pair] = true // Set to true to avoid infinite recursion
        value = isSubtypingHelper(sub, sup)
        cache[pair] = value // Cache now the actual result
      }
      return value
    }

    private fun isSubtypingHelper(derived: AbstractState<*>, base: AbstractState<*>): Boolean {
      if (derived == base) return true
      return when {
        derived is State && base is State -> {
          // For end states, "normalizedTransitions" is empty
          val t1 = derived.normalizedTransitions
          val t2 = base.normalizedTransitions

          // If "base" is droppable, "derived" needs to be droppable
          // (base.canDropHere() ==> derived.canDropHere()) <=> (!base.canDropHere() || derived.canDropHere())
          // Note: canDropHere() also returns true if the state is "end"
          (!base.canDropHere() || derived.canDropHere()) &&
            // Input contravariance
            t1.keys.containsAll(t2.keys) &&
            t2.keys.all { isSubtype(t1[it]!!, t2[it]!!) }
        }
        derived is DecisionState && base is DecisionState -> {
          val t1 = derived.normalizedTransitions
          val t2 = base.normalizedTransitions
          // Output covariance
          t2.keys.containsAll(t1.keys) && t1.keys.all { isSubtype(t1[it]!!, t2[it]!!) }
        }
        else -> false
      }
    }
  }

  val errors = mutableListOf<String>()

  fun subtyping(g1: Graph, g2: Graph, currentStates: Pair<AbstractState<*>, AbstractState<*>>, marked: Set<Pair<AbstractState<*>, AbstractState<*>>> = emptySet()) {
    if (currentStates in marked) return
    val derived = currentStates.first
    val base = currentStates.second
    when {
      derived is State && base is State -> {
        // For end states, "normalizedTransitions" is empty
        val t1 = derived.normalizedTransitions
        val t2 = base.normalizedTransitions

        // If "base" is droppable, "derived" needs to be droppable
        // (base.canDropHere() ==> derived.canDropHere()) <=> (!base.canDropHere() || derived.canDropHere())
        // Note: canDropHere() also returns true if the state is "end"
        if (!(!base.canDropHere() || derived.canDropHere())) {
          errors.add(inputErrorMsg(g1, g2, currentStates, listOf("drop: end")))
        }

        if (!t1.keys.containsAll(t2.keys)) { // Input contravariance
          val common = t2.keys.intersect(t1.keys)
          common.forEach {
            subtyping(g1, g2, t1[it]!! to t2[it]!!, marked + currentStates)
          }
          errors.add(inputErrorMsg(g1, g2, currentStates, t2.minus(common).map { it.key.name }))
        } else {
          t2.keys.forEach {
            subtyping(g1, g2, t1[it]!! to t2[it]!!, marked + currentStates)
          }
        }
      }
      derived is DecisionState && base is DecisionState -> {
        val t1 = derived.normalizedTransitions
        val t2 = base.normalizedTransitions
        if (!t2.keys.containsAll(t1.keys)) { // Output covariance
          val common = t1.keys.intersect(t2.keys)
          common.forEach {
            subtyping(g1, g2, t1[it]!! to t2[it]!!, marked + currentStates)
          }
          errors.add(outputErrorMsg(g1, g2, currentStates, t1.minus(common).map { it.key.label }))
        } else {
          t1.keys.forEach {
            subtyping(g1, g2, t1[it]!! to t2[it]!!, marked + currentStates)
          }
        }
      }
      else -> {
        errors.add("Discordant states error: state $derived in ${g1.filename} is ${type(derived)} while state $base in ${g2.filename} is ${type(base)}")
      }
    }
  }

  private fun type(state: AbstractState<*>): String {
    return when (state) {
      is EndState -> "END"
      is State -> "INPUT"
      is DecisionState -> "OUTPUT"
    }
  }

  private fun inputErrorMsg(fn1: Graph, fn2: Graph, currStates: Pair<AbstractState<*>, AbstractState<*>>, diff: List<String>): String {
    val first = currStates.first.format()
    val second = currStates.second.format()
    return "$diff transition(s) in [$second] of ${fn2.filename} are not included in [$first] of ${fn1.filename}"
  }

  private fun outputErrorMsg(fn1: Graph, fn2: Graph, currStates: Pair<AbstractState<*>, AbstractState<*>>, diff: List<String>): String {
    val first = currStates.first.format()
    val second = currStates.second.format()
    return "$diff transition(s) in $first of ${fn1.filename} are not included in $second of ${fn2.filename}"
  }
}
