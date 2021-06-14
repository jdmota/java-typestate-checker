package jatyc.typestate

import java.util.function.Function
import java.util.stream.Collectors

// Some utils used by the typestate parser
// Mark static methods as @JvmStatic so that they can be accessed from Java code

object Utils {
  @JvmStatic
  fun <T, R> map(list: List<T>, mapper: Function<T, R>): List<R> {
    return list.stream().map(mapper).collect(Collectors.toList())
  }

  @JvmStatic
  fun <T, R> map(list: Set<T>, mapper: Function<T, R>): List<R> {
    return list.stream().map(mapper).collect(Collectors.toList())
  }

  @JvmStatic
  fun <K, V> listToMap(list: List<Map.Entry<K, V>>): Map<K, V> {
    return list.stream().collect(Collectors.toMap({ it.key }, { it.value }))
  }
}
