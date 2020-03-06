package org.checkerframework.checker.mungo.typestate.ast;

import java.util.List;
import java.util.Map;
import java.util.function.Function;
import java.util.stream.Collectors;

public class Utils {

  public static <T, R> List<R> map(List<T> list, Function<T, R> mapper) {
    return list.stream().map(mapper).collect(Collectors.toList());
  }

  public static <K, V> Map<K, V> listToMap(List<Map.Entry<K, V>> list) {
    return list.stream().collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue));
  }

}
