import mungo.lib.Typestate;

@Typestate("MyComparatorProtocol")
public class MyComparator<T> {
  public int compare(T a, T b) {
    throw new RuntimeException("not implemented");
  }
}
