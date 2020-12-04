import mungo.lib.Typestate;

@Typestate("MyComparatorProtocol")
public class MyComparator {
  public int compare(int a, int b) {
    return a < b ? -1 : a > b ? 1 : 0;
  }
}
