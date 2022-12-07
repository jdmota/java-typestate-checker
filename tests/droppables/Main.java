import jatyc.lib.Requires;

public class Main {
  public static void main1() {
    MyComparator comparator = new MyComparator();
    // :: warning: (comparator: State{MyComparator, Start})
    // :: warning: (java.lang.System.out: Shared{java.io.PrintStream})
    System.out.println(comparator.compare(10, 5));
    // :: warning: (comparator: State{MyComparator, Start})
    // :: warning: (Object [comparator] with type State{MyComparator, Start} will be dropped)
    use1(comparator);
  }

  public static void use1(MyComparator comparator) {

  }

  public static void main2() {
    MyComparator comparator = new MyComparator();
    // :: warning: (comparator: State{MyComparator, Start})
    // :: warning: (java.lang.System.out: Shared{java.io.PrintStream})
    System.out.println(comparator.compare(10, 5));
    // :: warning: (comparator: State{MyComparator, Start})
    use2(comparator);
  }

  public static void use2(@Requires("Start") MyComparator comparator) {

  }
}
