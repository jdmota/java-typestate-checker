public class Main {
  public static void main(String[] args) {
    A a = new A(); //tool: A1, theory: A1
    boolean x = false;
    if (x = a.m1()) {
      //tool: A1 U A2, theory: A2
      a.m2();  //tool: A1 U A2 (error), theory: end
    }
  }

}
