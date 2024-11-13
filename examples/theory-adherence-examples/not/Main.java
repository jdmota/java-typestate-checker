public class Main {
  public static void main(String[] args) {
    A a = new A();
    if(!a.m1()) { // A1
      while(!a.m1()) {} //A1
      a.m2(); //end
    } else a.m2(); //A2
  }
}
