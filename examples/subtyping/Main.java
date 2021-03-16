public class Main {

  public static void main(String[] args) throws Exception {
    Base o = new Base();
    //Derived o = new Derived();
    while(!o.offer1().equals(Status_NO.NO)) { //Status.NO with Base
      o.offer2();
    }
    o.done();
  }
}
