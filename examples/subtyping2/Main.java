public class Main {

  public static void main(String[] args) throws Exception {
    //Base o = new Base();
    Base o = new Derived();
    while(!o.offer1().equals(RestrictedStatus.NO)) { //Status.NO with Base
      o.offer2();
    }
    o.done();
  }
}
