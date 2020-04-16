public class CastingChecks {

  public void main1() {
    JavaIterator it = new JavaIterator();
    Object obj = it;
    JavaIterator it2 = (JavaIterator) obj;
    while (it2.hasNext()) {
      it2.next();
    }
  }

  public void main2() {
    JavaIterator it = new JavaIterator();
    while (it.hasNext()) {
      it.next();
    }
    Object obj = it;
    // :: warning: (cast.unsafe)
    JavaIterator it2 = (JavaIterator) obj;
    while (it2.hasNext()) {
      it2.next();
    }
  }

}
