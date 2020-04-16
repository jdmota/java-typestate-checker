public class CastingChecks {

  public void main1() {
    JavaIterator it = new JavaIterator();
    // :: warning: (it: JavaIterator{HasNext})
    Object obj = it;
    // :: warning: (obj: JavaIterator{HasNext})
    JavaIterator it2 = (JavaIterator) obj;
    // :: warning: (it2: JavaIterator{HasNext|Next})
    while (it2.hasNext()) {
      // :: warning: (it2: JavaIterator{Next})
      it2.next();
    }
  }

  public void main2() {
    JavaIterator it = new JavaIterator();
    // :: warning: (it: JavaIterator{HasNext})
    while (it.hasNext()) {
      // :: warning: (it: JavaIterator{Next})
      it.next();
    }
    // :: warning: (it: Ended)
    Object obj = it;
    // :: warning: (cast.unsafe)
    // :: warning: (obj: Ended)
    JavaIterator it2 = (JavaIterator) obj;
    // :: warning: (it2: JavaIterator{HasNext|Next})
    while (it2.hasNext()) {
      // :: warning: (it2: JavaIterator{Next})
      it2.next();
    }
  }

}
