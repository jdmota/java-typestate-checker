public class CastingChecks {

  public void main1() {
    JavaIterator it = new JavaIterator();
    // :: warning: (it: State{JavaIterator, HasNext})
    // :: error: (Cannot assign: cannot cast from State{JavaIterator, HasNext} to Shared{java.lang.Object} | Null)
    Object obj = it;
    // :: warning: (obj: Bottom)
    JavaIterator it2 = (JavaIterator) obj;
    // :: warning: (it2: Bottom)
    while (it2.hasNext()) {
      // :: warning: (it2: Bottom)
      it2.next();
    }
  }

  public void main2() {
    JavaIterator it = new JavaIterator();
    // :: warning: (it: State{JavaIterator, HasNext})
    while (it.hasNext()) {
      // :: warning: (it: State{JavaIterator, Next})
      it.next();
    }
    // :: warning: (it: State{JavaIterator, end})
    Object obj = it;
    // :: warning: (obj: State{JavaIterator, end})
    JavaIterator it2 = (JavaIterator) obj;
    // :: warning: (it2: State{JavaIterator, end})
    // :: error: (Cannot call [hasNext] on State{JavaIterator, end})
    while (it2.hasNext()) {
      // :: warning: (it2: Bottom)
      it2.next();
    }
  }

}
