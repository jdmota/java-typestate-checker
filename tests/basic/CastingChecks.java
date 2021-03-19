public class CastingChecks {

  public void main1() {
    JavaIterator it = new JavaIterator();
    // :: warning: (it: State "HasNext")
    // :: error: (Up-casting not allowed. Left-hand-side has no protocol.)
    Object obj = it;
    // :: warning: (obj: State "HasNext")
    JavaIterator it2 = (JavaIterator) obj;
    // :: warning: (it2: State "HasNext" | State "Next")
    while (it2.hasNext()) {
      // :: warning: (it2: State "Next")
      it2.next();
    }
  }

  public void main2() {
    JavaIterator it = new JavaIterator();
    // :: warning: (it: State "HasNext")
    while (it.hasNext()) {
      // :: warning: (it: State "Next")
      it.next();
    }
    // :: warning: (it: Ended)
    // :: error: (Up-casting not allowed. Left-hand-side has no protocol.)
    Object obj = it;
    // :: warning: (cast.unsafe)
    // :: warning: (obj: Ended)
    JavaIterator it2 = (JavaIterator) obj;
    // :: warning: (it2: State "HasNext" | State "Next")
    while (it2.hasNext()) {
      // :: warning: (it2: State "Next")
      it2.next();
    }
  }

}
