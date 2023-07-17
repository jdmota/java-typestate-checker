public class CFG {
  public void main1(String[] args) {
    while (true) {}
  }

  public void main2(String[] args) {
    JavaIterator it = new JavaIterator();
    if (true) {

    } else {
      // :: warning: (it: Bottom)
      it.next();
    }
    // :: warning: (it: State{JavaIterator, HasNext})
    it.close();
  }

  public void main3(String[] args) {
    JavaIterator it = new JavaIterator();
    // :: error: ([it] did not complete its protocol (found: State{JavaIterator, HasNext}))
    System.exit(0);
  }
}
