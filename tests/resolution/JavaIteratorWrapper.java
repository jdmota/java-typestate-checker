import jatyc.lib.Typestate;
import jatyc.lib.Requires;
import utils.JavaIterator;

@Typestate("JavaIteratorWrapper")
class JavaIteratorWrapper1 {

  private JavaIterator iterator;

  public void init(@Requires("HasNext") JavaIterator it) {
    // :: warning: (this.iterator: Null)
    // :: warning: (it: State{utils.JavaIterator, HasNext})
    iterator = it;
  }

  public boolean hasNext() {
    // :: warning: (this.iterator: State{utils.JavaIterator, HasNext})
    // :: warning: (this.iterator: State{utils.JavaIterator, Next})
    return iterator.hasNext();
  }

  public String next() {
    // :: warning: (this.iterator: State{utils.JavaIterator, Next})
    return iterator.next();
  }

}
