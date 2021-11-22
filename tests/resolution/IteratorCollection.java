import jatyc.lib.Typestate;
import jatyc.lib.Requires;
import utils.JavaIterator;

@Typestate("ProtocolWithArray")
// :: error: (Method [init2] is required by the typestate but not implemented)
class IteratorCollection {

  private JavaIterator[] iterators;

  public void init(JavaIterator[] its) {
    // :: warning: (this.iterators: Null)
    // :: warning: (its: Shared{utils.JavaIterator[]})
    iterators = its;
  }

  public void init2(JavaIterator it) {

  }

}
