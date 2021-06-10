import mungo.lib.Typestate;

@Typestate("Derived.protocol")
// :: error: (Method [remove] is required by the typestate but not implemented)
public class Derived extends Base {

}
