import jatyc.lib.Typestate;

@Typestate("WrongDerivedProtocol")
// :: error: ([drop: end] transition(s) in [end] of BaseProtocol.protocol are not included in [B] of WrongDerivedProtocol.protocol)
public class WrongDerived extends Base {

}
