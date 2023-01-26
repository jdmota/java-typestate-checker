import jatyc.lib.Typestate;

@Typestate("SomeObj")
// :: error: (Method [a] is required by the typestate but not implemented)
// :: error: (Method [b] is required by the typestate but not implemented)
// :: error: (Method [d] is required by the typestate but not implemented)
public class SomeObjNotOk {
  public String a(String o) {
    return "";
  }
  public Object b(Object o) {
    return "";
  }
  public String c(Object o) {
    return "";
  }
  public Object d(Object o) {
    return "";
  }
  public Object e(A o) {
    return "";
  }
  public Object e(B o) {
    return "";
  }
}
