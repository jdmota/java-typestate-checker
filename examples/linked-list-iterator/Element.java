import jatyc.lib.Nullable;

public class Element extends Next {

  private String value;
  public Element(String v, @Nullable Element n) {
    super(n);
    this.value = v;
  }
  public String getValue() { return value; }
  public String toString() { return value + "-->" + super.toString(); }
}
