import jatyc.lib.Nullable;

public class Next {
  private @Nullable Element next;
  public Next(Element n) { this.next = n; }
  public @Nullable Element getNext() { return next; }
  public void setNext(@Nullable Element n) {this.next = n;}
  public String toString() {
    if(next != null) return next.toString();
    else return "null";
  }
}
