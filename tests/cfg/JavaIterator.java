import jatyc.lib.Typestate;

@Typestate("JavaIterator.protocol")
public final class JavaIterator {

  public boolean hasNext() {
    return false;
  }

  public String next() {
    return "";
  }

  public void close() {}
}
