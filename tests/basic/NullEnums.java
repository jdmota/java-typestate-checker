import jatyc.lib.Typestate;

@Typestate("File.protocol")
public class NullEnums {

  public FileStatus open() {
    // :: error: (Incompatible return value: cannot cast from Null to Shared{FileStatus})
    return null;
  }

  public boolean hasNext() {
    return false;
  }

  public int read() {
    return -1;
  }

  public void close() {
  }

  public FileStatus anytime() {
    // :: error: (Incompatible return value: cannot cast from Null to Shared{FileStatus})
    return null;
  }

}
