import org.checkerframework.checker.mungo.lib.MungoTypestate;

@MungoTypestate("FaultyFile.protocol")
// :: error: (Class has no public method for transition boolean hasNext() on state Open)
// :: error: (Duplicate transition void close() on state Close)
// :: error: (Expected a decision state in transition boolean hasNext2() on state Open)
// :: error: (Unexpected decision state in transition int read() on state Read)
// :: error: (Expected decision state with two labels (true/false) in transition boolean hasNext() on state Open)
// :: error: (Expected decision state to include all enumeration labels in transition FileStatus open() on state Init)
// :: error: (Unknown type voidd in transition voidd close() on state Read)
class FaultyFile {

  public FileStatus open() {
    return FileStatus.OK;
  }

  public void hasNext() {
  }

  public boolean hasNext2() {
    return false;
  }

  public int read() {
    return -1;
  }

  public void close() {
  }

}
