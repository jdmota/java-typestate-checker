import org.checkerframework.checker.mungo.lib.MungoTypestate;

@MungoTypestate("FaultyFile2.protocol")
class FaultyFile2 {

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
