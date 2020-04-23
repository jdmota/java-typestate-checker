import org.checkerframework.checker.mungo.lib.MungoTypestate;

@MungoTypestate("FaultyFile.protocol")
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
