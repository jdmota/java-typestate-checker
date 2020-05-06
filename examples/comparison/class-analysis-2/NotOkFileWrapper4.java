import org.checkerframework.checker.mungo.lib.MungoNullable;

class NotOkFileWrapper4 {

  private @MungoNullable File file = null;

  public void init(File file) {
    this.file = file;
  }

  public String read() {
    return file.read();
  }

  public void close() {

  }

}
