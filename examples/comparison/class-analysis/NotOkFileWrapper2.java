import mungo.lib.Typestate;
import org.checkerframework.checker.mungo.lib.MungoNullable;

@Typestate("FileWrapperProtocol")
class NotOkFileWrapper2 {

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
