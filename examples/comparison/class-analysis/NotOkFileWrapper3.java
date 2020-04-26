import mungo.lib.Typestate;
import org.checkerframework.checker.mungo.lib.MungoNullable;

@Typestate("FileWrapperProtocol")
class NotOkFileWrapper3 {

  private @MungoNullable File file = null;

  public void init(File file) {
    this.file = file;
  }

  public String read() {
    file.close();
    return "";
  }

  public void close() {
    file.read();
  }

}
