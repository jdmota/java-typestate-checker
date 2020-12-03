import mungo.lib.Typestate;
import org.checkerframework.checker.jtc.lib.Nullable;

@Typestate("FileWrapperProtocol")
class NotOkFileWrapper3 {

  private @Nullable File file = null;

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
