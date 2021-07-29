import jatyc.lib.Typestate;

@Typestate("FileProtocol")
public class File {

  public FileStatus open() {
    return FileStatus.OK;
  }

  public String read() {
    return "";
  }

  public void close() {

  }

}
