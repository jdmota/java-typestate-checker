import mungo.lib.Typestate;

@Typestate("FileProtocol")
class File {

  public FileStatus open() {
    return FileStatus.OK;
  }

  public String read() {
    return "";
  }

  public void close() {
  }

}
