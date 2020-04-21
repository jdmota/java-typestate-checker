import mungo.lib.Typestate;

@Typestate("FileProtocol")
class File {

  public enum Status {
    OK, ERROR
  }

  public Status open() {
    return Status.OK;
  }

  public boolean eof() {
    return false;
  }

  public int read() {
    return -1;
  }

  public void close() {
  }

}
