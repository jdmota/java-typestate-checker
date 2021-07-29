import mungo.lib.Typestate;

@Typestate("FileProtocol")
class File {

  public FileStatus open() {
    return FileStatus.OK;
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
