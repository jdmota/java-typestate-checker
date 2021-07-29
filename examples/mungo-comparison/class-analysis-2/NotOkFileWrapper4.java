import jatyc.lib.Nullable;

class NotOkFileWrapper4 {

  private @Nullable File file = null;

  public void init(File file) {
    this.file = file;
  }

  public String read() {
    return file.read();
  }

  public void close() {

  }

}
