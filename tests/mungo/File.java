import org.checkerframework.checker.mungo.lib.MungoTypestate;

@MungoTypestate("File.protocol")
class File {

  public enum Status {
    OK, ERROR
  }

  public Status open() {
    return Status.OK;
  }

  public boolean hasNext() {
    return false;
  }

  public int read() {
    return -1;
  }

  public void close() {
  }

  public static void main1(String[] args) {
    File f = new File();

    // :: warning: (f: FileProtocol{Init})
    switch (f.open()) {
      case OK:
        // :: warning: (f: FileProtocol{Open})
        while (f.hasNext()) {
          // :: warning: (f: FileProtocol{Read})
          f.read();
        }
        // :: warning: (f: FileProtocol{Close})
        f.close();
        break;
      case ERROR:
        break;
    }
  }

  public static void main2(String[] args) {
    File f = new File();

    // :: warning: (f: FileProtocol{Init})
    switch (f.open()) {
      case OK:
      case ERROR:
        // :: warning: (f: FileProtocol{Open} | Ended)
        // :: error: (Cannot call hasNext on ended protocol)
        while (f.hasNext()) {
          // :: warning: (f: FileProtocol{Read})
          f.read();
        }
        // :: warning: (f: FileProtocol{Close})
        f.close();
    }
  }

}
