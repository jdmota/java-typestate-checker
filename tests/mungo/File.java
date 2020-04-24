import org.checkerframework.checker.mungo.lib.MungoTypestate;

@MungoTypestate("File.protocol")
class File {

  public FileStatus open() {
    return FileStatus.OK;
  }

  public boolean hasNext() {
    return false;
  }

  public int read() {
    return -1;
  }

  public void close() {
  }

  public static void main1() {
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

  public static void main2() {
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

  public static void main3() {
    File f = new File();

    // :: warning: (f: FileProtocol{Init})
    if (f.open() == FileStatus.OK) {
      // :: warning: (f: FileProtocol{Open})
      while (f.hasNext()) {
        // :: warning: (f: FileProtocol{Read})
        f.read();
      }
      // :: warning: (f: FileProtocol{Close})
      f.close();
    }
  }

  public static void main4() {
    // :: error: (Object did not complete its protocol. Type: FileProtocol{Open})
    File f = new File();

    // :: warning: (f: FileProtocol{Init})
    if (f.open() != FileStatus.OK) {
      // :: warning: (f: Ended)
      // :: error: (Cannot call hasNext on ended protocol)
      while (f.hasNext()) {
        // :: warning: (f: Bottom)
        f.read();
      }
      // :: warning: (f: Bottom)
      f.close();
    }
  }

  public static void main5() {
    File f = new File();

    // :: warning: (f: FileProtocol{Init})
    if (f.open() == FileStatus.OK) {
      // :: warning: (f: FileProtocol{Open})
      while (f.hasNext() == true) {
        // :: warning: (f: FileProtocol{Read})
        f.read();
      }
      // :: warning: (f: FileProtocol{Close})
      f.close();
    }
  }

  public static void main6() {
    File f = new File();

    // :: warning: (f: FileProtocol{Init})
    if (f.open() == FileStatus.OK) {
      // :: warning: (f: FileProtocol{Open})
      while (!f.hasNext() == false) {
        // :: warning: (f: FileProtocol{Read})
        f.read();
      }
      // :: warning: (f: FileProtocol{Close})
      f.close();
    }
  }

  public static void main7() {
    File f = new File();

    // :: warning: (f: FileProtocol{Init})
    if (f.open() == FileStatus.OK) {
      // :: warning: (f: FileProtocol{Open})
      while (f.hasNext() == false) {
        // :: warning: (f: FileProtocol{Close})
        // :: error: (Cannot call read on state Close (got: Close))
        f.read();
      }
      // :: warning: (f: FileProtocol{Read})
      f.close();
    }
  }

  public static void main8() {
    File f = new File();

    // :: warning: (f: FileProtocol{Init})
    if (f.open() == FileStatus.OK) {
      // :: warning: (f: FileProtocol{Open})
      f.hasNext();
      boolean bool = false;
      while (bool) {
        // :: warning: (f: FileProtocol{Open|Read|Close})
        // :: error: (Cannot call read on states Open, Close (got: Open, Read, Close))
        f.read();
      }
      // :: warning: (f: FileProtocol{Open|Read|Close})
      f.close();
    }
  }

}
