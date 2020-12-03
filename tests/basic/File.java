import org.checkerframework.checker.jtc.lib.Typestate;

@Typestate("File.protocol")
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

    // :: warning: (f: State "Init")
    switch (f.open()) {
      case OK:
        // :: warning: (f: State "Open")
        while (f.hasNext()) {
          // :: warning: (f: State "Read")
          f.read();
        }
        // :: warning: (f: State "Close")
        f.close();
        break;
      case ERROR:
        break;
    }
  }

  public static void main2() {
    File f = new File();

    // :: warning: (f: State "Init")
    switch (f.open()) {
      case OK:
      case ERROR:
        // :: warning: (f: State "Open" | Ended)
        // :: error: (Cannot call hasNext on ended protocol)
        while (f.hasNext()) {
          // :: warning: (f: State "Read")
          f.read();
        }
        // :: warning: (f: State "Close")
        f.close();
    }
  }

  public static void main3() {
    File f = new File();

    // :: warning: (f: State "Init")
    if (f.open() == FileStatus.OK) {
      // :: warning: (f: State "Open")
      while (f.hasNext()) {
        // :: warning: (f: State "Read")
        f.read();
      }
      // :: warning: (f: State "Close")
      f.close();
    }
  }

  public static void main4() {
    // :: error: (Object did not complete its protocol. Type: State "Open")
    File f = new File();

    // :: warning: (f: State "Init")
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

    // :: warning: (f: State "Init")
    if (f.open() == FileStatus.OK) {
      // :: warning: (f: State "Open")
      while (f.hasNext() == true) {
        // :: warning: (f: State "Read")
        f.read();
      }
      // :: warning: (f: State "Close")
      f.close();
    }
  }

  public static void main6() {
    File f = new File();

    // :: warning: (f: State "Init")
    if (f.open() == FileStatus.OK) {
      // :: warning: (f: State "Open")
      while (!f.hasNext() == false) {
        // :: warning: (f: State "Read")
        f.read();
      }
      // :: warning: (f: State "Close")
      f.close();
    }
  }

  public static void main7() {
    File f = new File();

    // :: warning: (f: State "Init")
    if (f.open() == FileStatus.OK) {
      // :: warning: (f: State "Open")
      while (f.hasNext() == false) {
        // :: warning: (f: State "Close")
        // :: error: (Cannot call read on state Close (got: Close))
        f.read();
      }
      // :: warning: (f: State "Read")
      f.close();
    }
  }

  public static void main8() {
    File f = new File();

    // :: warning: (f: State "Init")
    if (f.open() == FileStatus.OK) {
      // :: warning: (f: State "Open")
      f.hasNext();
      boolean bool = false;
      while (bool) {
        // :: warning: (f: State "Open" | State "Read" | State "Close")
        // :: error: (Cannot call read on states Open, Close (got: Open, Read, Close))
        f.read();
      }
      // :: warning: (f: State "Open" | State "Read" | State "Close")
      f.close();
    }
  }

}
