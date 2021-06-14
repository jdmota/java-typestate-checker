import jatyc.lib.Typestate;

@Typestate("File.protocol")
class File {

  public FileStatus open() {
    // :: warning: (FileStatus.OK: Shared{FileStatus})
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

    // :: warning: (f: State{File, Init})
    switch (f.open()) {
      // :: warning: (FileStatus.OK: Shared{FileStatus})
      case OK:
        // :: warning: (f: State{File, Open})
        while (f.hasNext()) {
          // :: warning: (f: State{File, Read})
          f.read();
        }
        // :: warning: (f: State{File, Close})
        f.close();
        break;
      // :: warning: (FileStatus.ERROR: Shared{FileStatus})
      case ERROR:
        break;
    }
  }

  public static void main2() {
    File f = new File();

    // :: warning: (f: State{File, Init})
    switch (f.open()) {
      // :: warning: (FileStatus.OK: Shared{FileStatus})
      case OK:
      // :: warning: (FileStatus.ERROR: Shared{FileStatus})
      case ERROR:
        // :: warning: (f: State{File, Open} | State{File, end})
        // :: error: (Cannot call [hasNext] on State{File, Open} | State{File, end})
        while (f.hasNext()) {
          // :: warning: (f: State{File, Read})
          f.read();
        }
        // :: warning: (f: State{File, Close})
        f.close();
    }
  }

  public static void main3() {
    File f = new File();

    // :: warning: (f: State{File, Init})
    // :: warning: (FileStatus.OK: Shared{FileStatus})
    if (f.open() == FileStatus.OK) {
      // :: warning: (f: State{File, Open})
      while (f.hasNext()) {
        // :: warning: (f: State{File, Read})
        f.read();
      }
      // :: warning: (f: State{File, Close})
      f.close();
    }
  }

  // :: error: ([f] did not complete its protocol (found: State{File, Open}))
  public static void main4() {
    File f = new File();

    // :: warning: (f: State{File, Init})
    // :: warning: (FileStatus.OK: Shared{FileStatus})
    if (f.open() != FileStatus.OK) {
      // :: warning: (f: State{File, end})
      // :: error: (Cannot call [hasNext] on State{File, end})
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

    // :: warning: (f: State{File, Init})
    // :: warning: (FileStatus.OK: Shared{FileStatus})
    if (f.open() == FileStatus.OK) {
      // :: warning: (f: State{File, Open})
      while (f.hasNext() == true) {
        // :: warning: (f: State{File, Read})
        f.read();
      }
      // :: warning: (f: State{File, Close})
      f.close();
    }
  }

  public static void main6() {
    File f = new File();

    // :: warning: (f: State{File, Init})
    // :: warning: (FileStatus.OK: Shared{FileStatus})
    if (f.open() == FileStatus.OK) {
      // :: warning: (f: State{File, Open})
      while (!f.hasNext() == false) {
        // :: warning: (f: State{File, Read})
        f.read();
      }
      // :: warning: (f: State{File, Close})
      f.close();
    }
  }

  public static void main7() {
    File f = new File();

    // :: warning: (f: State{File, Init})
    // :: warning: (FileStatus.OK: Shared{FileStatus})
    if (f.open() == FileStatus.OK) {
      // :: warning: (f: State{File, Open})
      while (f.hasNext() == false) {
        // :: warning: (f: State{File, Close})
        // :: error: (Cannot call [read] on State{File, Close})
        f.read();
      }
      // :: warning: (f: State{File, Read})
      f.close();
    }
  }

  public static void main8() {
    File f = new File();

    // :: warning: (f: State{File, Init})
    // :: warning: (FileStatus.OK: Shared{FileStatus})
    if (f.open() == FileStatus.OK) {
      // :: warning: (f: State{File, Open})
      f.hasNext();
      boolean bool = false;
      while (bool) {
        // :: warning: (f: State{File, Close} | State{File, Open} | State{File, Read})
        // :: error: (Cannot call [read] on State{File, Close} | State{File, Open} | State{File, Read})
        f.read();
      }
      // :: warning: (f: State{File, Close} | State{File, Open} | State{File, Read})
      f.close();
    }
  }

}
