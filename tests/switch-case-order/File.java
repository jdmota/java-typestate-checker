import jatyc.lib.Typestate;

@Typestate("File.protocol")
final class File {

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
      default:
        // :: warning: (f: Bottom)
        File f2 = f;
    }
  }

  public static void main2() {
    File f = new File();

    // :: warning: (f: State{File, Init})
    switch (f.open()) {
      // :: warning: (FileStatus.ERROR: Shared{FileStatus})
      case ERROR:
        break;
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
      default:
        // :: warning: (f: Bottom)
        File f2 = f;
    }
  }
}
