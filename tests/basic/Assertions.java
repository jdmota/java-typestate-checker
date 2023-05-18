public class Assertions {
  public static void main1() {
    File f = new File();
    // :: warning: (f: State{File, Init})
    // :: warning: (FileStatus.OK: Shared{FileStatus})
    assert f.open() == FileStatus.OK;
    // :: warning: (f: State{File, Init} | State{File, Open})
    // :: error: (Cannot call [hasNext] on State{File, Init} | State{File, Open})
    f.hasNext();
    // :: warning: (f: State{File, Close})
    f.close();
  }

  public static void main2() {
    File f = new File();
    // :: warning: (f: State{File, Init})
    // :: warning: (FileStatus.OK: Shared{FileStatus})
    assert f.open() == FileStatus.OK : "description";
    // :: warning: (f: State{File, Init} | State{File, Open})
    // :: error: (Cannot call [hasNext] on State{File, Init} | State{File, Open})
    f.hasNext();
    // :: warning: (f: State{File, Close})
    f.close();
  }
}
