import org.checkerframework.checker.jtc.lib.Typestate;

import java.util.List;
import java.util.LinkedList;

@Typestate("FileInCollection.protocol")
class FileInCollection {

  public FileState state() {
    return FileState.CLOSE;
  }

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

  public static void main1(String[] args) {
    List<FileInCollection> list = new LinkedList<>();
    // :: error: (Passing an object with protocol to a method that cannot be analyzed)
    list.add(new FileInCollection());

    // :: error: (enhancedfor.type.incompatible)
    for (FileInCollection f : list) {
      // :: warning: (f: State "Init" | State "Open" | State "Read" | State "Close" | Ended | Moved)
      // :: error: (Cannot call state on ended protocol, on moved value)
      switch (f.state()) {
        case INIT:
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
          break;
        case OPEN:
        case READ:
          // :: warning: (f: State "Open" | State "Read")
          while (f.hasNext()) {
            // :: warning: (f: State "Read")
            f.read();
          }
          // :: warning: (f: State "Close")
          f.close();
          break;
        case CLOSE:
          // :: warning: (f: State "Close")
          f.close();
          break;
      }
    }
  }

  // TODO
  /*public static void main2(String[] args) {
    FileInCollection[] list = new FileInCollection[] { new FileInCollection() };

    :: error: (enhancedfor.type.incompatible)
    for (FileInCollection f : list) {
      :: warning: (f: State "Init" | State "Open" | State "Read" | State "Close" | Ended | Moved)
      :: error: (Cannot call state on ended protocol, on moved value)
      switch (f.state()) {
        case INIT:
          :: warning: (f: State "Init")
          switch (f.open()) {
            case OK:
              :: warning: (f: State "Open")
              while (f.hasNext()) {
                :: warning: (f: State "Read")
                f.read();
              }
              :: warning: (f: State "Close")
              f.close();
              break;
            case ERROR:
              break;
          }
          break;
        case OPEN:
        case READ:
          :: warning: (f: FileInCollection{Open|Read})
          while (f.hasNext()) {
            :: warning: (f: State "Read")
            f.read();
          }
          :: warning: (f: State "Close")
          f.close();
          break;
        case CLOSE:
          :: warning: (f: State "Close")
          f.close();
          break;
      }
    }
  }*/

}
