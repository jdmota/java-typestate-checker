import org.checkerframework.checker.jtc.lib.Typestate;

import java.util.List;
import java.util.LinkedList;

@Typestate("FileInCollection.protocol")
class FileInCollection {

  public FileState state() {
    // :: warning: (FileState.CLOSE: Shared{FileState})
    return FileState.CLOSE;
  }

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

  /*:: error: ([new FileInCollection] did not complete its protocol (found: State{FileInCollection, Init}))
  public static void main1(String[] args) {
    List<FileInCollection> list = new LinkedList<>();
    :: warning: (list: Shared{java.util.LinkedList})
    list.add(new FileInCollection());

    :: warning: (list: Shared{java.util.LinkedList})
    for (FileInCollection f : list) {
      :: warning: (f: Shared{java.lang.Object} | Null)
      :: error: (Cannot call state on Shared{java.lang.Object})
      :: error: (Cannot call state on null)
      switch (f.state()) {
        :: warning: (FileState.INIT: Shared{FileState})
        case INIT:
          :: warning: (f: Bottom)
          switch (f.open()) {
            :: warning: (FileStatus.OK: Shared{FileStatus})
            case OK:
              :: warning: (f: Bottom)
              while (f.hasNext()) {
                :: warning: (f: Bottom)
                f.read();
              }
              :: warning: (f: Bottom)
              f.close();
              break;
            :: warning: (FileStatus.ERROR: Shared{FileStatus})
            case ERROR:
              break;
          }
          break;
        :: warning: (FileState.OPEN: Shared{FileState})
        case OPEN:
        :: warning: (FileState.READ: Shared{FileState})
        case READ:
          :: warning: (f: Bottom)
          while (f.hasNext()) {
            :: warning: (f: Bottom)
            f.read();
          }
          :: warning: (f: Bottom)
          f.close();
          break;
        :: warning: (FileState.CLOSE: Shared{FileState})
        case CLOSE:
          :: warning: (f: Bottom)
          f.close();
          break;
      }
    }
  }*/

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
