import org.checkerframework.checker.mungo.lib.MungoTypestate;

import java.util.List;
import java.util.LinkedList;

@MungoTypestate("FileInCollection.protocol")
class FileInCollection {

  public enum State {
    INIT, OPEN, READ, CLOSE
  }

  public enum Status {
    OK, ERROR
  }

  public State state() {
    return State.CLOSE;
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

    List<FileInCollection> list = new LinkedList<>();
    list.add(new FileInCollection());

    for (FileInCollection f : list) {
      // :: warning: (f: FileInCollection{Init|Open|Read|Close})
      switch (f.state()) {
        case INIT:
          // :: warning: (f: FileInCollection{Init})
          switch (f.open()) {
            case OK:
              // :: warning: (f: FileInCollection{Open})
              while (f.hasNext()) {
                // :: warning: (f: FileInCollection{Read})
                f.read();
              }
              // :: warning: (f: FileInCollection{Close})
              f.close();
              break;
            case ERROR:
              break;
          }
          break;
        case OPEN:
        case READ:
          // :: warning: (f: FileInCollection{Read|Open})
          while (f.hasNext()) {
            // :: warning: (f: FileInCollection{Read})
            f.read();
          }
          // :: warning: (f: FileInCollection{Close})
          f.close();
          break;
        case CLOSE:
          // :: warning: (f: FileInCollection{Close})
          f.close();
          break;
      }
    }

  }

}
