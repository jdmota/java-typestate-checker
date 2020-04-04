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

    // :: error: (enhancedfor.type.incompatible)
    for (FileInCollection f : list) {
      switch (f.state()) {
        case INIT:
          switch (f.open()) {
            case OK:
              while (f.hasNext()) {
                f.read();
              }
              f.close();
              break;
            case ERROR:
              break;
          }
          break;
        case OPEN:
        case READ:
          while (f.hasNext()) {
            f.read();
          }
          f.close();
          break;
        case CLOSE:
          f.close();
          break;
      }
    }

  }

}
