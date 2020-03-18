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
    list.add(new FileInCollection()); // TODO this should not error, List has no protocol

    for (FileInCollection f : list) {
      // TODO what if "f" is in the end state?
      // Or assume that the only possible states are those that have transitions?
      // And error when "end" is a possible state? Saying that the object might be dropped or not?

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
