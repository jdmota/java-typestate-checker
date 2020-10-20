import org.checkerframework.checker.mungo.MungoUtils;

public class Main {

  public static void main(String args[]) {
    Cell cell = new Cell();
    cell.setItem("Hello World!");

    if (true) {

    } else {

    }

    MungoUtils.unpack(cell);
    String item = cell.getItem();

    System.out.println(item);
  }

}
