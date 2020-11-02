import org.checkerframework.checker.mungo.MungoUtils;

public class Main {

  /*public static void main1() {
    Cell cell = new Cell();
    cell.setItem(new Item());

    Item item = cell.getItem();

    item.changeState();

    Item item2 = cell.getItem();

    item2.changeState();
  }*/

  /*public static void main2() {
    Cell cell = new Cell();
    cell.setItem(new Item());

    Item item = cell.getItem();

    Thread t = new Thread(() -> {
      item.changeState();
    });

    t.start();
    t.join();

    Item item2 = cell.getItem();
    item2.changeState();
  }*/

  public static void main3() {
    Cell cell = new Cell();
    cell.setItem(new Item());

    Item item = cell.getItem();

    Thread t = new Thread(() -> {
      item.changeState();
    });

    t.start();

    Item item2 = cell.getItem();
    item2.changeState();

    t.join();
  }

}
