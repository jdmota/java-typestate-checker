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

  /*public static void main3() {
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
  }*/

  /*public static void main4() {
    Cell cell = new Cell();
    cell.setItem(new Item());

    Item item = cell.getItem();

    Thread t1 = new Thread(() -> {
      item.changeState();
    });

    Thread t2 = new Thread(() -> {
      item.changeState();
    });

    t1.start();
    t1.join();

    t2.start();
    t2.join();
  }*/

  /*public static void main5() {
    Cell cell = new Cell();
    cell.setItem(new Item());

    Item item = cell.getItem();

    Thread t1 = new Thread(() -> {
      item.changeState();
    });

    Thread t2 = new Thread(() -> {
      item.changeState();
    });

    t1.start();
    t2.start();

    t1.join();
    t2.join();
  }*/

  public static void main6() {
    Cell cell = new Cell();
    cell.setItem(new Item());

    Item item = cell.getItem();

    Thread t1 = new Thread(() -> {
      item.getState();
    });

    Thread t2 = new Thread(() -> {
      item.getState();
    });

    t1.start();
    t2.start();

    t1.join();
    t2.join();
  }

}
