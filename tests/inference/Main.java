import org.checkerframework.checker.mungo.MungoUtils;

public class Main {

  /*public static void main(String args[]) {
    // access(cell, f1) && access(cell.item, f2) && access(item, f3)
    // typeof(cell, t1) && typeof(cell.item, t2) && typeof(item, t3)
    Cell cell;
    // f4 = 1
    // access(cell, f4) && access(cell.item, f5) && access(item, f6)
    // typeof(cell, t4) && typeof(cell.item, t5) && typeof(item, t6)

    // f4 = f7

    // f7 = 1
    // access(cell, f7) && access(cell.item, f8) && access(item, f9)
    cell = new Cell();
    // access(cell, f10) && access(cell.item, f11) && access(item, f12)

    // f13 > 0
    // access(cell, f13) && access(cell.item, ?) && access(item, ?)
    // typeof(cell, T) && T <: State "NoItem" | State "OneItem"
    cell.setItem("Hello World!");
    // access(cell, ?) && access(cell.item, ?) && access(item, ?)

    // access(cell, ?) && access(cell.item, ?) && access(item, ?)
    String item;
    // access(cell, ?) && access(cell.item, ?) && access(item, ?)


    // eq(item, cell.item), eq(item, item2)
    // eq(cell.item, item2)







    access(item.0, f1) && access(cell.item.0, f2)
    eq_1(item, cell.item) == false

    item = cell.item;




    access(item.0, f3) && access(cell.item.0, f4) && access(item2.0, f5)
    eq_2(item, cell.item) && eq_2(item2, item)


    access(item.0, f6) && access(cell.item.0, f7) && access(item2.0, f8)
    eq_3(item, cell.item) && eq_2(item2, item)


      f3 + f4 + f5 = f6 + f7 + f8
      (f3 - f6) + (f4 - f7) + (f5 - f8) = 0


    item:      (if eq_3(item, item)      then (f3 - f6) else 0) +
               (if eq_3(item, cell.item) then (f4 - f7) else 0) +
               (if eq_3(item, item2)     then (f5 - f8) else 0) +
          = 0


    cell.item: (if eq_3(cell.item, cell.item) then (f4 - f6) else 0) + (if eq_3(cell.item, item) then (f3 - f5) else 0) = 0


    item2: (if eq_3(cell.item, cell.item) then (f4 - f6) else 0) + (if eq_3(cell.item, item) then (f3 - f5) else 0) = 0



  }*/

  public static void main1() {
    Cell cell = new Cell();
    cell.setItem(new Item());

    Item item = cell.getItem();

    item.changeState();

    // TODO since the getItem() assumes that the item is in state S0|S1,
    // and since eq(item, cell.item) is not tracked
    // the second getItem() call will not work since it wont know in which state the item is

    Item item2 = cell.getItem();

    //item2.changeState();
  }

  /*public static void main2() {
    Cell c = new Cell();
    c.setItem(new Item());

    Item item = c.getItem();

    Thread t = new Thread(() -> {
      item.changeState();
    });

    t.start();
    t.join();

    Item item2 = c.getItem();
    item2.changeState();
  }*/

  /*public static void main3() {
    Cell c = new Cell();
    c.setItem(new Item());

    Item item = c.getItem();

    Thread t = new Thread(() -> {
      item.changeState();
    });

    t.start();

    Item item2 = c.getItem();
    item2.changeState();

    t.join();
  }*/

}
