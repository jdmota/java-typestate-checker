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


    // access(cell.item.0, f1) && access(item.0, f2)
    // eq_1(item, cell.item) == false
    item = cell.item;
    // access(cell.item.0, f3) && access(item.0, f4)
    // eq_2(item, cell.item) == true
    // f1 = f3 + f4


    // access(cell.item.0, f5) && access(item.0, f6)
    // f3 + f4 = f5 + f6
    // eq_3(item, cell.item) == eq_2(item, cell.item)
    item2 = item;


  }*/

  public static void main2(String args[]) {
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
