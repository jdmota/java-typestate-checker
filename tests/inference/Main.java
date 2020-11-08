import org.checkerframework.checker.mungo.MungoUtils;

public class Main {

  public static void main1() {
    Cell cell = new Cell();
    cell.setItem(new Item());

    Item item = cell.getItem();
    item.changeState();

    Item item2 = cell.getItem();
    item2.changeState();
  }

  /*
  acc(item,1) && typeof(item,Object)
  acc(item.state.0,1) &&

    Weird that part of the permission acc(node(new Item())[152].state.0,1) was lost...
    ----
    acc(cell,1) && acc(cell.0,1) && typeof(cell,Cell{NoItem})
    acc(cell.item,1) && acc(cell.item.0,1) && typeof(cell.item,Null)
    acc(node(item2.changeState())[279],1) && acc(node(item2.changeState())[279].0,1) && typeof(node(item2.changeState())[279],Primitive)
    acc(node(new Item())[152],1) && acc(node(new Item())[152].0,1) && typeof(node(new Item())[152],Item{S0})
    acc(node(new Item())[152].state,1) && acc(node(new Item())[152].state.0,1) && typeof(node(new Item())[152].state,Primitive)
    acc(node(item.changeState())[219],1) && acc(node(item.changeState())[219].0,1) && typeof(node(item.changeState())[219],Primitive)
    acc(node(new Cell())[123],1) && typeof(node(new Cell())[123],Object | Null)
    acc(node(cell.getItem())[194],1) && acc(node(cell.getItem())[194].0,1) &&
    acc(node(cell.setItem(new Item()))[151],1) && acc(node(cell.setItem(new Item()))[151].0,1) && typeof(node(cell.setItem(new Item()))[151],Primitive)
    acc(node(cell.getItem())[253],1) && acc(node(cell.getItem())[253].0,1) &&
    acc(#ret,1) && acc(#ret.0,1) && typeof(#ret,Primitive)

    --> cell.setItem(new Item())

    acc(cell,1) && acc(cell.0,1) && typeof(cell,Cell{OneItem})
    acc(cell.item,1) && acc(cell.item.0,5/133) && typeof(cell.item,Item{S0})
    acc(cell.item.state,1/5320) && typeof(cell.item.state,Primitive)
    acc(node(item2.changeState())[279],1) && acc(node(item2.changeState())[279].0,1) && typeof(node(item2.changeState())[279],Primitive)
    acc(node(new Item())[152],1) && acc(node(new Item())[152].0,128/133) && typeof(node(new Item())[152],Item{S0})
    acc(node(new Item())[152].state,5319/5320) && acc(node(new Item())[152].state.0,1/5320) && typeof(node(new Item())[152].state,Primitive)
    acc(node(item.changeState())[219],1) && acc(node(item.changeState())[219].0,1) && typeof(node(item.changeState())[219],Primitive)
    acc(node(new Cell())[123],1) && typeof(node(new Cell())[123],Object | Null)
    acc(node(cell.getItem())[194],1) && acc(node(cell.getItem())[194].0,1) &&
    acc(node(cell.setItem(new Item()))[151],1) && acc(node(cell.setItem(new Item()))[151].0,1) && typeof(node(cell.setItem(new Item()))[151],Primitive)
    acc(node(cell.getItem())[253],1) && acc(node(cell.getItem())[253].0,1) &&
    acc(#ret,1) && acc(#ret.0,1) && typeof(#ret,Primitive)
    eq(cell.item,node(new Item())[152]) &&
    ----
    */

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

  /*public static void main6() {
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
  }*/

}
