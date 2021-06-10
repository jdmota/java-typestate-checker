public class Main {

  // :: error: ([list] did not complete its protocol (found: State{LinkedList, State0}))
  public static void main(String[] args) {
    LinkedList list = new LinkedList();
    Item item = new Item();
    // :: warning: (list: State{LinkedList, State0})
    // :: warning: (item: State{Item, State0})
    list.add(item);
  }

}
