import jatyc.lib.Typestate;

@Typestate("Item.protocol")
public class Item {

  private int state;

  public Item() {
    this.state = 0;
  }

  public int getState() {
    return this.state;
  }

  public void changeState() {
    this.state = 1;
  }
}
