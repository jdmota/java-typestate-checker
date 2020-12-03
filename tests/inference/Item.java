import org.checkerframework.checker.mungo.lib.MungoTypestate;

@MungoTypestate("Item.protocol")
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
