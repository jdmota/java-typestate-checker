import jatyc.lib.Typestate;

@Typestate("Cell.protocol")
public class Cell {

  private Item item;

  public Cell() {
    this.item = null;
  }

  public void setItem(Item item) {
    this.item = item;
  }

  public Item getItem() {
    return item;
  }
}
