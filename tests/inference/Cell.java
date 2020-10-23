import org.checkerframework.checker.mungo.lib.MungoTypestate;

@MungoTypestate("Cell.protocol")
public class Cell {

  private String item;

  public Cell() {
    this.item = null;
  }

  public void setItem(String item) {
    this.item = item;
  }

  public String getItem() {
    return item;
  }
}
