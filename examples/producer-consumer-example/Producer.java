import mungo.lib.Typestate;
import org.checkerframework.checker.jtc.lib.Nullable;

@Typestate("Producer.protocol")
public class Producer {
  private @Nullable Consumer consumer;

  public Producer() {
    this.consumer = null;
  }

  public void init(Consumer consumer) {
    this.consumer = consumer;
  }
  
  public void produce(String string) {
    this.consumer.consume(string);
  }
}
