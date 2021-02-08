import mungo.lib.Typestate;

@Typestate("Consumer.protocol")
public class Consumer {
  public void consume(String string) {
    System.out.println(string);
  }
}
