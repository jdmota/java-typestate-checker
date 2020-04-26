import mungo.lib.Typestate;

@Typestate("ClientProtocol")
public class Client {
  private final int id;
	private double bid;
	public Client(int id) {
    this.id = id;
		this.bid = 0.0;
	}
  public int getId() {
    return id;
  }
  public double getBid() {
    return bid;
  }
	public void bid(double newBid) {
    bid = newBid;
  }
  public void close() {
    // Free resources...
  }
}
