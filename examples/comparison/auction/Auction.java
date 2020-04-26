import mungo.lib.Typestate;

@Typestate("AuctionProtocol")
public class Auction {
  private int hBidder;
  private Client[] clients;
  private boolean ended;
  public Auction(int maxClients) {
    hBidder = -1;
    clients = new Client[maxClients];
    ended = false;
    for (int i = 0; i < maxClients; i++)
      clients[i] = new Client(i);
  }
  public Boolean canBid(int clientId, double val) {
    return 0 <= clientId && clientId < clients.length &&
           (hBidder == -1 ||
           (hBidder != clientId && val > clients[hBidder].getBid())) ?
              Boolean.True :
              Boolean.False;
  }
  public void bid(int clientId, double val) {
    clients[clientId].bid(val);
    hBidder = clientId;
  }
  // There is an error here, clients are not being closed!
  public int finish() {
    ended = true;
    for (Client client : clients) {
      System.out.println(client.getId());
      // client.close();
    }
    return hBidder;
  }
}
