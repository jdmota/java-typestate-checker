public class Main {
  public static void main(String[] args) {
    Auction auction = new Auction(2);
    switch(auction.canBid(0, 5.0)){
      case True:
        auction.bid(1, 5.0);
        break;
      case False:
        break;
    }
    auction.finish();
  }
}
