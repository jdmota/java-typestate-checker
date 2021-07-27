## Mungo's output

```

Auction.java: 23-12: Semantic Error
		Object reference is used uninitialised.

Auction.java: 30-17: Semantic Error
		Object reference is used uninitialised.

Auction.java: 30-17: Semantic Error
		Object reference is used uninitialised.

Auction.java: 30-17: Semantic Error
		Object reference is used uninitialised.```

## Our tool's output

```
Auction.java:31: error: Cannot call [getId] on Shared{Client}
      System.out.println(client.getId());
                                     ^
Auction.java:18: error: Cannot call [getBid] on Shared{Client}
           (hBidder != clientId && val > clients[hBidder].getBid())) ?
                                                                ^
Auction.java:18: error: Cannot call getBid on null
           (hBidder != clientId && val > clients[hBidder].getBid())) ?
                                                         ^
Auction.java:13: error: Incompatible parameter: cannot cast from State{Client, Running} to Shared{Client} | Null
      clients[i] = new Client(i);
                   ^
Auction.java:31: error: Cannot call getId on null
      System.out.println(client.getId());
                               ^
Auction.java:24: error: Cannot call bid on null
    c.bid(val);
     ^
Auction.java:24: error: Cannot call [bid] on Shared{Client}
    c.bid(val);
         ^
7 errors```
