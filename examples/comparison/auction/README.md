## Mungo's output

```

Auction.java: 29-17: Semantic Error
		Object reference is used uninitialised.

Auction.java: 29-17: Semantic Error
		Object reference is used uninitialised.

Auction.java: 29-17: Semantic Error
		Object reference is used uninitialised.```

## Our tool's output

```
Auction.java:13: error: [Cannot override because object has not ended its protocol. Type: State "Running" | Ended | Moved] (Cannot override because object has not ended its protocol. Type: State "Running" | Ended | Moved)
      clients[i] = new Client(i);
             ^
Auction.java:18: error: [Cannot call getBid on ended protocol, on moved value] (Cannot call getBid on ended protocol, on moved value)
           (hBidder != clientId && val > clients[hBidder].getBid())) ?
                                                                ^
Auction.java:23: error: [Cannot call bid on ended protocol, on moved value] (Cannot call bid on ended protocol, on moved value)
    clients[clientId].bid(val);
                         ^
Auction.java:29: error: [Object did not complete its protocol. Type: State "Running"] (Object did not complete its protocol. Type: State "Running")
    for (Client client : clients) {
                ^
Auction.java:29: error: [enhancedfor.type.incompatible] incompatible types in enhanced for loop.
    for (Client client : clients) {
                         ^
  found   : NoProtocol Client
  required: State "Running" Client
5 errors```
