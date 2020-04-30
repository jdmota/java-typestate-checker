## Original Mungo's output

```

Auction.java: 29-17: Semantic Error
		Object reference is used uninitialised.

Auction.java: 29-17: Semantic Error
		Object reference is used uninitialised.

Auction.java: 29-17: Semantic Error
		Object reference is used uninitialised.```

## Mungo Checker's output

```
Auction.java:13: error: [Cannot override because object has not ended its protocol] (Cannot override because object has not ended its protocol)
      clients[i] = new Client(i);
             ^
Auction.java:29: error: [Object did not complete its protocol. Type: ClientProtocol{Running}] (Object did not complete its protocol. Type: ClientProtocol{Running})
    for (Client client : clients) {
                ^
2 errors```
