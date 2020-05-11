Bookstore:
- A basic communication protocol that describes a multiparty
  session protocol.

The protocol:
- Buyer 1 selects a book and it is informed for its price from the book Seller
- Buyer 1 then quotes a contribution to Buyer 2.
- If Buyer 2 agrees on the purchase, both buyers send their contribution to
  the Seller to buy the book.
- On a different case the protocol terminates

Implementation: A distributed execution of three processes that implement the roles of the protocol and exchange protocol messages via sockets