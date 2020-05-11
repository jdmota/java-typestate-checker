HTTP (HyperText Transfer Protocol) is the underlying data protocol used by the World Wide Web defining how messages are 
formatted and transmitted, and what actions servers and clients may take in response to various methods, such as GET, 
PUT or POST. An HTTP session is a sequence of network request-response transactions, initiated by the client sending a 
request over a TCP connection to a particular port of a server. Upon receiving the request, the server listening on that 
port sends back a status line, such as “HTTP/1.1 200 OK”, and a message of its own. The structure of the request and 
response messages exchanged is rich and complex, lending itself to be further specified through session types. 
Hence, the request and response can be broken down into sending and receiving a request line – request, followed by zero or more header-fields – host or usera 
terminated by a new-line. This fine grained representation of the protocol is made possible by the message being broken
 down via TCP bit streams, in a manner that is transparent to the parties involved.
 
 The folder contains an implementation of an HTTP client based on a scribble specification.
