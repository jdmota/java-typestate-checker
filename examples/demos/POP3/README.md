POP3 (Post Office Protocol Version 3) is a protocol that allows an email client to retrieve messages from a server. 
This implementation is based on RFC 1939, the official specification of the protocol.

The protocol starts with the client connecting to the server and the server authenticating the connection. The client then has the choice to either submit a username to log into a mailbox, or to end the authorization. Upon receiving the username, the server has the choice to accept the username or to send an error message to the client, for example if the username does not exist. After the username has been accepted, the client is then required to send a password or to end the authorization. If the password is accepted, the transaction stage begins. In the transaction stage, the client has a choice of various commands: the diagram shows STAT (mailbox statistics) and RETR (retrieve a message). Some of these requests involve a choice at the server side to either fulfil the request or to send an error message. Alternatively the client can also choose to end the transaction. 

The folder contains an implementation of a POP3 client based on a scribble specification.
