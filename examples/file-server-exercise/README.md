# File server

## Description

We want to develop a file server so that clients can request files from it.

The communication will be implemented using `java.net.Socket` classes and will follow a specific byte protocol:

1. The client sends the string `"REQUEST\n"` to start a request
2. The client sends the name of the file followed by `"\n"`
3. If the file exists, the server responds by sending to the client each one of the bytes of the file
4. If the file does not exist, or when the end of the file is reached, the server sends the `0` byte
5. After the client receives the `0` byte, it can start a new request (see steps 1 and 2), or send the string `"CLOSE\n"` to finish the protocol

## Assignment (Part 1)

Design two protocols to be used with the [JaTyC tool](https://github.com/jdmota/java-typestate-checker): one for a `FileClient` class and one for a `FileServer` class, so that correct correct usages of the protocols imply that both parties will communicate correctly according to the description above. The server's protocol should be specified so that each byte of a file is sent at a time (i.e. creating a method that accepts a string with the full contents of the file at once is not the assignment). In the same manner, the client's protocol should have methods to retrieve the contents of the file one by one.

After specifying the protocols (i.e. typestates), implement the classes. Some code skeletons are provided. Look for "TODO" comments to get hints of what needs to be completed. You may assume that the socket communication is always stable. In other words, if the above protocol is followed, assume that reading and writing to the socket's input and output streams will not result in exceptions.

## Assignment (Part 2)

Create a `FileClient2` class that extends `FileClient` with a method to retrieve the file contents line by line instead of byte by byte. For this part of the assignment, you need to create a new method and protocol for `FileClient2`, correctly extending the protocol of `FileClient`. The `FileServer` class should remain as implemented in Part 1.

## Evaluation

To ensure the correct implementation of the classes:

- Make sure you have JDK 11 installed. We recommend [Eclipse Temurin](https://adoptium.net/temurin/releases/?version=11).
- Execute the JaTyC tool. No output is expected, meaning that no errors were found.
- Execute `java FileServer` to start the server and wait for client requests.
- Execute `java FileClient` to start a client communicating with the server.

After the client gracefully terminates, you may terminate the process started with `java FileServer` by hitting CTRL+C.
