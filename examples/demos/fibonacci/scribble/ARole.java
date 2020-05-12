package demos.fibonacci.scribble;

/**
 * Generated by StMungo
 * Wed Apr 08 17:25:52 BST 2020
 */

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.ServerSocket;
import java.net.Socket;

@Typestate("AProtocol")
public class ARole {
    private BufferedReader socketBIn = null;
    private PrintWriter socketBOut = null;

    public ARole() {
        // Bind the sockets
        ServerSocket serverB = null;
        // Connecting to the server
        try {
            // Create the sockets
            serverB = new ServerSocket(20000);
        } catch (IOException e) {
            System.out.println("Unable to listen on ports");
            System.exit(-1);
        }

        // Accept a client connection
        Socket socketB = null;
        try {
            System.out.println("Accepting...");
            socketB = serverB.accept();
            System.out.println("B accepted");
        } catch (IOException e) {
            System.out.println("Accept failed");
            System.exit(-1);
        }
        // Create the read and write streams
        try {
            socketBIn = new BufferedReader(new InputStreamReader(socketB.getInputStream()));
            socketBOut = new PrintWriter(socketB.getOutputStream(), true);
        } catch (IOException e) {
            System.out.println("Read failed");
            System.exit(-1);
        }

    }

    public void send_FIBONACCIToB() {
        this.socketBOut.println("FIBONACCI");
    }

    public void send_ENDToB() {
        this.socketBOut.println("END");
    }

    public void send_fibonacciLongToB(Long payload) {
        this.socketBOut.println(payload);
    }

    public Long receive_fibonacciLongFromB() {
        String line = "";
        try {
            line = this.socketBIn.readLine();
        } catch (IOException e) {
            System.out.println("Input/Outpur error. " + e.getMessage());
            System.exit(-1);
        }
        // Perform a cast of line to the appropriate type and then return it
        return Long.parseLong(line);
    }

    public void send_endToB() {
        // Nothing to be sent
    }

}