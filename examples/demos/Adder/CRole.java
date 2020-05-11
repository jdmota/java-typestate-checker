package demos.Adder;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.ServerSocket;
import java.net.Socket;

@Typestate("CProtocol")
public class CRole{
    private BufferedReader socketSIn = null;
    private PrintWriter socketSOut = null;
    public CRole() {
        // Bind the sockets
        ServerSocket serverS = null;
        // Connecting to the server
        try {
            // Create the sockets
            serverS = new ServerSocket(20000);
        } catch(IOException e) {
            System.out.println("Unable to listen on ports");
            System.exit(-1);
        }

        // Accept a client connection
        Socket socketS = null;
        try {
            System.out.println("Accepting...");
            socketS = serverS.accept();
            System.out.println("S accepted");
        }
        catch (IOException e) {
            System.out.println("Accept failed");
            System.exit(-1);
        }
        // Create the read and write streams
        try {
            socketSIn = new BufferedReader(new InputStreamReader(socketS.getInputStream()));
            socketSOut = new PrintWriter(socketS.getOutputStream(), true);
        }
        catch (IOException e) {
            System.out.println("Read failed");
            System.exit(-1);
        }

    }

    public void send_ADDToS() {
        this.socketSOut.println("ADD");
    }

    public void send_BYEToS() {
        this.socketSOut.println("BYE");
    }

    public void send_AddintToS(Integer payload) {
        this.socketSOut.println(payload);
    }

    public Integer receive_ResintFromS() {
        String line = "";
        try {
            line = this.socketSIn.readLine();
        } catch(IOException e) {
            System.out.println("Input/Outpur error. " + e.getMessage());
            System.exit(-1);
        }
        return Integer.parseInt(line);
    }

    public void send_ByeToS() {
        // Nothing to be sent
    }

}
