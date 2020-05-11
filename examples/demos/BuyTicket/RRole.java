package demos.BuyTicket;

//import mungo.lib.Typestate;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.ServerSocket;
import java.net.Socket;

@Typestate("RProtocol")
public class RRole {
    private BufferedReader socketAIn = null;
    private PrintWriter socketAOut = null;
    private BufferedReader socketFIn = null;
    private PrintWriter socketFOut = null;

    public RRole() {
        // Bind the sockets
        ServerSocket serverA = null;
        ServerSocket serverF = null;
        // Connecting to the server
        try {// Create the sockets
            serverA = new ServerSocket(20001);
            serverF = new ServerSocket(20000);
        } catch (IOException e) {
            System.out.println("Unable to listen on ports");
            System.exit(-1);
        }
        // Accept a client connection
        Socket socketA = null;
        Socket socketF = null;
        try {
            System.out.println("Accepting...");
            socketA = serverA.accept();
            System.out.println("Agent accepted");
            System.out.println("Accepting...");
            socketF = serverF.accept();
            System.out.println("Finance accepted");
        } catch (IOException e) {
            System.out.println("Accept failed");
            System.exit(-1);
        }
        // Create the read and write streams
        try {
            socketAIn = new BufferedReader(new InputStreamReader(socketA.getInputStream()));
            socketAOut = new PrintWriter(socketA.getOutputStream(), true);
            socketFIn = new BufferedReader(new InputStreamReader(socketF.getInputStream()));
            socketFOut = new PrintWriter(socketF.getOutputStream(), true);
        } catch (IOException e) {
            System.out.println("Read failed");
            System.exit(-1);
        }
    }

    public void send_requestStringToA(String payload) {
        this.socketAOut.println(payload);
    }

    public int receive_quoteintFromA() {
        String line = "";
        try {
            line = this.socketAIn.readLine();
        } catch (IOException e) {
            System.out.println("Input/Output error.");
            System.exit(-1);
        }
        return Integer.parseInt(line);
    }

    public void send_checkintToF(int payload) {
        this.socketFOut.println(payload);
    }

    public Choice1 receive_Choice1LabelFromF() {
        String stringLabelChoice1 = "";
        try {
            stringLabelChoice1 = this.socketFIn.readLine();
        } catch (IOException e) {
            System.out.println("Input/Output error, unable to get label");
            System.exit(-1);
        }
        switch (stringLabelChoice1) {
            case "APPROVE":
                return Choice1.APPROVE;
            case "REFUSE":
            default:
                return Choice1.REFUSE;
        }
    }

    public int receive_approveintFromF() {
        String line = "";
        try {
            line = this.socketFIn.readLine();
        } catch (IOException e) {
            System.out.println("Input/Output error.");
            System.exit(-1);
        }
        return Integer.parseInt(line);
    }

    public String receive_ticketStringFromA() {
        String line = "";
        try {
            line = this.socketAIn.readLine();
        } catch (IOException e) {
            System.out.println("Input/Output error.");
            System.exit(-1);
        }
        return line;
    }

    public String receive_refuseStringFromF() {
        String line = "";
        try {
            line = this.socketFIn.readLine();
        } catch (IOException e) {
            System.out.println("Input/Output error.");
            System.exit(-1);
        }
        return line;
    }
}
