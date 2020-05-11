package demos.Bookstore;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;

public class SellerMain {
    public static String safeRead(BufferedReader readerSeller) {
        String readline = "";
        try {
            readline = readerSeller.readLine();
        } catch (IOException e) {
            System.out.println("Input/Output error, unable to read");
            System.exit(-1);
        }
        return readline;
    }

    public static void main(String[] args) {
        // Create the current role
        SellerRole currentSeller = new SellerRole();
        // readerSeller can be used to input strings, and then use them in send method invocation
        BufferedReader readerSeller = new BufferedReader(new InputStreamReader(System.in));
        // Method invocation follows the Seller typestate
        String payload1 = currentSeller.receive_bookStringFromBuyer1();
        System.out.println("Received book title from Buyer1: " + payload1);
        System.out.print("Send book price to Buyer1: £");
        int payload2 = Integer.parseInt(safeRead(readerSeller));
        currentSeller.send_bookintToBuyer1(payload2);
        switch (currentSeller.receive_Choice1LabelFromBuyer2()) {
            case AGREE:
                String payload3 = currentSeller.receive_agreeStringFromBuyer2();
                System.out.println("Received agreement message from Buyer2: " + payload3);
                int payload4 = currentSeller.receive_transferintFromBuyer1();
                System.out.println("Received transfer from Buyer1: £" + payload4);
                int payload5 = currentSeller.receive_transferintFromBuyer2();
                System.out.println("Received transfer from Buyer2: £" + payload5);
                System.out.println("\n---Transaction complete: book sold---");
                break;
            case QUIT:
                String payload6 = currentSeller.receive_quitStringFromBuyer2();
                System.out.println("Received quit message from Buyer2: " + payload6);
                System.out.println("\n---Transaction complete: no sale---");
                break;
        }
    }
}
