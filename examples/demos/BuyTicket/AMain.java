package demos.BuyTicket;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;

public class AMain {
    public static String safeRead(BufferedReader readerA) {
        String readline = "";
        try {
            readline = readerA.readLine();
        } catch (IOException e) {
            System.out.println("Input/Output error, unable to read");
            System.exit(-1);
        }
        return readline;
    }

    public static void main(String[] args) {
        // Create the current role
        ARole currentA = new ARole();
        // readerA can be used to input strings, and then use them in send method invocation
        BufferedReader readerA = new BufferedReader(new InputStreamReader(System.in));
        // Method invocation follows the A typestate
        String payload1 = currentA.receive_requestStringFromR();
        System.out.println("Received travel destination request from Researcher: " + payload1);
        System.out.print("Send quote price to Researcher: £");
        int payload2 = Integer.parseInt(safeRead(readerA));
        currentA.send_quoteintToR(payload2);
        switch (currentA.receive_Choice1LabelFromF()) {
            case APPROVE:
                int payload3 = currentA.receive_approveintFromF();
                System.out.println("Received approval code from Finance: " + payload3);
                System.out.print("Send ticket to Researcher: ");
                String payload4 = safeRead(readerA);
                currentA.send_ticketStringToR(payload4);
                System.out.print("Send invoice code to Finance: ");
                int payload5 = Integer.parseInt(safeRead(readerA));
                currentA.send_invoiceintToF(payload5);
                int payload6 = currentA.receive_paymentintFromF();
                System.out.println("Received payment from Finance: £" + payload6);
                System.out.println("\n	----TRANSACTION COMPLETE----	");
                break;
            case REFUSE:
                String payload7 = currentA.receive_refuseStringFromF();
                System.out.println("Received refusal from Finance: " + payload7);
                System.out.println("\n	----TRANSACTION COMPLETE----	");
                break;
        }
    }
}
