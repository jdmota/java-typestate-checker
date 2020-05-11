package demos.BuyTicket;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;

public class FMain {
    public static String safeRead(BufferedReader readerF) {
        String readline = "";
        try {
            readline = readerF.readLine();
        } catch (IOException e) {
            System.out.println("Input/Output error, unable to read");
            System.exit(-1);
        }
        return readline;
    }

    public static void main(String[] args) {
        // Create the current role
        FRole currentF = new FRole();
        // readerF can be used to input strings, and then use them in send method invocation
        BufferedReader readerF = new BufferedReader(new InputStreamReader(System.in));
        // Method invocation follows the F typestate
        int payload1 = currentF.receive_checkintFromR();
        System.out.println("Received quote price from Researcher: £" + payload1);
        System.out.print("Choose a label among [APPROVE, REFUSE]: ");
        switch (safeRead(readerF)) {
            case "APPROVE":
                currentF.send_APPROVEToR();
                System.out.print("Send approval code to Researcher: ");
                int payload2 = Integer.parseInt(safeRead(readerF));
                currentF.send_approveintToR(payload2);
                System.out.print("Send approval code to Agent: ");
                int payload3 = Integer.parseInt(safeRead(readerF));
                currentF.send_approveintToA(payload3);
                int payload4 = currentF.receive_invoiceintFromA();
                System.out.println("Received invoice from Agent: " + payload4);
                System.out.print("Send payment to Agent: £");
                int payload5 = Integer.parseInt(safeRead(readerF));
                currentF.send_paymentintToA(payload5);
                System.out.println("\n	----TRANSACTION COMPLETE----	");
                break;
            case "REFUSE":
                currentF.send_REFUSEToR();
                System.out.print("Send travel refusal to Researcher: ");
                String payload6 = safeRead(readerF);
                currentF.send_refuseStringToR(payload6);
                System.out.print("Send travel refusal to Agent: ");
                String payload7 = safeRead(readerF);
                currentF.send_refuseStringToA(payload7);
                System.out.println("\n	----TRANSACTION COMPLETE----	");
                break;
        }
    }
}
