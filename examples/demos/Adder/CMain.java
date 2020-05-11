package demos.Adder;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;

public class CMain {
    public static String safeRead(BufferedReader readerC) {
        String readline = "";
        try {
            readline = readerC.readLine();
        } catch(IOException e) {
            System.out.println("Input/Output error, unable to read");
            System.exit(-1);
        }
        return readline;
    }

    public static void main(String[] args) {
        // Create the current role
        CRole currentC =  new CRole();
        // readerC can be used to input strings, and then use them in send method invocation
        BufferedReader readerC = new BufferedReader(new InputStreamReader(System.in));
        // Method invocation follows the C typestate
        _X: do{
            System.out.print("Choose a label among [ADD, BYE]: ");
            String sread1 = safeRead(readerC);
            switch(sread1){
                case "ADD":
                    currentC.send_ADDToS();
                    System.out.print("Send to S: ");
                    Integer payload1 = Integer.parseInt(safeRead(readerC));
                    currentC.send_AddintToS(payload1);
                    System.out.print("Send to S: ");
                    Integer payload2 = Integer.parseInt(safeRead(readerC));
                    currentC.send_AddintToS(payload2);
                    Integer payload3 = currentC.receive_ResintFromS();
                    System.out.println("Received from S: " + payload3);
                    continue _X;
                case "BYE":
                    currentC.send_BYEToS();
                    currentC.send_ByeToS();
                    break _X;
            }
        } while(true);
    }
}
