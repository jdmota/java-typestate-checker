//package demos.http;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;

public class CMain {
    public static String safeRead(BufferedReader readerC) {
        String readline = "";
        try {
            readline = readerC.readLine();
        } catch (IOException e) {
            System.out.println("Input/Output error, unable to read");
            System.exit(-1);
        }
        return readline;
    }

    public static void main(String[] args) {
        // Create the current role
        CRole currentC = new CRole();
        // readerC can be used to input strings, and then use them in send method invocation
        BufferedReader readerC = new BufferedReader(new InputStreamReader(System.in));
        // Method invocation follows the C typestate
        System.out.print("Choose a label among [REQUEST]: ");
        String sread1 = safeRead(readerC);
        switch (sread1) {
            case "REQUEST":
                currentC.send_REQUESTToS();
                System.out.print("Send to S: ");
                String payload1 = safeRead(readerC);
                currentC.send_requestStrToS(payload1);
                _X:
                do {
                    System.out.print("Choose a label among [HOST, USERA, ACCEPTT, ACCEPTL, ACCEPTE, DNT, CONNECTION, UPGRADEIR, COOKIE, BODY]: ");
                    String sread2 = safeRead(readerC);
                    switch (sread2) {
                        case "HOST":
                            currentC.send_HOSTToS();
                            System.out.print("Send to S: ");
                            String payload2 = safeRead(readerC);
                            currentC.send_hostStrToS(payload2);
                            continue _X;
                        case "USERA":
                            currentC.send_USERAToS();
                            System.out.print("Send to S: ");
                            String payload3 = safeRead(readerC);
                            currentC.send_userAStrToS(payload3);
                            continue _X;
                        case "ACCEPTT":
                            currentC.send_ACCEPTTToS();
                            System.out.print("Send to S: ");
                            String payload4 = safeRead(readerC);
                            currentC.send_acceptTStrToS(payload4);
                            continue _X;
                        case "ACCEPTL":
                            currentC.send_ACCEPTLToS();
                            System.out.print("Send to S: ");
                            String payload5 = safeRead(readerC);
                            currentC.send_acceptLStrToS(payload5);
                            continue _X;
                        case "ACCEPTE":
                            currentC.send_ACCEPTEToS();
                            System.out.print("Send to S: ");
                            String payload6 = safeRead(readerC);
                            currentC.send_acceptEStrToS(payload6);
                            continue _X;
                        case "DNT":
                            currentC.send_DNTToS();
                            System.out.print("Send to S: ");
                            Integer payload7 = Integer.parseInt(safeRead(readerC));
                            currentC.send_DNTIntToS(payload7);
                            continue _X;
                        case "CONNECTION":
                            currentC.send_CONNECTIONToS();
                            System.out.print("Send to S: ");
                            String payload8 = safeRead(readerC);
                            currentC.send_connectionStrToS(payload8);
                            continue _X;
                        case "UPGRADEIR":
                            currentC.send_UPGRADEIRToS();
                            System.out.print("Send to S: ");
                            String payload9 = safeRead(readerC);
                            currentC.send_upgradeIRStrToS(payload9);
                            continue _X;
                        case "COOKIE":
                            currentC.send_COOKIEToS();
                            System.out.print("Send to S: ");
                            String payload10 = safeRead(readerC);
                            currentC.send_cookieStrToS(payload10);
                            continue _X;
                        case "BODY":
                            currentC.send_BODYToS();
                            System.out.print("Send to S: ");
                            String payload11 = safeRead(readerC);
                            currentC.send_bodyStrToS(payload11);
                            break _X;
                    }
                } while (true);
                break;
        }
        String payload12 = currentC.receive_httpvStrFromS();
        System.out.println("Received HTTPV from S: " + payload12);
        switch (currentC.receive_Choice1LabelFromS()) {
            case _200:
                String payload13 = currentC.receive_200StrFromS();
                System.out.println("Received 200 from S: " + payload13);
                break;
            case _404:
                String payload14 = currentC.receive_404StrFromS();
                System.out.println("Received 404 from S: " + payload14);
                break;
        }
        _Y:
        do {
            switch (currentC.receive_Choice2LabelFromS()) {
                case DATE:
                    String payload15 = currentC.receive_dateStrFromS();
                    System.out.println("Received Date from S: " + payload15);
                    continue _Y;
                case SERVER:
                    String payload16 = currentC.receive_serverStrFromS();
                    System.out.println("Received Server from S: " + payload16);
                    continue _Y;
                case STRICTTS:
                    String payload17 = currentC.receive_strictTSStrFromS();
                    System.out.println("Received Strict-Transport-Security from S: " + payload17);
                    continue _Y;
                case LASTM:
                    String payload18 = currentC.receive_lastMStrFromS();
                    System.out.println("Received Last-Modified from S: " + payload18);
                    continue _Y;
                case ETAG:
                    String payload19 = currentC.receive_eTagStrFromS();
                    System.out.println("Received ETag from S: " + payload19);
                    continue _Y;
                case ACCEPTR:
                    String payload20 = currentC.receive_acceptRStrFromS();
                    System.out.println("Received Accept-Ranges from S: " + payload20);
                    continue _Y;
                case CONTENTL:
                    Integer payload21 = currentC.receive_contentLIntFromS();
                    System.out.println("Received Content-Length from S: " + payload21);
                    continue _Y;
                case VARY:
                    String payload22 = currentC.receive_varyStrFromS();
                    System.out.println("Received Vary from S: " + payload22);
                    continue _Y;
                case CONTENTT:
                    String payload23 = currentC.receive_contentTStrFromS();
                    System.out.println("Received Content-Type from S: " + payload23);
                    continue _Y;
                case VIA:
                    String payload24 = currentC.receive_viaStrFromS();
                    System.out.println("Received Via from S: " + payload24);
                    continue _Y;
                case CACHEC:
                    String payload25 = currentC.receive_cacheCStrFromS();
                    System.out.println("Received Cache-Control from S: " + payload25);
                    continue _Y;
                case P3P:
                    String payload26 = currentC.receive_p3pStrFromS();
                    System.out.println("Received P3P from S: " + payload26);
                    continue _Y;
                case XXSSPROTECTION:
                    String payload27 = currentC.receive_xxssProtectionStrFromS();
                    System.out.println("Received X-XSS-Protection from S: " + payload27);
                    continue _Y;
                case XFRAMEOPT:
                    String payload28 = currentC.receive_xframeOptStrFromS();
                    System.out.println("Received X-Frame-Options from S: " + payload28);
                    continue _Y;
                case SETCOOKIE:
                    String payload29 = currentC.receive_setCookieStrFromS();
                    System.out.println("Received Set-Cookie from S: " + payload29);
                    continue _Y;
                case TRANSFERE:
                    String payload30 = currentC.receive_transferEStrFromS();
                    System.out.println("Received Transfer-Encoding from S: " + payload30);
                    continue _Y;
                case EXPIRES:
                    String payload31 = currentC.receive_expiresStrFromS();
                    System.out.println("Received Expires from S: " + payload31);
                    continue _Y;
                case BODY:
                    String payload32 = currentC.receive_bodyStrFromS();
                    System.out.println("Received Body from S: " + payload32);
                    break _Y;
            }
        } while (true);
    }
}
