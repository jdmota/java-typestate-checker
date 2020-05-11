//package demos.http;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.InetAddress;
import java.net.ServerSocket;
import java.net.Socket;

import mungo.lib.Typestate;
import org.checkerframework.checker.mungo.lib.MungoNullable;

@Typestate("CProtocol")
public class CRole {
    private @MungoNullable BufferedReader socketSIn = null;
    private @MungoNullable PrintWriter socketSOut = null;

    public CRole() {
        // Bind the sockets
        // Not used: ServerSocket serverS = null;
        // Connecting to the server
        InetAddress addr;
        @MungoNullable Socket socket = null;

        try {// Create the sockets
            addr = InetAddress.getByName("www.google.co.uk");
            socket = new Socket(addr, 80);
        } catch (IOException e) {
            System.out.println("Unable to listen on ports");
            System.exit(-1);
        }

        // Accept a client connection
        // Create the read and write streams
        try {
            socketSIn = new BufferedReader(new InputStreamReader(socket.getInputStream()));
            socketSOut = new PrintWriter(socket.getOutputStream(), true);
        } catch (IOException e) {
            System.out.println("Read failed");
            System.exit(-1);
        }

    }

    public static String getString(BufferedReader socketSIn) {
        String body = "";
        try {
            int i = 0;
            while (i != -1 && (char) i != '\r' && (char) i != '\n') {
                i = socketSIn.read();
                body += ((char) i);
            }
        } catch (IOException e) {
            System.out.println("Input/Outpur error. " + e.getMessage());
            System.exit(-1);
        }
        return body;
    }

    public void send_REQUESTToS() {
        this.socketSOut.print("");
    }

    public void send_requestStrToS(String payload) {
        this.socketSOut.println(payload);
    }

    public void send_HOSTToS() {
        this.socketSOut.print("Host: ");
    }

    public void send_USERAToS() {
        this.socketSOut.print("User-Agent: ");
    }

    public void send_ACCEPTTToS() {
        this.socketSOut.print("Accept: ");
    }

    public void send_ACCEPTLToS() {
        this.socketSOut.print("Accept-Language: ");
    }

    public void send_ACCEPTEToS() {
        this.socketSOut.print("Accept-Encoding: ");
    }

    public void send_DNTToS() {
        this.socketSOut.print("DNT: ");
    }

    public void send_CONNECTIONToS() {
        this.socketSOut.print("Connection: ");
    }

    public void send_UPGRADEIRToS() {
        this.socketSOut.print("Upgrade-Insecure-Requests: ");
    }

    public void send_COOKIEToS() {
        this.socketSOut.print("Cookie: ");
    }

    public void send_BODYToS() {
        this.socketSOut.println(" ");
    }

    public void send_hostStrToS(String payload) {
        this.socketSOut.println(payload);
    }

    public void send_userAStrToS(String payload) {
        this.socketSOut.println(payload);
    }

    public void send_acceptTStrToS(String payload) {
        this.socketSOut.println(payload);
    }

    public void send_acceptLStrToS(String payload) {
        this.socketSOut.println(payload);
    }

    public void send_acceptEStrToS(String payload) {
        this.socketSOut.println(payload);
    }

    public void send_DNTIntToS(Integer payload) {
        this.socketSOut.println(payload);
    }

    public void send_connectionStrToS(String payload) {
        this.socketSOut.println(payload);
    }

    public void send_upgradeIRStrToS(String payload) {
        this.socketSOut.println(payload);
    }

    public void send_cookieStrToS(String payload) {
        this.socketSOut.println(payload);
    }

    public void send_bodyStrToS(String payload) {
        this.socketSOut.println(payload + "\r\n");
    }

    public String receive_httpvStrFromS() {
        String line = "";
        try {
            int i = 0;
            while (i != -1 && (char) i != ' ') {
                i = socketSIn.read();
                line += ((char) i);
            }
        } catch (IOException e) {
            System.out.println("Input/Outpur error." + e);
            System.exit(-1);
        }
        return line;
    }

    public Choice1 receive_Choice1LabelFromS() {
        String stringLabelChoice1 = "";
		try {
			int i = 0;
			while (i != -1 && (char) i != ' ') {
				i = socketSIn.read();
				stringLabelChoice1 += ((char) i);
			}
		} catch (IOException e) {
			System.out.println("Input/Outpur error." + e);
			System.exit(-1);
		}
        switch (stringLabelChoice1.trim()) {
            case "200":
                return Choice1._200;
            case "404":
            default:
                return Choice1._404;
        }
    }

    public String receive_200StrFromS() {
        String line = "";
        try {
            line = this.socketSIn.readLine();
        } catch (IOException e) {
            System.out.println("Input/Outpur error. " + e.getMessage());
            System.exit(-1);
        }
        return line;
    }

    public String receive_404StrFromS() {
        String line = "";
        try {
            line = this.socketSIn.readLine();
        } catch (IOException e) {
            System.out.println("Input/Outpur error. " + e.getMessage());
            System.exit(-1);
        }
        return line;
    }

    public Choice2 receive_Choice2LabelFromS() {
        String stringLabelChoice2 = "";
        try {
            int i = 0;
            while (i != -1 && (char) i != ' ') {
                i = socketSIn.read();
                stringLabelChoice2 += ((char) i);
            }
        } catch (IOException e) {
            System.out.println("Input/Outpur error, unable to get label" + e.getMessage());
            System.exit(-1);
        }
        switch (stringLabelChoice2.trim()) {
            case "Date:":
                return Choice2.DATE;
            case "Server:":
                return Choice2.SERVER;
            case "Strict-Transport-Security:":
                return Choice2.STRICTTS;
            case "Last-Modified:":
                return Choice2.LASTM;
            case "ETag:":
                return Choice2.ETAG;
            case "Accept-Ranges:":
                return Choice2.ACCEPTR;
            case "Content-Length":
                return Choice2.CONTENTL;
            case "Vary:":
                return Choice2.VARY;
            case "Content-Type:":
                return Choice2.CONTENTT;
            case "Via:":
                return Choice2.VIA;
            case "Cache-Control:":
                return Choice2.CACHEC;
            case "P3P:":
                return Choice2.P3P;
            case "X-XSS-Protection:":
                return Choice2.XXSSPROTECTION;
            case "X-Frame-Options:":
                return Choice2.XFRAMEOPT;
            case "Set-Cookie:":
                return Choice2.SETCOOKIE;
            case "Transfer-Encoding:":
                return Choice2.TRANSFERE;
            case "Expires:":
                return Choice2.EXPIRES;
            case "\r\n":
            default:
                return Choice2.BODY;
        }
    }

    public String receive_dateStrFromS() {
        String line = "";
        try {
            line = this.socketSIn.readLine();
        } catch (IOException e) {
            System.out.println("Input/Outpur error. " + e.getMessage());
            System.exit(-1);
        }
        return line;
    }

    public String receive_serverStrFromS() {
        String line = "";
        try {
            line = this.socketSIn.readLine();
        } catch (IOException e) {
            System.out.println("Input/Outpur error. " + e.getMessage());
            System.exit(-1);
        }
        return line;
    }

    public String receive_strictTSStrFromS() {
        String line = "";
        try {
            line = this.socketSIn.readLine();
        } catch (IOException e) {
            System.out.println("Input/Outpur error. " + e.getMessage());
            System.exit(-1);
        }
        return line;
    }

    public String receive_lastMStrFromS() {
        String line = "";
        try {
            line = this.socketSIn.readLine();
        } catch (IOException e) {
            System.out.println("Input/Outpur error. " + e.getMessage());
            System.exit(-1);
        }
        return line;
    }

    public String receive_eTagStrFromS() {
        String line = "";
        try {
            line = this.socketSIn.readLine();
        } catch (IOException e) {
            System.out.println("Input/Outpur error. " + e.getMessage());
            System.exit(-1);
        }
        return line;
    }

    public String receive_acceptRStrFromS() {
        String line = "";
        try {
            line = this.socketSIn.readLine();
        } catch (IOException e) {
            System.out.println("Input/Outpur error. " + e.getMessage());
            System.exit(-1);
        }
        return line;
    }

    public Integer receive_contentLIntFromS() {
        String line = "";
        try {
            line = this.socketSIn.readLine();
        } catch (IOException e) {
            System.out.println("Input/Outpur error. " + e.getMessage());
            System.exit(-1);
        }
        return Integer.parseInt(line);
    }

    public String receive_varyStrFromS() {
        String line = "";
        try {
            line = this.socketSIn.readLine();
        } catch (IOException e) {
            System.out.println("Input/Outpur error. " + e.getMessage());
            System.exit(-1);
        }
        return line;
    }

    public String receive_contentTStrFromS() {
        String line = "";
        try {
            line = this.socketSIn.readLine();
        } catch (IOException e) {
            System.out.println("Input/Outpur error. " + e.getMessage());
            System.exit(-1);
        }
        return line;
    }

    public String receive_viaStrFromS() {
        String line = "";
        try {
            line = this.socketSIn.readLine();
        } catch (IOException e) {
            System.out.println("Input/Outpur error. " + e.getMessage());
            System.exit(-1);
        }
        return line;
    }

    public String receive_cacheCStrFromS() {
        String line = "";
        try {
            line = this.socketSIn.readLine();
        } catch (IOException e) {
            System.out.println("Input/Outpur error. " + e.getMessage());
            System.exit(-1);
        }
        return line;
    }

    public String receive_p3pStrFromS() {
        String line = "";
        try {
            line = this.socketSIn.readLine();
        } catch (IOException e) {
            System.out.println("Input/Outpur error. " + e.getMessage());
            System.exit(-1);
        }
        return line;
    }

    public String receive_xxssProtectionStrFromS() {
        String line = "";
        try {
            line = this.socketSIn.readLine();
        } catch (IOException e) {
            System.out.println("Input/Outpur error. " + e.getMessage());
            System.exit(-1);
        }
        return line;
    }

    public String receive_xframeOptStrFromS() {
        String line = "";
        try {
            line = this.socketSIn.readLine();
        } catch (IOException e) {
            System.out.println("Input/Outpur error. " + e.getMessage());
            System.exit(-1);
        }
        return line;
    }

    public String receive_setCookieStrFromS() {
        String line = "";
        try {
            line = this.socketSIn.readLine();
        } catch (IOException e) {
            System.out.println("Input/Outpur error. " + e.getMessage());
            System.exit(-1);
        }
        return line;
    }

    public String receive_transferEStrFromS() {
        String line = "";
        try {
            line = this.socketSIn.readLine();
        } catch (IOException e) {
            System.out.println("Input/Outpur error. " + e.getMessage());
            System.exit(-1);
        }
        return line;
    }

    public String receive_expiresStrFromS() {
        String line = "";
        try {
            line = this.socketSIn.readLine();
        } catch (IOException e) {
            System.out.println("Input/Outpur error. " + e.getMessage());
            System.exit(-1);
        }
        return line;
    }

    public String receive_bodyStrFromS() {
        return getString(socketSIn);
    }

}
