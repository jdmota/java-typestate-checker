package demos.SMTP;


public class SMTPMessage {
  private String command;
  private String payload;
  private boolean isDashed;

  public SMTPMessage(String command, String payload, boolean isDashed) {
    this.command = command;
    this.payload = payload;
    this.isDashed = isDashed;
  }

  public SMTPMessage(String command, String payload) {
    this.command = command;
    this.payload = payload;
    this.isDashed = false;
  }

  public SMTPMessage(String command) {
    this.command = command;
    this.payload = null;
    this.isDashed = false;
  }

  public static SMTPMessage Parse(String message) {
    String[] matches = message.split(" |-", 2);
    return new SMTPMessage(matches[0], matches[1], message.charAt(3) == '-');
  }

  public String toString() {
    String message;
    if (this.payload == null) {
      message = this.command + "\\r\\n";
    } else {
      message = this.command + " " + this.payload + "\\r\\n";
    }

    return message;
  }

  public String getCommand() {
    return this.command;
  }

  public String getPayload() {
    return this.payload;
  }

  public boolean getIsDashed() {
    return this.isDashed;
  }
}
