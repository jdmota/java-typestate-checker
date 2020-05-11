package demos.POP3;


public class OKString {
	String a;
	String label = "OK ";

	public OKString (String y){
		a = y;
	}

	public String toString() {
		  String message;

		  message = this.label + this.a;
		  return message;
		}

	public static OKString Parse(String message){
		String substring = "";
		if(message != null)
			substring = message.substring(3, message.length());
		return new OKString(substring);

	}

}
