package demos.POP3;


public class ERRString {
	String a;
	//static String sep = "-";

	public ERRString (String y){
		a = y;
	}

	public String toString() {
		  String message;

		  message = "ERR " + this.a;
		  return message;
		}

	public static ERRString Parse(String message){
		String substring = "";
		if(message != null)
			substring = message.substring(4, message.length());
		return new ERRString(substring);

	}

}
