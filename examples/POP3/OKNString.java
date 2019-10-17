package examples.POP3;


public class OKNString {
	String a;
	String label = "OK ";

	public OKNString (String y){
		a = y;
	}

	public String toString() {
		  String message;

		  message = this.label + this.a;
		  return message;
		}

	public static OKNString Parse(String message){

		String substring = message.substring(4, message.length());
		return new OKNString(substring);

	}

}
