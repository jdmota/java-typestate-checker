package demos.POP3;


public class SUMString {
	String a;

	public SUMString (String y){
		a = y;
	}

	public String toString() {
		  String message;

		  message = this.a;
		  return message;
		}

	public static SUMString Parse(String message){

		return new SUMString(message);

	}

}
