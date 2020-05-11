package demos.POP3;


public class IntString {
	int x;
	String y;
	static String sep = " ";
	//static string needed for static parser

	public IntString (int p, String q){
		x = p;
		y = q;
	}

	// take substring
	// +OK Int String
	// OK Int String

	public String toString() {
		  String message;

		  message = "OK " + this.x + sep + this.y;
		  return message;
		}

	public static IntString Parse(String message){

		String substring = message.substring(4, message.length());
		String[] pieces = substring.split(sep);

   		return new IntString(Integer.parseInt(pieces[0]), pieces[1]);
  	}

}
