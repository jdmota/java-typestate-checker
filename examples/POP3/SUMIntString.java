package examples.POP3;

public class SUMIntString {
	int x;
	String y;
	static String sep = " ";
	//static string needed for static parser

	public SUMIntString (int p, String q){
		x = p;
		y = q;
	}

	// take substring
	// +OK Int String
	// OK Int String

	public String toString() {
		  String message;

		  message = this.x + sep + this.y;
		  return message;
		}

	public static SUMIntString Parse(String message){

		String[] pieces = message.split(sep);

   		return new SUMIntString(Integer.parseInt(pieces[0]), pieces[1]);
  	}

}
