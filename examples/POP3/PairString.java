package examples.POP3;


public class PairString {
	String x;
	String y;
	static String sep = " ";
	//there might be a space after the separator between the two payloads

	public PairString (String p, String q) {
		x = p;
		y = q;
	}

	public String toString() {
  	  String message;

  	  //out: string string

  	  message = this.x + sep + this.y;
  	  return message;
  	}

  	public static PairString Parse(String message){

  		//input: string string

  		String[] pieces = message.split(sep);
  		return new PairString(pieces[0], pieces[1]);

  	}

}
