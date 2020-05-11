package demos.POP3;


public class TwoString {
	String a;
	String b;
	static String sep = " ";

	public TwoString (String x, String y){
		a = x;
		b = y;
	}

	public String toString() {
		  String message;

		  message = this.a + sep + this.b;
		  return message;
		}

	public static TwoString Parse(String message){

		String substring = message.substring(4, message.length());

  		PairString r = PairString.Parse(substring);
  		return new TwoString((r.x), (r.y));
  	}

}
