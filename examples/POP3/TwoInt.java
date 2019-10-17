package examples.POP3;


public class TwoInt {
	int x;
	int y;
	static String sep = " ";

	public TwoInt (int p, int q){
		x = p;
		y = q;
	}

	// take substring
	// use PairInt.java
	// +OK Int Int
	// OK Int Int

	public String toString() {
		  String message;

		  message = this.x + sep + this.y;
		  return message;
		}

	public static TwoInt Parse(String message){

		String substring = message.substring(4, message.length());

  		PairInt r = PairInt.Parse(substring);
  		return new TwoInt((r.x), (r.y));
  	}

}
