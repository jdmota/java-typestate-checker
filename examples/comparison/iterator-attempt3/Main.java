import java.util.*;
import mungo.lib.Boolean;

public class Main {
	public static void main(String[] args) {
		JavaIterator it = new JavaIterator(Arrays.asList(args).iterator());
    
    while(it.hasNext() == Boolean.True){
      System.out.println(it.next());
    }
	}
}
