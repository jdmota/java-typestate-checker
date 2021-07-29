import java.util.*;

public class Main {
	public static void main(String[] args) {
		JavaIterator it = new JavaIterator(Arrays.asList(args).iterator());

    loop: while(true) {
      switch(it.hasNext()) {
        case True:
          System.out.println(it.next());
          break;
        case False:
          break loop;
      }
    }
	}
}
