import java.util.*;

public class NotOk {
	public static void main(String[] args) {
		JavaIterator it = new JavaIterator(Arrays.asList(args).iterator());

    loop: do {
      switch(it.hasNext()) {
        case True:
          System.out.println(it.next());
          continue loop; // Actually, this makes it return to the condition, not the beginning
          // But the original Mungo thinks otherwise
        case False:
          break loop;
      }
    } while(false); // After the first cycle, we leave, potentially leaving the object incompleted
	}
}
