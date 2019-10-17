package demos.iterator;
import java.io.*;
import java.util.*;

class Main {
    public static void main () {
      Collection c = new HashSet();
      Integer i = 0;
      while(i < 32)
        c.add(i++);
      StateIterator iter = new StateIterator(c.iterator());
      iterate:
      do {
        switch(iter.hasNext()) {
          case TRUE:
          System.out.println(i = (Integer) iter.next());
          if(i%2 == 0) iter.remove(); continue iterate;
          case FALSE: break iterate;
          }
      } while(true);
    }
}
