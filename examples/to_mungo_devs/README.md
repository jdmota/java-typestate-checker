# Examples

This folder contains some examples where Mungo does not detect present issues and code examples where the current version of Mungo crashes. Inside each folder there are `README.md` files with the corresponding outputs that Mungo gives.

Each example was run with the command `java -jar "mungo.jar" -classpath "mungo.jar" *.java`, where `mungo.jar` is the file available at [https://bitbucket.org/abcd-glasgow/mungo-tools/src/4d05a797a0ee22a3680890cbdbd88158056af224/](https://bitbucket.org/abcd-glasgow/mungo-tools/src/4d05a797a0ee22a3680890cbdbd88158056af224/).

## `flow-issue-1`

An example where an error was expected but none is reported.

```java
import java.util.*;

public class Main {
  public static void main(String[] args) {
    JavaIterator it = new JavaIterator(Arrays.asList(args).iterator());

    loop: do {
      switch(it.hasNext()) {
        case True:
          System.out.println(it.next());
          continue loop;
        case False:
          break loop;
      }
    } while(false); // This is false, iterator might not finish
  }
}
```

The current version seems to wrongly assume that a `continue` statement jumps to the beginning of a loop, when in actuality, a `continue` statement jumps to the condition expression. If the condition were to be always `true`, that would make no difference, but if the condition is `false`, bugs may go unnoticed. Like in the example, where the iterator might not reach the `end` state.

## `flow-issue-2`

An example where an error was expected but none is reported.

```java
public class Main {
  public static void main(String args[]) {
    File f = new File();

    switch (f.open()) {
      case OK:
        switch (f.read()) {
          case "CLOSE":
            f.close();
            break;
        }
        // File might not close
        break;
      case ERROR:
        break;
    }
  }
}
```

The current implementation of Mungo does not seem to detect that it is possible that no case in the `switch` statement matches. In the example, this allows the code to exit without the file being closed.

This is a simplified example of an issue not detected in the `CMain.java` file in the `http` example at [https://bitbucket.org/abcd-glasgow/mungo-tools/src/master/demos/http/](https://bitbucket.org/abcd-glasgow/mungo-tools/src/master/demos/http/). If `sread1` does not match `"REQUEST"`, the code jumps to line 102, where there is a `currentC.receive_httpvStrFromS()` call, which is not allowed in the initial state of `CRole`, as specified by the `CProtocol`. An error reporting that was expected, but none was shown.

## `crash-1`

An example that crashes with `NullPointerException`. 

Removing the following code from inside the lambda in the `Main.java` avoids the crash, like one can see in the `crash-1-adapted` example.

```java
File f = new File();
f.read();
f.close();
```

## `crash-2`

An example that crashes with `NullPointerException`. 

Removing the `@Typestate` annotation from the `File` class, avoids the crash, like one can see in the `crash-2-adapted` example.

## `crash-3`

An example that crashes with `NullPointerException`. 

Removing the following line of code from the `Main.java` file avoids the crash, like one can see in the `crash-3-adapted` example.

```java
File f1 = list.get(0);
```

