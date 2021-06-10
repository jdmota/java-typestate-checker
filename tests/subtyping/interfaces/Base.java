import org.checkerframework.checker.jtc.lib.Nullable;
import mungo.lib.Typestate;

@Typestate("Base")
interface Base {
  boolean hasNext();
  void next();
}
