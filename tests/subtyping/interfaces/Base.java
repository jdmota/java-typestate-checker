import org.checkerframework.checker.jtc.lib.Nullable;
import mungo.lib.Typestate;

@Typestate("Base.protocol")
// :: error: Protocols on interfaces are not supported yet
interface Base {
  boolean hasNext();
  void next();
}
