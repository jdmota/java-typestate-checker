import mungo.lib.Typestate;

@Typestate("Base.protocol")
public abstract class Base {
  public abstract boolean hasNext();
  public abstract void next();
}
