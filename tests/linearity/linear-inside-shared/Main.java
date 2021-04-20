public class Main {
  public static void main(String args[]) {
    Shared a = new Shared();
    Shared b = a;
    
    a.change();
    b.change();
    
    // It seems that in sequential code, this is fine,
    // because the operations are performed in "lock step"
    // and the class analysis of Shared already takes into account
    // that "change" may be called any number of times.

    // But with paralelism, this is not fine.
  }
}
