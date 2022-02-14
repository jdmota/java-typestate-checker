import jatyc.lib.Requires;

public class Example1 {
  public static void main(String[] args) {
    BaseAccount b = new ProAccount(); // up-cast
    b.deposit(50);
    ProAccount p = (ProAccount) b; // down-cast
    if (p.canTransfer(70)) p.transfer(new ProAccount());
    else p.deposit(100);
    withdrawAttempt(p); // up-cast
  }

  static void withdrawAttempt(@Requires("Attempt") BaseAccount b) {
    if (b.canWithdraw(15)) b.withdraw();
    else b.deposit(100);
  }
}
