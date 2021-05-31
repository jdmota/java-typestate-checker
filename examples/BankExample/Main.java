import java.util.Scanner;
import org.checkerframework.checker.jtc.lib.Requires;
import org.checkerframework.checker.jtc.lib.Ensures;
import java.util.List;
public class Main {

  public static void main(String[] args) throws Exception {
    Bank bank = new Bank();
    Scanner s = new Scanner(System.in);
    loop1:
    while (true) {
      String cmd = s.next().toLowerCase();
      if (cmd.equals("open")) {
        String name = s.next();
        String password = s.nextLine();
        if (bank.openAccount(name, password)) {
          if (bank instanceof ExtendedBank) extendedBankUsage((ExtendedBank) bank, s);
          else bankUsage(bank, s);
        } else System.out.println("Could not open. Try again.");
      } else if (cmd.equals("exit")) break loop1;
      else if (cmd.equals("upgrade")) bank = new ExtendedBank();
      else if (cmd.equals("downgrade")) bank = new Bank();
      else System.out.println("Unexpected command. Try again.");
    }
  }

    public static void bankUsage(@Requires("Open") @Ensures("Init") Bank bank, Scanner s) {
      loop2: while(true) {
        String cmd = s.next().toLowerCase();
        if (cmd.equals("close")) {
          bank.closeAccount();
          break loop2;
        } else if (cmd.equals("deposit")) {
          int val = s.nextInt();
          bank.deposit(new FunnyMoney(val));
        }
        else if (cmd.equals("withdraw")) {
          int val = s.nextInt();
          bank.withdraw(val);
        }
        else if (cmd.equals("balance")) bank.getBalance();
        else if (cmd.equals("history")) bank.getTransactionHistory();
        else System.out.println("Unexpected command. Try again.");
        s.nextLine();
      }
    }


  public static void extendedBankUsage(@Requires("Open") @Ensures("Init") ExtendedBank bank, Scanner s) {
    loop2: while(true) {
      String cmd = s.next().toLowerCase();
      if (cmd.equals("close")) {
        bank.closeAccount();
        break loop2;
      } else if (cmd.equals("deposit")) {
        int val = s.nextInt();
        bank.deposit(new FunnyMoney(val));
      }
      else if (cmd.equals("withdraw")) {
        int val = s.nextInt();
        bank.withdraw(val);
      }
      else if (cmd.equals("balance")) bank.getBalance();
      else if (cmd.equals("history")) bank.getTransactionHistory();
      else if (cmd.equals("withdrawAll")) bank.withdrawAll();
      else System.out.println("Unexpected command. Try again.");
      s.nextLine();
    }

  }
}
