import java.util.Scanner;
import java.util.List;
import org.checkerframework.checker.jtc.lib.Requires;
import org.checkerframework.checker.jtc.lib.Ensures;

public class Main {

  public static void main(String[] args) throws Exception {
    Bank bank = new Bank();
    Scanner s = new Scanner(System.in);

    while (true) {
      String cmd = s.next().toLowerCase();
      if (cmd.equals("open")) {
        String name = s.next();
        String password = s.nextLine();
        if (bank.openAccount(name, password)) {
          if (bank instanceof ExtendedBank) {
            extendedBankUsage((ExtendedBank) bank, s);
          } else {
            bankUsage(bank, s);
          }
        } else System.out.println("Could not open. Try again.");
      } else if (cmd.equals("exit")) break;
      else if (cmd.equals("upgrade")) bank = new ExtendedBank();
      else if (cmd.equals("downgrade")) bank = new Bank();
      else System.out.println("Unexpected command. Try again.");
    }
  }

  public static void bankUsage(@Requires("Open") @Ensures("Init") Bank bank, Scanner s) {
    while(true) {
      String cmd = s.next().toLowerCase();
      if (cmd.equals("close")) {
        bank.closeAccount();
        break;
      } else if (cmd.equals("deposit")) {
        int val = s.nextInt();
        bank.deposit(new FunnyMoney(val));
      }
      else if (cmd.equals("withdraw")) {
        int val = s.nextInt();
        bank.withdraw(val);
      }
      else if (cmd.equals("balance")) bank.getBalance();
      else System.out.println("Unexpected command. Try again.");
      s.nextLine();
    }
  }

  public static void extendedBankUsage(@Requires("Open") @Ensures("Init") ExtendedBank bank, Scanner s) {
    while(true) {
      String cmd = s.next().toLowerCase();
      if (cmd.equals("close")) {
        bank.closeAccount();
        break;
      } else if (cmd.equals("deposit")) {
        int val = s.nextInt();
        bank.deposit(new FunnyMoney(val));
      }
      else if (cmd.equals("withdraw")) {
        int val = s.nextInt();
        bank.withdraw(val);
      }
      else if (cmd.equals("balance")) bank.getBalance();
      else if (cmd.equals("withdrawAll")) bank.withdrawAll();
      else System.out.println("Unexpected command. Try again.");
      s.nextLine();
    }
  }
}
