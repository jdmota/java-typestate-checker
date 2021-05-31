import mungo.lib.Typestate;
import java.util.ArrayList;
import java.util.List;
@Typestate("Bank.protocol")
public class Bank {

  public boolean openAccount(String name, String password) {return true;} //throws RemoteException, BankingException;

  public FunnyMoney closeAccount() {return new FunnyMoney(0);}
    //throws RemoteException, BankingException;

  public boolean deposit(FunnyMoney money) {return true;}
    //throws RemoteException, BankingException;

  public boolean withdraw(int amount) {return true;}
    //throws RemoteException, BankingException;

  public int getBalance() {return 0;}
    //throws RemoteException, BankingException;

  public List<Object> getTransactionHistory() {return new ArrayList<>();}
    //throws RemoteException, BankingException;

}
