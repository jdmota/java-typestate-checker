public class NotOk {
  public static void main(String args[]) {
    File f = new File();
    
    System.out.println(f.read()); // error: Cannot call [read] on State{File, Init}
    f.close();
  }
}
