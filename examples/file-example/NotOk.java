public class NotOk {
  public static void main(String args[]) {
    File f = new File();
    
    System.out.println(f.read());
    f.close();
  }
}
