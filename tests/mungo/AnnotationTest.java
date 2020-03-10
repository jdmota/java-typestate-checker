import org.checkerframework.checker.mungo.qual.MungoState;
import org.checkerframework.checker.mungo.qual.MungoTypestate;

@MungoTypestate("ProtocolFile.protocol")
class AnnotationTest {

  public static void main(String[] args) {
    AnnotationTest a = new AnnotationTest();

    Object b = new @MungoTypestate("ProtocolFile.protocol") @MungoState("STATE2") Object() {

    };
  }

}
