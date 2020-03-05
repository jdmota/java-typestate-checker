import org.checkerframework.checker.mungo.qual.*;

// Test basic subtyping relationships for the Mungo Checker.
class SubtypingTest {
  void allSubtypingRelationships(@MungoUnknown int x, @MungoBottom int y) {
    @MungoUnknown int a = x;
    @MungoUnknown int b = y;
    // :: error: assignment.type.incompatible
    @MungoBottom int c = x; // expected error on this line
    @MungoBottom int d = y;
  }
}
