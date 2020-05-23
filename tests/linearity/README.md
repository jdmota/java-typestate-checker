The following examples test if the new implementation of Mungo currently enforces linearity, specially in some corner cases dealing with objects holding references to other objects and potentially producing a circular reference. All these examples are available here: [tests/linearity](https://github.com/jdmota/abcd-mungo/tree/jdmota-v2/tests/linearity).

The examples make use of some dummy objects:

- `ObjWithSetter`: Objects of this class have a private field `f`, which stores a reference to another `ObjWithSetter` object. To ensure completion, there is a `finish` method which transits the state to `end`. Examples using this object, assign a value to the field using the `setF` method.

```java
public class ObjWithSetter {
  private @MungoNullable ObjWithSetter f = null;

  public void setF(ObjWithSetter f) {
    this.f = f;
  }

  public void finish() {
    if (f != null) f.finish();
  }
}
```

- `ObjWithPrivField`: Objects of this class have a private field `f`, which stores a reference to another `ObjWithPrivField` object. Examples using this object, assign to the field directly, which is possible if the methods which create and use these objects are declared in the `ObjWithPrivField` class itself.

```java
public class ObjWithPrivField {
  private @MungoNullable ObjWithPrivField f = null;

  public void finish() {
    if (f != null) f.finish();
  }
}
```

- `ObjWithPubField`: Objects of this class are similar to instances of `ObjWithPrivField` except the `f` field is public.

```java
public class ObjWithPubField {
  public @MungoNullable ObjWithPubField f = null;

  public void finish() {
    if (f != null) f.finish();
  }
}
```

The following code examples make use of objects from the class `ObjWithSetter`.

The first code example presents the creation of two objects, where the second once is stored in the first. No errors are reported since this respects linearity.

```java
// o1 -> o2
ObjWithSetter o1 = new ObjWithSetter();
ObjWithSetter o2 = new ObjWithSetter();
o1.setF(o2);
o1.finish();
```

The following example is similar to the previous one, except there is a third object introduced. The first object will point to the second, and the second to the third. There is one error reported. Since the second object was "moved" to the first one, it cannot be used anymore.

```java
// o1 -> o2 -> o3
ObjWithSetter o1 = new ObjWithSetter();
ObjWithSetter o2 = new ObjWithSetter();
ObjWithSetter o3 = new ObjWithSetter();
o1.setF(o2);
// :: error: (Cannot call setF on moved value)
o2.setF(o3);
o1.finish();
```

The third example also creates a "chain" of three objects, but the `setF` calls are reversed, allowing the code to be checked without errors being reported: the third object is assigned to the field of the second, and then the second to the first.

```java
// o1 -> o2 -> o3
ObjWithSetter o1 = new ObjWithSetter();
ObjWithSetter o2 = new ObjWithSetter();
ObjWithSetter o3 = new ObjWithSetter();
o2.setF(o3);
o1.setF(o2);
o1.finish();
```

The following example attempts to create a circular reference, when an object is referenced from itself. This example produces an error. When a method on an object is called, that object is temporarily considered "moved", and only after the method call, the object is available again. In the example, when the checker encounters `o1.setF`, it marks `o1` as "moved", and then, when checking the arguments, it will find that `o1` was moved, which produces an `argument.type.incompatible` error, since the type `Moved` is not compatible to the type `ObjWithSetter`. Another way of thinking about this, is to imagine a method call where the first argument is the `this` value, like so: `setF(o1, o1)`. In this example, it becomes obvious that `o1` is moved twice, which breaks linearity.

```java
// o1 -> o1
ObjWithSetter o1 = new ObjWithSetter();
// :: error: (argument.type.incompatible)
o1.setF(o1);
o1.finish();
```

This next example also creates a circular reference, but with a level of indirection. Notice how `o2` is "moved" to `o1`, which then disallows the next `setF` call.

```java
// o1 -> o2 -> o1
ObjWithSetter o1 = new ObjWithSetter();
ObjWithSetter o2 = new ObjWithSetter();
o1.setF(o2);
// :: error: (Cannot call setF on moved value)
o2.setF(o1);
```

The following example creates a circular reference, like the previous example, but with two levels of indirection. First `o2` is assigned to the field of `o1`, then `o3` is assigned to `o2`, and finnaly, `o1` to `o2`, creating a circular reference. Two errors are reported since after `o2` is "moved" to `o1`, it cannot be used, and after `o3` is moved to `o2`, it cannot be used as well.

```java
// o1 -> o2 -> o3 -> o1
ObjWithSetter o1 = new ObjWithSetter();
ObjWithSetter o2 = new ObjWithSetter();
ObjWithSetter o3 = new ObjWithSetter();
o1.setF(o2);
// :: error: (Cannot call setF on moved value)
o2.setF(o3);
// :: error: (Cannot call setF on moved value)
o3.setF(o1);
```

The next code example does the same as previously, but the `setF` calls are in different order. `o1` is first assigned to the field of `o3`, then `o3` is assigned to `o2`, and then `o2` to `o1`. In this instance, only one error is reported, when the "cycle" is closed. Notice how `o1` was "moved" to `o3` in the first `setF` call. By doing that, `o1` became unavailable, which means it cannot be used in the last `setF` call.

```java
// o1 -> o2 -> o3 -> o1
ObjWithSetter o1 = new ObjWithSetter();
ObjWithSetter o2 = new ObjWithSetter();
ObjWithSetter o3 = new ObjWithSetter();
o3.setF(o1);
o2.setF(o3);
// :: error: (Cannot call setF on moved value)
o1.setF(o2);
```

The following code examples make use of objects from the class `ObjWithPrivField`.

```
// o1 -> o2
ObjWithPrivField o1 = new ObjWithPrivField();
ObjWithPrivField o2 = new ObjWithPrivField();
o1.f = o2;
o1.finish();
```

```
// o1 -> o2 -> o3
ObjWithPrivField o1 = new ObjWithPrivField();
ObjWithPrivField o2 = new ObjWithPrivField();
ObjWithPrivField o3 = new ObjWithPrivField();
// :: error: (Cannot override because object has not ended its protocol. Type: ObjWithPrivField{Start} | Ended | Moved | Null)
o1.f = o2;
// :: error: (Cannot access f on moved value)
// :: error: (Cannot override because object has not ended its protocol. Type: ObjWithPrivField{Start} | Ended | Moved | Null)
o2.f = o3;
o1.finish();
```

```
// o1 -> o2 -> o3
ObjWithPrivField o1 = new ObjWithPrivField();
ObjWithPrivField o2 = new ObjWithPrivField();
ObjWithPrivField o3 = new ObjWithPrivField();
// :: error: (Cannot override because object has not ended its protocol. Type: ObjWithPrivField{Start} | Ended | Moved | Null)
o2.f = o3;
// :: error: (Cannot override because object has not ended its protocol. Type: ObjWithPrivField{Start} | Ended | Moved | Null)
o1.f = o2;
o1.finish();
```

```
// o1 -> o1
ObjWithPrivField o1 = new ObjWithPrivField();
// :: error: (Cannot override because object has not ended its protocol. Type: ObjWithPrivField{Start} | Ended | Moved | Null)
o1.f = o1;
// :: error: (Cannot call finish on moved value)
o1.finish();
```

```
// o1 -> o2 -> o1
ObjWithPrivField o1 = new ObjWithPrivField();
ObjWithPrivField o2 = new ObjWithPrivField();
// :: error: (Cannot override because object has not ended its protocol. Type: ObjWithPrivField{Start} | Ended | Moved | Null)
o1.f = o2;
// :: error: (Cannot override because object has not ended its protocol. Type: ObjWithPrivField{Start} | Ended | Moved | Null)
// :: error: (Cannot access f on moved value)
o2.f = o1;
```

```
// o1 -> o2 -> o3 -> o1
ObjWithPrivField o1 = new ObjWithPrivField();
ObjWithPrivField o2 = new ObjWithPrivField();
ObjWithPrivField o3 = new ObjWithPrivField();
// :: error: (Cannot override because object has not ended its protocol. Type: ObjWithPrivField{Start} | Ended | Moved | Null)
o1.f = o2;
// :: error: (Cannot override because object has not ended its protocol. Type: ObjWithPrivField{Start} | Ended | Moved | Null)
// :: error: (Cannot access f on moved value)
o2.f = o3;
// :: error: (Cannot override because object has not ended its protocol. Type: ObjWithPrivField{Start} | Ended | Moved | Null)
// :: error: (Cannot access f on moved value)
o3.f = o1;
```

```
// o1 -> o2 -> o3 -> o1
ObjWithPrivField o1 = new ObjWithPrivField();
ObjWithPrivField o2 = new ObjWithPrivField();
ObjWithPrivField o3 = new ObjWithPrivField();
// :: error: (Cannot override because object has not ended its protocol. Type: ObjWithPrivField{Start} | Ended | Moved | Null)
o3.f = o1;
// :: error: (Cannot override because object has not ended its protocol. Type: ObjWithPrivField{Start} | Ended | Moved | Null)
o2.f = o3;
// :: error: (Cannot override because object has not ended its protocol. Type: ObjWithPrivField{Start} | Ended | Moved | Null)
// :: error: (Cannot access f on moved value)
o1.f = o2;
```

The following code examples make use of objects from the class `ObjWithPubField`.

TODO
