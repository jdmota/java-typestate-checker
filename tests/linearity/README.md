The following examples test if the new implementation of Mungo currently enforces linearity. All these examples are available here: [tests/linearity](https://github.com/jdmota/abcd-mungo/tree/jdmota/tests/linearity).

## Contents:

- [Examples with ObjWithSetter](#objwithsetter)
- [Examples with ObjWithPrivField](#objwithprivfield)
- [Issue found](#issue-found)

#### ObjWithSetter

[Top](#contents)

The code examples in this section make use of objects from the class `ObjWithSetter`. Objects of this class have a private field `f`, which stores a reference to another `ObjWithSetter` object. To ensure completion, there is a `finish` method which transits the state to `end`. Examples using this object, assign a value to the field using the `setF` method, which can only be called once, according to the protocol.

```java
@Typestate("ObjWithSetter")
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

```
typestate ObjWithSetter {
  Start = {
    void setF(ObjWithSetter): Set,
    void finish(): end
  }
  Set = {
    void finish(): end
  }
}
```

The first code example presents the creation of two objects, where the second once is stored in the first. No errors are reported since this respects linearity.

```java
// o1 -> o2
ObjWithSetter o1 = new ObjWithSetter();
ObjWithSetter o2 = new ObjWithSetter();
o1.setF(o2);
o1.finish();
```

The following example is similar to the previous one, except a third object is introduced. The first object will point to the second, and the second to the third. This code produces an error. Since the second object was "moved" to the first one, by the first `setF` call, it cannot be used anymore, so the second `setF` call is not allowed.

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

The following example attempts to create a circular reference, when an object is referenced from itself. This example produces an error. When a method on an object is called, that object is temporarily considered "moved", and only after the method call, the object is available again. In the example, when the checker encounters `o1.setF`, it marks `o1` as "moved", and then, when checking the arguments, it will find that `o1` was moved, which produces an `argument.type.incompatible` error, since the type `Moved` is not compatible with the type `ObjWithSetter`. Another way of thinking about this, is to imagine a method call where the first argument is the `this` value, like so: `setF(o1, o1)`. In this example, it becomes obvious that `o1` is moved twice, which breaks linearity.

```java
// o1 -> o1
ObjWithSetter o1 = new ObjWithSetter();
// :: error: (argument.type.incompatible)
o1.setF(o1);
o1.finish();
```

This next example also attempts to create a circular reference, but with a level of indirection. The `o2` object is assigned to the field of `o1`, and then there is an attempt to assign `o1` to `o2`. Notice how `o2` is "moved" to `o1`, in the first `setF` call, which then disallows the next `setF` call on `o2`, preventing a circular reference from occurring.

```java
// o1 -> o2 -> o1
ObjWithSetter o1 = new ObjWithSetter();
ObjWithSetter o2 = new ObjWithSetter();
o1.setF(o2);
// :: error: (Cannot call setF on moved value)
o2.setF(o1);
```

The following example attempts to create a circular reference, like the previous example, but with two levels of indirection. First, `o2` is assigned to the field of `o1`, then `o3` is assigned to `o2`, and finnaly, `o1` to `o2`, creating a circular reference. Two errors are reported since after `o2` is "moved" to `o1`, it cannot be used, and after `o3` is moved to `o2`, it cannot be used as well.

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

The next code example does the same as the previous one, but the `setF` calls are in different order. `o1` is first assigned to the field of `o3`, then `o3` is assigned to `o2`, and then `o2` to `o1`. In this instance, only one error is reported: when the "cycle" is closed. Notice how `o1` was "moved" to `o3` in the first `setF` call. By doing that, `o1` became unavailable, which means it cannot be used in the last `setF` call.

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

####  ObjWithPrivField

[Top](#contents)

The following code examples make use of objects from the class `ObjWithPrivField`. Objects of this class have a private field `f`, which stores a reference to another `ObjWithPrivField` object. They reproduce the same cases presented previously for the objects from the class `ObjWithSetter`, but instead of using a `setF` method, they assign directly to the `f` field. Since the following code is defined in the same class, the private field is visible.

```java
@Typestate("ObjWithPrivField")
public class ObjWithPrivField {
  private @MungoNullable ObjWithPrivField f = null;

  public void finish() {
    if (f != null) f.finish();
  }
}
```

```
typestate ObjWithPrivField {
  Start = {
    void finish(): end
  }
}
```

In the previous section, errors like `Cannot call setF on moved value` were reported. In this section, the exact same thing happens with errors like `Cannot access f on moved value`. Additionally, errors like `Cannot override because object has not ended its protocol` are reported everytime an assignment to the `f` field is done. This happens because the static analysis does not know what is the state of `f`, so it assumed any is possible, and reports the possibility that the object pointed by the field, had not its protocol reach completion.

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

#### Issue found

[Top](#contents)

While it is true that, when a field is accessed from "outside", every type is assumed to be possible, disallowing any actions on it, if the field is private, it is assumed that the class has control over it, and nothing from "outside" will tamper with the field. Sadly, that assumption can be broken if a static method is declared in the same class as the private field, allowing it to be accessed.

In the following example, notice that the field access `w.o` in `privateAccess` reports an error, since we default to all possible types. But inside the `PrivateAccess` class, namely in the `finish` method, there is no error, because it is assumed that no one else can change the private field.

```
typestate Obj {
  Start = {
    void finish(): end
  }
}
```

```java
@Typestate("Obj")
public class Obj {
  public void finish() {}
}

@Typestate("Obj")
public class PrivateAccess {

  private Obj o = new Obj();

  public void finish() {
    // FIXME issue here, we are not aware that privateAccess() broke our assumptions...
    // and the object already finished...
    o.finish();
  }

  public static void privateAccess() {
    PrivateAccess w = new PrivateAccess();
    // :: error: (Cannot call finish on ended protocol, on moved value)
    w.o.finish();
    w.finish();
  }

}
```

Public fields accessed from "outside" or "inside" the class have all the possible types, because it is assumed that they might be changed at anytime, since they are public. For private fields, it is assumed that those are completly controlled by the class. In the previous example, an error should be reported "inside" the class as well, for consistency with the way public fields are handled, like in the following example:

```java
@Typestate("Obj")
public class PublicAccess {
  
  // :: error: (Object did not complete its protocol. Type: Obj{Start} | Ended | Moved)
  public Obj o = new Obj();

  public void finish() {
    // :: error: (Cannot call finish on ended protocol, on moved value)
    o.finish();
  }

  public static void publicAccess() {
    PublicAccess w = new PublicAccess();
    // :: error: (Cannot call finish on ended protocol, on moved value)
    w.o.finish();
    w.finish();
  }

}
```
