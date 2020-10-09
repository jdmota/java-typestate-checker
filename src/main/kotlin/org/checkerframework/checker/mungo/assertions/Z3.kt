package org.checkerframework.checker.mungo.assertions

import com.microsoft.z3.*
import java.lang.reflect.Method


class Z3Context : Context() {

  companion object {
    private val getNativeObjectMethod: Method = Z3Object::class.java.getDeclaredMethod("getNativeObject")
    private val funcDeclConstructor = FuncDecl::class.java.getDeclaredConstructor(Context::class.java, Long::class.java)

    init {
      getNativeObjectMethod.isAccessible = true
      funcDeclConstructor.isAccessible = true
    }

    private fun getNative(obj: Z3Object) = getNativeObjectMethod.invoke(obj) as Long
    private fun createFuncDecl(ctx: Context, id: Long): FuncDecl = funcDeclConstructor.newInstance(ctx, id)
  }

  /*
  /// <summary>
  /// Creates a new recursive function declaration.
  /// </summary>
  public FuncDecl MkRecFuncDecl(string name, Sort[] domain, Sort range)
  {
      Debug.Assert(range != null);
      Debug.Assert(domain.All(d => d != null));

      CheckContextMatch<Sort>(domain);
      CheckContextMatch(range);
      return new FuncDecl(this, MkSymbol(name), domain, range, true);
  }
  */
  private fun mkRecFuncDecl(symbol: Symbol, domain: Array<Sort>, range: Sort): FuncDecl {
    return createFuncDecl(this, Native.mkRecFuncDecl(
      this.nCtx(),
      getNative(symbol),
      FuncDecl.arrayLength(domain),
      FuncDecl.arrayToNative(domain),
      getNative(range)
    ))
  }

  /*
  /// <summary>
  /// Bind a definition to a recursive function declaration.
	/// The function must have previously been created using
	/// MkRecFuncDecl. The body may contain recursive uses of the function or
	/// other mutually recursive functions.
  /// </summary>
  public void AddRecDef(FuncDecl f, Expr[] args, Expr body)
	{
	    CheckContextMatch(f);
	    CheckContextMatch<Expr>(args);
	    CheckContextMatch(body);
      IntPtr[] argsNative = AST.ArrayToNative(args);
	    Native.Z3_add_rec_def(nCtx, f.NativeObject, (uint)args.Length, argsNative, body.NativeObject);
	}
  */
  private fun addRecDef(f: FuncDecl, args: Array<Expr>, body: Expr) {
    Native.addRecDef(nCtx(), getNative(f), AST.arrayLength(args), AST.arrayToNative(args), getNative(body))
  }

  fun mkRecFuncDecl(symbol: Symbol, domain: Array<Sort>, range: Sort, fn: (FuncDecl, Array<Expr>) -> Expr): FuncDecl {
    val f = mkRecFuncDecl(symbol, domain, range)
    val size = domain.size
    val xs = arrayOfNulls<Expr>(size)
    val types = arrayOfNulls<Sort>(size)
    for (j in 0 until size) {
      types[j] = domain[j]
      xs[j] = mkBound(j, types[j])
    }
    addRecDef(f, xs as Array<Expr>, fn(f, xs as Array<Expr>))
    return f
  }

  fun mkForall(domain: Array<Sort>, fn: (Array<Expr>) -> Expr): Quantifier {
    val size = domain.size
    val xs = arrayOfNulls<Expr>(size)
    val names = arrayOfNulls<Symbol>(size)
    val types = arrayOfNulls<Sort>(size)
    for (j in 0 until size) {
      types[j] = domain[j]
      names[j] = mkSymbol("x_$j")
      xs[j] = mkBound(j, types[j])
    }
    return mkForall(types, names, fn(xs as Array<Expr>), 0, null, null, null, null)
  }

}
