///|
/// Function index allocation and linker table (matches refs/simple CodeGen FIDXS + _linker).
///
/// This is global state within the chapter19 package, reset on each new Parser/CodeGen.
let _fidx_counts : Ref[Map[String, Int]] = Ref::{ val: Map::new() }

///|
let _linker : Ref[Map[String, Node]] = Ref::{ val: Map::new() }

///|
pub let main_sig : Ref[TypeFunPtr] = Ref::{
  // Overwritten on each Parser/CodeGen creation.
  val: { _nil: 2, _sig: Some([type_integer_bot]), _ret: bottom, _fidxs: 1L, _name: None },
}

///|
pub fn fun_table_reset() -> Unit {
  _fidx_counts.val = Map::new()
  _linker.val = Map::new()
}

///|
fn _sig_key(sig : Array[Type]) -> String {
  // Stable enough for a per-run map key.
  let sb = StringBuilder::new()
  let mut first = true
  for t in sig {
    if !first {
      sb.write_string(",")
    }
    first = false
    sb.write_string(t.str())
  }
  sb.to_string()
}

///|
fn _tfp_key(tfp : TypeFunPtr) -> String {
  // Linker ignores return type (matches refs/simple).
  tfp.make_from_ret(bottom).str()
}

///|
/// Compute a new constant funptr for this signature (one fidx bit set).
///
/// Matches refs/simple CodeGen.makeFun(TypeTuple sig, Type ret).
pub fn make_fun(sig : Array[Type], ret : Type) -> TypeFunPtr {
  let key = _sig_key(sig)
  let next = match _fidx_counts.val.get(key) {
    Some(n) => n
    None => 0
  }
  if next >= 64 {
    panic()
  }
  _fidx_counts.val[key] = next + 1
  { _nil: 2, _sig: Some(sig), _ret: ret, _fidxs: 1L << next, _name: None }
}

///|
/// Insert linker mapping from constant fun signature (return wiped to BOTTOM) to the function head.
pub fn link_put(fun : Node) -> Unit {
  if fun.kind != Fun {
    panic()
  }
  match fun._fun_sig {
    Some(sig) => {
      _linker.val[_tfp_key(sig)] = fun
    }
    None => panic()
  }
}

///|
/// Reverse from a constant function pointer to the IR function being called.
pub fn link_get(tfp : TypeFunPtr) -> Node? {
  _linker.val.get(_tfp_key(tfp))
}
