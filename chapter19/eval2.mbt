///|
pub struct Eval2 {}

///|
enum Eval2Value {
  Int(Int64)
  Float(Double)
  Obj(Ref[Eval2Obj])
  FunPtr(TypeFunPtr)
  Closure(Closure)
  Str(String)
  TypeVal(Type)
}

///|
struct Eval2Obj {
  id : Int
  fields : Array[Eval2Value?]
}

///|
struct Frame {
  mut data : Map[Int, Eval2Value?]
  mut prior : Ref[Frame]?
  mut refcnt : Int
  uid : Int
}

///|
struct Closure {
  _cc : Node
  mut _frame : Ref[Frame]
}

///|
let _frame_uid : Ref[Int] = Ref::{ val: 1 }

///|
let _next_obj_id : Ref[Int] = Ref::{ val: 1 }

///|
let _current_frame : Ref[Ref[Frame]?] = Ref::{ val: None }

///|
fn current_frame() -> Ref[Frame] {
  match _current_frame.val {
    Some(frame) => frame
    None => panic()
  }
}

///|
fn set_current_frame(frame : Ref[Frame]) -> Unit {
  _current_frame.val = Some(frame)
}

///|
fn frame_new(prior : Ref[Frame]?) -> Ref[Frame] {
  let uid = _frame_uid.val
  _frame_uid.val = uid + 1
  let frame = Frame::{ data: Map::new(), prior, refcnt: 1, uid }
  match prior {
    Some(p) => p.val.refcnt += 1
    None => ()
  }
  Ref::{ val: frame }
}

///|
fn frame_dec(frame : Ref[Frame]) -> Unit {
  if frame.val.refcnt <= 0 {
    panic()
  }
  frame.val.refcnt -= 1
  if frame.val.refcnt == 0 {
    let prior = frame.val.prior
    frame.val.prior = None
    frame.val.data = Map::new()
    match prior {
      Some(p) => frame_dec(p)
      None => ()
    }
  }
}

///|
fn frame_put(frame : Ref[Frame], node : Node, value : Eval2Value) -> Node {
  frame.val.data[node._nid] = Some(value)
  node
}

///|
fn frame_put0(frame : Ref[Frame], node : Node, value : Eval2Value?) -> Node {
  frame.val.data[node._nid] = value
  node
}

///|
fn frame_get(frame : Ref[Frame], node : Node) -> Eval2Value? {
  match frame.val.data.get(node._nid) {
    Some(v) => v
    None =>
      match frame.val.prior {
        Some(p) => frame_get(p, node)
        None => None
      }
  }
}

///|
fn closure_new(cc : Node, frame : Ref[Frame]) -> Closure {
  frame.val.refcnt += 1
  { _cc: cc, _frame: frame }
}

///|
fn closure_is_stop(clj : Closure) -> Bool {
  clj._cc.kind == Stop
}

///|
fn val(node : Node) -> Eval2Value? {
  let v = frame_get(current_frame(), node)
  if v is None && node.kind != Phi && node.kind != Parm && !node.is_cfg() {
    step(node)
    return frame_get(current_frame(), node)
  }
  v
}

///|
fn x(node : Node) -> Int64 {
  match val(node) {
    None => 0L
    Some(Eval2Value::Int(i)) => i
    _ => panic()
  }
}

///|
fn d(node : Node) -> Double {
  match val(node) {
    None => 0.0
    Some(Eval2Value::Float(f)) => f
    _ => panic()
  }
}

///|
fn tfp(node : Node) -> TypeFunPtr {
  match val(node) {
    Some(Eval2Value::FunPtr(fp)) => fp
    Some(Eval2Value::TypeVal(FunPtr(fp))) => fp
    _ => panic()
  }
}

///|
fn clj(node : Node) -> Closure {
  match val(node) {
    Some(Eval2Value::Closure(c)) => c
    _ => panic()
  }
}

///|
fn val_eq(lhs : Eval2Value?, rhs : Eval2Value?) -> Bool {
  match (lhs, rhs) {
    (None, None) => true
    (None, Some(_)) | (Some(_), None) => false
    (Some(l), Some(r)) => eval2_eq(l, r)
  }
}

///|
fn eval2_eq(lhs : Eval2Value, rhs : Eval2Value) -> Bool {
  match (lhs, rhs) {
    (Eval2Value::Int(a), Eval2Value::Int(b)) => a == b
    (Eval2Value::Float(a), Eval2Value::Float(b)) => a == b
    (Eval2Value::Obj(a), Eval2Value::Obj(b)) => a.val.id == b.val.id
    (Eval2Value::FunPtr(a), Eval2Value::FunPtr(b)) => a == b
    (Eval2Value::Str(a), Eval2Value::Str(b)) => a == b
    (Eval2Value::TypeVal(a), Eval2Value::TypeVal(b)) => a == b
    (Eval2Value::Closure(a), Eval2Value::Closure(b)) =>
      a._cc._nid == b._cc._nid && a._frame.val.uid == b._frame.val.uid
    _ => false
  }
}

///|
fn find_input_index(r : Node, prior : Node) -> Int {
  for i, input in r._inputs {
    match input {
      Some(n) if n == prior => return i
      _ => ()
    }
  }
  -1
}

///|
fn is_main_fun(fun : Node) -> Bool {
  match fun._fun_sig {
    Some(sig) => Type::FunPtr(sig).isa(Type::FunPtr(main_sig.val))
    None => false
  }
}

///|
fn parallel_assign_phis(r : Node, prior : Node?, arg : Int64) -> Int {
  let prior = match prior {
    Some(p) => p
    None => return 0
  }
  let path = find_input_index(r, prior)
  if path < 0 {
    panic()
  }
  let frame = if r.kind == Fun {
    match current_frame().val.prior {
      Some(p) => p
      None => current_frame()
    }
  } else {
    current_frame()
  }
  let is_main = r.kind == Fun && is_main_fun(r)

  let phi_nodes : Array[Node] = []
  let phi_vals : Array[Eval2Value?] = []
  let mut i = 0
  while i < r._outputs.length() {
    match r._outputs[i] {
      Some(phi) if phi.kind == Phi || phi.kind == Parm => {
        let v = if is_main && phi.kind == Parm && phi._parm_idx == 2 {
          Some(Eval2Value::Int(arg))
        } else {
          let src = if phi.kind == Parm {
            if phi._parm_idx == 0 {
              Some(prior)
            } else if phi._parm_idx >= 0 && phi._parm_idx < prior.n_ins() {
              prior.input(phi._parm_idx)
            } else {
              None
            }
          } else {
            Some(phi.input_exn(path))
          }
          match src {
            Some(s) => frame_get(frame, s)
            None => None
          }
        }
        phi_nodes.push(phi)
        phi_vals.push(v)
      }
      _ => ()
    }
    i = i + 1
  }

  for j = 0; j < phi_nodes.length(); j = j + 1 {
    ignore(frame_put0(current_frame(), phi_nodes[j], phi_vals[j]))
  }
  phi_nodes.length()
}

///|
fn call_end(call : Node) -> Node {
  for use_ in call._outputs {
    match use_ {
      Some(n) if n.kind == CallEnd => return n
      _ => ()
    }
  }
  panic()
}

///|
fn uctrl(cfg : Node) -> Node? {
  match cfg.kind {
    Start => {
      let mut out : Node? = None
      for use_ in cfg._outputs {
        match use_ {
          Some(fun) if fun.kind == Fun && is_main_fun(fun) => out = Some(fun)
          _ => ()
        }
      }
      out
    }
    Call => Some(call_end(cfg))
    Fun => {
      for use_ in cfg._outputs {
        match use_ {
          Some(n) if n.is_cfg() &&
              (n.kind == Region || n.kind == Loop || n.cfg0() == cfg) =>
            return Some(n)
          _ => ()
        }
      }
      None
    }
    _ => {
      let mut out : Node? = None
      for use_ in cfg._outputs {
        match use_ {
          Some(n) if n.is_cfg() => out = Some(n)
          _ => ()
        }
      }
      out
    }
  }
}

///|
fn cproj(iff : Node, idx : Int) -> Node {
  for use_ in iff._outputs {
    match use_ {
      Some(n) if n.kind == CProj && n._proj_idx == idx => return n
      _ => ()
    }
  }
  panic()
}

///|
fn call(call : Node) -> Node {
  let cont = closure_new(call_end(call), current_frame())
  ignore(frame_put(current_frame(), call, Eval2Value::Closure(cont)))
  let new_frame = frame_new(Some(current_frame()))
  set_current_frame(new_frame)
  match link_get(tfp(call.input_exn(call.n_ins() - 1))) {
    Some(fun) => fun
    None => panic()
  }
}

///|
fn ret(ret : Node) -> Node {
  let rez = val(ret.expr())
  let cont = clj(ret.input_exn(3))
  frame_dec(current_frame())
  set_current_frame(cont._frame)
  ignore(frame_put0(current_frame(), cont._cc, rez))
  cont._cc
}

///|
fn exit(ret : Node) -> String {
  pretty_print(ret.expr().ty(), val(ret.expr()))
}

///|
fn step(n : Node) -> Unit {
  if n.kind == Phi || n.kind == Parm {
    return
  }
  ignore(frame_put0(current_frame(), n, compute(n)))
  if n.kind == New {
    for use_ in n._outputs {
      match use_ {
        Some(u) if !u.is_cfg() => step(u)
        _ => ()
      }
    }
  }
}

///|
fn compute(n : Node) -> Eval2Value? {
  match n.kind {
    AddF => Some(Eval2Value::Float(d(n.input_exn(1)) + d(n.input_exn(2))))
    Add => Some(Eval2Value::Int(x(n.input_exn(1)) + x(n.input_exn(2))))
    And => Some(Eval2Value::Int(x(n.input_exn(1)) & x(n.input_exn(2))))
    BoolEqF =>
      Some(
        Eval2Value::Int(
          if d(n.input_exn(1)) == d(n.input_exn(2)) { 1L } else { 0L },
        ),
      )
    BoolEq =>
      Some(
        Eval2Value::Int(
          if val_eq(val(n.input_exn(1)), val(n.input_exn(2))) { 1L } else { 0L },
        ),
      )
    BoolLtF =>
      Some(
        Eval2Value::Int(
          if d(n.input_exn(1)) < d(n.input_exn(2)) { 1L } else { 0L },
        ),
      )
    BoolLt =>
      Some(
        Eval2Value::Int(
          if x(n.input_exn(1)) < x(n.input_exn(2)) { 1L } else { 0L },
        ),
      )
    BoolLeF =>
      Some(
        Eval2Value::Int(
          if d(n.input_exn(1)) <= d(n.input_exn(2)) { 1L } else { 0L },
        ),
      )
    BoolLe =>
      Some(
        Eval2Value::Int(
          if x(n.input_exn(1)) <= x(n.input_exn(2)) { 1L } else { 0L },
        ),
      )
    Cast => val(n.input_exn(1))
    Constant =>
      match n._con {
        Some(con) => con_eval(con)
        None => None
      }
    DivF =>
      if d(n.input_exn(2)) == 0.0 {
        Some(Eval2Value::Float(0.0))
      } else {
        Some(Eval2Value::Float(d(n.input_exn(1)) / d(n.input_exn(2))))
      }
    Div =>
      if x(n.input_exn(2)) == 0L {
        Some(Eval2Value::Int(0L))
      } else {
        Some(Eval2Value::Int(x(n.input_exn(1)) / x(n.input_exn(2))))
      }
    Load => load(n)
    MinusF => Some(Eval2Value::Float(-d(n.input_exn(1))))
    Minus => Some(Eval2Value::Int(-x(n.input_exn(1))))
    MulF => Some(Eval2Value::Float(d(n.input_exn(1)) * d(n.input_exn(2))))
    Mul => Some(Eval2Value::Int(x(n.input_exn(1)) * x(n.input_exn(2))))
    New => alloc(n)
    Not =>
      Some(Eval2Value::Int(if x(n.input_exn(1)) == 0L { 1L } else { 0L }))
    Or => Some(Eval2Value::Int(x(n.input_exn(1)) | x(n.input_exn(2))))
    Proj =>
      match n.ty() {
        Mem(_) => Some(Eval2Value::Str("$mem"))
        _ => val(n.input_exn(0))
      }
    ReadOnly => val(n.input_exn(1))
    Sar =>
      Some(
        Eval2Value::Int(
          x(n.input_exn(1)) >> x(n.input_exn(2)).land(63L).to_int(),
        ),
      )
    Mem => Some(Eval2Value::Str("$mem"))
    Shl =>
      Some(
        Eval2Value::Int(
          x(n.input_exn(1)) << x(n.input_exn(2)).land(63L).to_int(),
        ),
      )
    Shr =>
      Some(
        Eval2Value::Int(
          (x(n.input_exn(1)).reinterpret_as_uint64() >>
            x(n.input_exn(2)).land(63L).to_int())
            .reinterpret_as_int64(),
        ),
      )
    Store => store(n)
    SubF => Some(Eval2Value::Float(d(n.input_exn(1)) - d(n.input_exn(2))))
    Sub => Some(Eval2Value::Int(x(n.input_exn(1)) - x(n.input_exn(2))))
    ToFloat => Some(Eval2Value::Float(x(n.input_exn(1)).to_double()))
    RoundF32 =>
      Some(Eval2Value::Float(Float::from_double(d(n.input_exn(1))).to_double()))
    Xor => Some(Eval2Value::Int(x(n.input_exn(1)) ^ x(n.input_exn(2))))
    _ => panic()
  }
}

///|
fn con_eval(t : Type) -> Eval2Value? {
  match t {
    Int(i) =>
      if i.is_constant() {
        Some(Eval2Value::Int(i.value_exn()))
      } else {
        Some(Eval2Value::Str("INT"))
      }
    Flt(f) =>
      if f.is_constant() {
        Some(Eval2Value::Float(f.value_exn()))
      } else {
        Some(Eval2Value::Str("FLT"))
      }
    MemPtr(_, _) => Some(Eval2Value::TypeVal(t))
    FunPtr(fp) => Some(Eval2Value::FunPtr(fp))
    Mem(_) => Some(Eval2Value::Str("MEM"))
    RPC(_) => Some(Eval2Value::Str("RPC"))
    Nil => None
    _ => None
  }
}

///|
fn off_to_idx(off : Int64, obj : TypeStruct) -> Int {
  let off = off - Int64::from_int(obj.ary_base())
  let scale = obj.ary_scale()
  let mask = (1L << scale) - 1L
  if (off & mask) != 0L {
    panic()
  }
  (off >> scale).to_int()
}

///|
fn alloc(n : Node) -> Eval2Value? {
  let obj = match n._con {
    Some(MemPtr(obj, _)) => obj
    _ => panic()
  }
  let fields = match obj._fields {
    Some(fs) => fs
    None => panic()
  }
  let id = _next_obj_id.val
  _next_obj_id.val = id + 1

  if obj.is_ary() {
    let size = x(n.input_exn(1))
    let len = off_to_idx(size, obj)
    if len < 0 {
      panic()
    }
    let out : Array[Eval2Value?] = Array::make(len, None)
    let elem = fields[1]._type
    match elem {
      Int(_) =>
        for i = 0; i < out.length(); i = i + 1 {
          out[i] = Some(Eval2Value::Int(0L))
        }
      Flt(_) =>
        for i = 0; i < out.length(); i = i + 1 {
          out[i] = Some(Eval2Value::Float(0.0))
        }
      _ => ()
    }
    return Some(Eval2Value::Obj(Ref::{ val: { id, fields: out } }))
  }

  let out : Array[Eval2Value?] = Array::make(fields.length(), None)
  for i = 0; i < fields.length(); i = i + 1 {
    out[i] = con_eval(fields[i]._type.make_zero())
  }
  Some(Eval2Value::Obj(Ref::{ val: { id, fields: out } }))
}

///|
fn load(ld : Node) -> Eval2Value? {
  let obj = match ld.input_exn(2).ty() {
    MemPtr(obj, _) => obj
    _ => panic()
  }
  let ptr = match val(ld.input_exn(2)) {
    Some(Eval2Value::Obj(obj)) => obj
    _ => return None
  }
  if ld._memop_name == "#" {
    return Some(Eval2Value::Int(Int64::from_int(ptr.val.fields.length())))
  }
  let idx = if obj.is_ary() {
    off_to_idx(x(ld.input_exn(3)), obj)
  } else {
    obj.find(ld._memop_name)
  }
  ptr.val.fields[idx]
}

///|
fn store(st : Node) -> Eval2Value? {
  if st._memop_name == "#" {
    return Some(Eval2Value::Str("$mem"))
  }
  let obj = match st.input_exn(2).ty() {
    MemPtr(obj, _) => obj
    _ => panic()
  }
  let ptr = match val(st.input_exn(2)) {
    Some(Eval2Value::Obj(obj)) => obj
    _ => return Some(Eval2Value::Str("$mem"))
  }
  let idx = if obj.is_ary() {
    off_to_idx(x(st.input_exn(3)), obj)
  } else {
    obj.find(st._memop_name)
  }
  ptr.val.fields[idx] = val(st.input_exn(4))
  Some(Eval2Value::Str("$mem"))
}

///|
fn pretty_print(t : Type, v : Eval2Value?) -> String {
  let sb = StringBuilder::new()
  let visit : Map[Int, Bool] = Map::new()
  print_value(t, v, sb, visit)
  sb.to_string()
}

///|
fn print_value(
  t : Type,
  v : Eval2Value?,
  sb : StringBuilder,
  visit : Map[Int, Bool],
) -> Unit {
  match v {
    Some(Eval2Value::Str(s)) => { sb.write_string(s); return }
    Some(Eval2Value::TypeVal(tv)) => { sb.write_string(tv.str()); return }
    None => { sb.write_string("null"); return }
    _ => ()
  }

  match t {
    Int(_) =>
      match v {
        Some(Eval2Value::Int(i)) => sb.write_string(i.to_string())
        _ => sb.write_string("0")
      }
    Flt(_) =>
      match v {
        Some(Eval2Value::Float(f)) => sb.write_string(f.to_string())
        _ => sb.write_string("0.0")
      }
    MemPtr(obj0, _) => {
      let mut obj = obj0
      if obj.is_fref() {
        match types.val.get(obj._name) {
          Some(MemPtr(actual, _)) => obj = actual
          _ => ()
        }
      }
      let ptr = match v {
        Some(Eval2Value::Obj(obj)) => obj
        _ => { sb.write_string("null"); return }
      }
      if visit.contains(ptr.val.id) {
        sb.write_string("$cyclic")
        return
      }
      visit[ptr.val.id] = true

      if obj.is_ary() {
        let elem = match obj._fields {
          Some(fields) => fields[1]._type
          None => panic()
        }
        if elem == type_integer_u8 {
          for item in ptr.val.fields {
            match item {
              Some(Eval2Value::Int(i)) =>
                sb.write_char(i.to_int().unsafe_to_char())
              _ => sb.write_char('\u{0000}')
            }
          }
          return
        }
        elem.print_to(sb)
        sb.write_string("[ ")
        let mut first = true
        for item in ptr.val.fields {
          if !first {
            sb.write_string(",")
          }
          first = false
          print_value(elem, item, sb, visit)
        }
        sb.write_string("]")
        return
      }

      let fields = match obj._fields {
        Some(fields) => fields
        None => { sb.write_string(obj._name); return }
      }
      sb.write_string(obj._name)
      sb.write_string("{")
      let mut first = true
      for i = 0; i < fields.length(); i = i + 1 {
        if !first {
          sb.write_string(",")
        }
        first = false
        sb.write_string(fields[i]._fname)
        sb.write_string("=")
        print_value(fields[i]._type, ptr.val.fields[i], sb, visit)
      }
      sb.write_string("}")
    }
    FunPtr(_) =>
      match v {
        Some(Eval2Value::FunPtr(fp)) => sb.write_string(fp.str())
        Some(Eval2Value::TypeVal(FunPtr(fp))) => sb.write_string(fp.str())
        _ => sb.write_string("null")
      }
    RPC(_) =>
      match v {
        Some(Eval2Value::Closure(c)) => sb.write_string(c._cc.label())
        _ => sb.write_string("null")
      }
    Mem(_) => sb.write_string("$mem")
    Tuple(ts) =>
      match ts {
        Some(types0) if types0.length() > 1 =>
          match types0[1] {
            MemPtr(_, _) => print_value(types0[1], v, sb, visit)
            _ => panic()
          }
        _ => panic()
      }
    Nil => sb.write_string("null")
    _ => sb.write_string("null")
  }
}

///|
pub fn Eval2::eval(code : CodeGen, arg : Int64, loops? : Int = 1000) -> String {
  // Force scheduling before running the interpreter (matches refs/simple intent).
  ignore(code.gcm().local_sched())

  _next_obj_id.val = 1
  let frame = frame_new(None)
  set_current_frame(frame)

  let mut bb = code._start
  let mut prior : Node? = None
  ignore(frame_put(frame, bb, Eval2Value::Closure(closure_new(code._stop, frame))))

  let mut loop_cnt = 0
  while true {
    if bb.kind == Region || bb.kind == Loop || bb.kind == Fun {
      ignore(parallel_assign_phis(bb, prior, arg))
    }

    let outs = bb._outputs
    let mut i = 0
    while i < outs.length() {
      match outs[i] {
        Some(n) if !n.is_cfg() && n.kind != Phi && n.kind != Parm => step(n)
        _ => ()
      }
      i = i + 1
    }

    prior = Some(bb)
    let mut next = uctrl(bb)
    match bb.kind {
      Start => {
        let new_frame = frame_new(Some(current_frame()))
        set_current_frame(new_frame)
      }
      Call => next = Some(call(bb))
      If => {
        let pred = val(bb.input_exn(1))
        let false_branch = match pred {
          None => true
          Some(Eval2Value::Int(i)) => i == 0L
          _ => false
        }
        next = Some(cproj(bb, if false_branch { 1 } else { 0 }))
      }
      Return => {
        let cont = clj(bb.input_exn(3))
        if closure_is_stop(cont) {
          return exit(bb)
        }
        next = Some(ret(bb))
      }
      Fun | Loop => {
        loop_cnt += 1
        if loop_cnt > loops {
          return "null"
        }
      }
      CallEnd | CProj | Region => ()
      _ => panic()
    }

    bb = match next {
      Some(n) => n
      None => panic()
    }
    if bb.is_dead() {
      panic()
    }
  }
  panic()
}
