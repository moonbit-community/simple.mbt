///|
pub enum NodeKind {
  Start
  Stop
  Return
  Constant
  XCtrl
  Mem
  Struct
  New
  Load
  Store
  Cast
  ReadOnly
  ToFloat
  RoundF32
  Add
  AddF
  Sub
  SubF
  Mul
  MulF
  Div
  DivF
  Minus
  MinusF
  Not
  Shl
  Shr
  Sar
  And
  Or
  Xor
  If
  Never
  CProj
  Proj
  BoolEq
  BoolEqF
  BoolLt
  BoolLtF
  BoolLe
  BoolLeF
  Region
  Loop
  Phi
  Scope
} derive(Eq, Show)

///|
pub struct Var {
  _idx : Int
  _name : String
  _type : Type
  _final : Bool
} derive(Eq)

///|
pub struct Node {
  _nid : Int
  mut _inputs : Array[Node?]
  mut _outputs : Array[Node?]
  mut _type : Type?
  mut _idepth : Int
  mut _idom : Node?
  mut _loop_depth : Int
  mut _anti : Int
  mut _deps : Array[Node]?
  mut _hash : Int
  kind : NodeKind
  mut _con : Type?
  mut _scopes : Array[Map[String, Int]]
  mut _types : Array[Map[String, Type]]
  mut _vars : Array[Var]
  mut _lex_size : Array[Int]
  mut _in_cons : Array[Bool]
  mut _guards : Array[Node]
  mut _proj_idx : Int
  mut _proj_label : String
  mut _start_args : Array[Type]
  mut _alias_starts : Map[String, Int]
  mut _phi_label : String
  mut _declared_type : Type
  mut _memop_name : String
  mut _memop_alias : Int
  mut _memop_init : Bool
  mut _struct_ts : TypeStruct?
}

///|
pub let scope_ctrl : String = "$ctrl"

///|
pub let scope_mem0 : String = "$mem"

///|
pub let scope_arg0 : String = "arg"

///|
let _unique_id : Ref[Int] = Ref::{ val: 1 }

///|
pub let start : Ref[Node] = Ref::{
  val: Node::new_start([control, type_integer_bot]),
}

///|
pub let zero : Ref[Node] = Ref::{ val: Node::new_constant(type_integer_zero) }

///|
pub let xctrl : Ref[Node] = Ref::{
  val: Node::new_raw(XCtrl, [Some(start.val)]),
}

///|
pub let disable_peephole : Ref[Bool] = Ref::{ val: false }

///|
let gvn : Ref[Map[Int, Array[Node]]] = Ref::{ val: Map::new() }

///|
pub let iter_cnt : Ref[Int] = Ref::{ val: 0 }

///|
pub let iter_nop_cnt : Ref[Int] = Ref::{ val: 0 }

///|
pub fn Node::reset() -> Unit {
  _unique_id.val = 1
  disable_peephole.val = false
  gvn.val = Map::new()
  iter_cnt.val = 0
  iter_nop_cnt.val = 0
}

///|
pub fn Node::uid() -> Int {
  _unique_id.val
}

///|
fn _find_use(ary : Array[Node?], node : Node?) -> Int {
  for i, x in ary {
    match (x, node) {
      (None, None) => return i
      (Some(n0), Some(n1)) if n0._nid == n1._nid => return i
      _ => ()
    }
  }
  -1
}

///|
fn[T] _del(ary : Array[T], i : Int) -> T? {
  let len = ary.length()
  if i >= 0 && i < len {
    let tmp = ary[i]
    let last = ary.remove(len - 1)
    if i < ary.length() {
      ary[i] = last
    }
    Some(tmp)
  } else {
    None
  }
}

///|
fn Node::new_raw(kind : NodeKind, inputs : Array[Node?]) -> Node {
  let nid = _unique_id.val
  _unique_id.val += 1
  let node : Node = {
    _nid: nid,
    _inputs: inputs,
    _outputs: [],
    _type: None,
    _idepth: 0,
    _idom: None,
    _loop_depth: 0,
    _anti: 0,
    _deps: None,
    _hash: 0,
    kind,
    _con: None,
    _scopes: [],
    _types: [],
    _vars: [],
    _lex_size: [],
    _in_cons: [],
    _guards: [],
    _proj_idx: 0,
    _proj_label: "",
    _start_args: [],
    _alias_starts: Map::new(),
    _phi_label: "",
    _declared_type: bottom,
    _memop_name: "",
    _memop_alias: 0,
    _memop_init: false,
    _struct_ts: None,
  }
  for input in node._inputs {
    match input {
      Some(n) => n._outputs.push(Some(node))
      None => ()
    }
  }
  node
}

///|
pub fn Node::new_start(args : Array[Type]) -> Node {
  let node = Node::new_raw(Start, [])
  node._start_args = args
  node._type = Some(Tuple(Some(args)))
  node
}

///|
pub fn Node::new_stop() -> Node {
  Node::new_raw(Stop, [])
}

///|
pub fn Node::new_return0(ctrl : Node?, data : Node) -> Node {
  Node::new_raw(Return, [ctrl, Some(data)])
}

///|
pub fn Node::new_return(ctrl : Node?, data : Node, scope : Node) -> Node {
  let node = Node::new_raw(Return, [ctrl, Some(data)])
  if scope.kind != Scope {
    panic()
  }
  let mem = scope.mem()
  for i = 2; i < mem.n_ins(); i = i + 1 {
    ignore(node.add_def(mem.input(i)))
  }
  node
}

///|
pub fn Node::new_constant(con : Type) -> Node {
  let node = Node::new_raw(Constant, [Some(start.val)])
  node._con = Some(con)
  node
}

///|
pub fn Node::new_xctrl() -> Node {
  Node::new_raw(XCtrl, [Some(start.val)])
}

///|
pub fn Node::new_new(
  ptr : Type,
  ctrl : Node,
  size : Node,
  mems : Array[Node],
  inits : Array[Node],
) -> Node {
  let inputs : Array[Node?] = [Some(ctrl), Some(size)]
  for mem in mems {
    inputs.push(Some(mem))
  }
  for init in inits {
    inputs.push(Some(init))
  }
  let node = Node::new_raw(New, inputs)
  node._con = Some(ptr)
  node
}

///|
pub fn Node::new_load(
  name : String,
  mem_alias : Int,
  declared_type : Type,
  mem_slice : Node,
  mem_ptr : Node,
  mem_off : Node,
) -> Node {
  let node = Node::new_raw(Load, [
    None,
    Some(mem_slice),
    Some(mem_ptr),
    Some(mem_off),
  ])
  node._memop_name = name
  node._memop_alias = mem_alias
  node._declared_type = declared_type
  node
}

///|
pub fn Node::new_store(
  name : String,
  mem_alias : Int,
  declared_type : Type,
  mem_slice : Node,
  mem_ptr : Node,
  mem_off : Node,
  value : Node,
  init? : Bool = false,
) -> Node {
  let node = Node::new_raw(Store, [
    None,
    Some(mem_slice),
    Some(mem_ptr),
    Some(mem_off),
    Some(value),
  ])
  node._memop_name = name
  node._memop_alias = mem_alias
  node._declared_type = declared_type
  node._memop_init = init
  node
}

///|
pub fn Node::new_cast(t : Type, ctrl : Node?, input : Node) -> Node {
  let node = Node::new_raw(Cast, [ctrl, Some(input)])
  node._declared_type = t
  node
}

///|
pub fn Node::new_read_only(input : Node) -> Node {
  Node::new_raw(ReadOnly, [None, Some(input)])
}

///|
pub fn Node::new_to_float(input : Node) -> Node {
  Node::new_raw(ToFloat, [None, Some(input)])
}

///|
pub fn Node::new_round_f32(input : Node) -> Node {
  Node::new_raw(RoundF32, [None, Some(input)])
}

///|
pub fn Node::new_add(lhs : Node, rhs : Node) -> Node {
  Node::new_raw(Add, [None, Some(lhs), Some(rhs)])
}

///|
pub fn Node::new_addf(lhs : Node, rhs : Node) -> Node {
  Node::new_raw(AddF, [None, Some(lhs), Some(rhs)])
}

///|
pub fn Node::new_sub(lhs : Node, rhs : Node) -> Node {
  Node::new_raw(Sub, [None, Some(lhs), Some(rhs)])
}

///|
pub fn Node::new_subf(lhs : Node, rhs : Node) -> Node {
  Node::new_raw(SubF, [None, Some(lhs), Some(rhs)])
}

///|
pub fn Node::new_mul(lhs : Node, rhs : Node) -> Node {
  Node::new_raw(Mul, [None, Some(lhs), Some(rhs)])
}

///|
pub fn Node::new_mulf(lhs : Node, rhs : Node) -> Node {
  Node::new_raw(MulF, [None, Some(lhs), Some(rhs)])
}

///|
pub fn Node::new_div(lhs : Node, rhs : Node) -> Node {
  Node::new_raw(Div, [None, Some(lhs), Some(rhs)])
}

///|
pub fn Node::new_divf(lhs : Node, rhs : Node) -> Node {
  Node::new_raw(DivF, [None, Some(lhs), Some(rhs)])
}

///|
pub fn Node::new_minus(input : Node) -> Node {
  Node::new_raw(Minus, [None, Some(input)])
}

///|
pub fn Node::new_minusf(input : Node) -> Node {
  Node::new_raw(MinusF, [None, Some(input)])
}

///|
pub fn Node::new_not(input : Node) -> Node {
  Node::new_raw(Not, [None, Some(input)])
}

///|
pub fn Node::new_shl(lhs : Node, rhs : Node) -> Node {
  Node::new_raw(Shl, [None, Some(lhs), Some(rhs)])
}

///|
pub fn Node::new_shr(lhs : Node, rhs : Node) -> Node {
  Node::new_raw(Shr, [None, Some(lhs), Some(rhs)])
}

///|
pub fn Node::new_sar(lhs : Node, rhs : Node) -> Node {
  Node::new_raw(Sar, [None, Some(lhs), Some(rhs)])
}

///|
pub fn Node::new_and(lhs : Node, rhs : Node) -> Node {
  Node::new_raw(And, [None, Some(lhs), Some(rhs)])
}

///|
pub fn Node::new_or(lhs : Node, rhs : Node) -> Node {
  Node::new_raw(Or, [None, Some(lhs), Some(rhs)])
}

///|
pub fn Node::new_xor(lhs : Node, rhs : Node) -> Node {
  Node::new_raw(Xor, [None, Some(lhs), Some(rhs)])
}

///|
pub fn Node::new_if(ctrl : Node?, pred : Node) -> Node {
  Node::new_raw(If, [ctrl, Some(pred)])
}

///|
pub fn Node::new_never(ctrl : Node) -> Node {
  Node::new_raw(Never, [Some(ctrl), Some(zero.val)])
}

///|
pub fn Node::new_cproj(ctrl : Node, idx : Int, label : String) -> Node {
  let node = Node::new_raw(CProj, [Some(ctrl)])
  node._proj_idx = idx
  node._proj_label = label
  node
}

///|
pub fn Node::new_proj(ctrl : Node, idx : Int, label : String) -> Node {
  let node = Node::new_raw(Proj, [Some(ctrl)])
  node._proj_idx = idx
  node._proj_label = label
  node
}

///|
pub fn Node::new_bool_eq(lhs : Node, rhs : Node) -> Node {
  Node::new_raw(BoolEq, [None, Some(lhs), Some(rhs)])
}

///|
pub fn Node::new_bool_eqf(lhs : Node, rhs : Node) -> Node {
  Node::new_raw(BoolEqF, [None, Some(lhs), Some(rhs)])
}

///|
pub fn Node::new_bool_lt(lhs : Node, rhs : Node) -> Node {
  Node::new_raw(BoolLt, [None, Some(lhs), Some(rhs)])
}

///|
pub fn Node::new_bool_ltf(lhs : Node, rhs : Node) -> Node {
  Node::new_raw(BoolLtF, [None, Some(lhs), Some(rhs)])
}

///|
pub fn Node::new_bool_le(lhs : Node, rhs : Node) -> Node {
  Node::new_raw(BoolLe, [None, Some(lhs), Some(rhs)])
}

///|
pub fn Node::new_bool_lef(lhs : Node, rhs : Node) -> Node {
  Node::new_raw(BoolLeF, [None, Some(lhs), Some(rhs)])
}

///|
pub fn Node::new_region(ctrl0 : Node?, ctrl1 : Node?) -> Node {
  Node::new_raw(Region, [None, ctrl0, ctrl1])
}

///|
pub fn Node::new_loop(entry : Node?) -> Node {
  Node::new_raw(Loop, [None, entry, None])
}

///|
pub fn Node::new_phi(
  label : String,
  declared_type : Type,
  inputs : Array[Node?],
) -> Node {
  let node = Node::new_raw(Phi, inputs)
  node._phi_label = label
  node._declared_type = declared_type
  node
}

///|
pub fn Node::new_scope() -> Node {
  let node = Node::new_raw(Scope, [])
  node._type = Some(bottom)
  node
}

///|
pub fn Node::new_mem() -> Node {
  let node = Node::new_raw(Mem, [])
  node._type = Some(type_mem_bot)
  node
}

///|
pub fn Node::new_struct() -> Node {
  Node::new_raw(Struct, [])
}

///|
pub fn Node::label(self : Node) -> String {
  match self.kind {
    Start => "Start"
    Stop => "Stop"
    Return => "Return"
    Constant =>
      match self._con {
        Some(con) => "\{con}"
        None => "\{bottom}"
      }
    XCtrl => "Xctrl"
    Mem => "MEM"
    Struct =>
      match self._struct_ts {
        Some(ts) => ts.str()
        None => "STRUCT?"
      }
    New => "new"
    Load => self._memop_name
    Store => ".\{self._memop_name}="
    Cast => "(\{self._declared_type.str()})"
    ReadOnly => "ReadOnly"
    ToFloat => "ToFloat"
    RoundF32 => "RoundF32"
    Add => "Add"
    AddF => "AddF"
    Sub => "Sub"
    SubF => "SubF"
    Mul => "Mul"
    MulF => "MulF"
    Div => "Div"
    DivF => "DivF"
    Minus => "Minus"
    MinusF => "MinusF"
    Not => "Not"
    Shl => "Shl"
    Shr => "Shr"
    Sar => "Sar"
    And => "And"
    Or => "Or"
    Xor => "Xor"
    If => "If"
    Never => "Never"
    CProj => self._proj_label
    Proj => self._proj_label
    BoolEq => "EQ"
    BoolEqF => "EQF"
    BoolLt => "LT"
    BoolLtF => "LTF"
    BoolLe => "LE"
    BoolLeF => "LEF"
    Region => "Region"
    Loop => "Loop"
    Phi => "Phi_\{self._phi_label}"
    Scope => "Scope"
  }
}

///|
pub fn Node::unique_name(self : Node) -> String {
  match self.kind {
    Constant => "Con_\{self._nid}"
    _ => "\{self.label()}\{self._nid}"
  }
}

///|
pub fn Node::glabel(self : Node) -> String {
  match self.kind {
    New =>
      match self._con {
        Some(MemPtr(obj, _)) => "new \{obj.str()}"
        _ => "new"
      }
    ToFloat => "(flt)"
    RoundF32 => "(f32)"
    Add => "+"
    AddF => "+"
    Sub => "-"
    SubF => "-"
    Mul => "*"
    MulF => "*"
    Div => "//"
    DivF => "/"
    Minus => "-"
    MinusF => "-"
    Not => "!"
    Shl => "<<"
    Shr => ">>>"
    Sar => ">>"
    And => "&"
    Or => "|"
    Xor => "^"
    Load => ".\{self._memop_name}"
    Store => ".\{self._memop_name}="
    BoolEq => "=="
    BoolEqF => "=="
    BoolLt => "<"
    BoolLtF => "<"
    BoolLe => "<="
    BoolLeF => "<="
    Phi => "&phi;_\{self._phi_label}"
    _ => self.label()
  }
}

///|
pub fn Node::input(self : Node, i : Int) -> Node? {
  self._inputs[i]
}

///|
pub fn Node::input_exn(self : Node, i : Int) -> Node {
  match self._inputs[i] {
    Some(n) => n
    None => panic()
  }
}

///|
pub fn Node::n_ins(self : Node) -> Int {
  self._inputs.length()
}

///|
pub fn Node::n_outs(self : Node) -> Int {
  self._outputs.length()
}

///|
pub fn Node::is_unused(self : Node) -> Bool {
  self.n_outs() == 0
}

///|
pub fn Node::is_cfg(self : Node) -> Bool {
  match self.kind {
    Start | Stop | Return | If | Never | Region | Loop | CProj | XCtrl => true
    _ => false
  }
}

///|
pub fn Node::is_pinned(self : Node) -> Bool {
  if self.is_cfg() {
    return true
  }
  match self.kind {
    Phi | Proj | New | Cast => true
    Constant => self == zero.val
    _ => false
  }
}

///|
pub fn Node::block_head(self : Node) -> Bool {
  match self.kind {
    Start | Stop | Region | Loop | CProj => true
    _ => false
  }
}

///|
pub fn Node::cfg0(self : Node) -> Node {
  match self.kind {
    Start => self
    Proj => self.input_exn(0).cfg0()
    _ => self.input_exn(0)
  }
}

///|
pub fn Node::ctrl(self : Node) -> Node {
  self.input_exn(0)
}

///|
pub fn Node::expr(self : Node) -> Node {
  self.input_exn(1)
}

///|
fn Node::add_use(self : Node, user : Node?) -> Unit {
  self._outputs.push(user)
}

///|
fn Node::del_use(self : Node, user : Node?) -> Bool {
  let idx = _find_use(self._outputs, user)
  ignore(_del(self._outputs, idx))
  self._outputs.length() == 0
}

///|
pub fn Node::set_def(self : Node, idx : Int, new_def : Node?) -> Node? {
  self.unlock()
  let old_def = self._inputs[idx]
  if old_def is Some(old) && new_def is Some(new_) && old._nid == new_._nid {
    return new_def
  }
  if old_def is None && new_def is None {
    return new_def
  }
  match new_def {
    Some(n) => n.add_use(Some(self))
    None => ()
  }
  match old_def {
    Some(old) => if old.del_use(Some(self)) { old.kill() }
    None => ()
  }
  self._inputs[idx] = new_def
  new_def
}

///|
pub fn Node::del_def(self : Node, idx : Int) -> Node {
  self.unlock()
  let old_def = self._inputs[idx]
  match old_def {
    Some(old) => {
      if old.del_use(Some(self)) {
        old.kill()
      }
      old.move_deps_to_worklist()
    }
    None => ()
  }
  let last = self._inputs.remove(self._inputs.length() - 1)
  if idx < self._inputs.length() {
    self._inputs[idx] = last
  }
  self
}

///|
pub fn Node::add_def(self : Node, new_def : Node?) -> Node? {
  self.unlock()
  self._inputs.push(new_def)
  match new_def {
    Some(n) => n.add_use(Some(self))
    None => ()
  }
  new_def
}

///|
pub fn Node::pop_n(self : Node, n : Int) -> Unit {
  self.unlock()
  for _i = 0; _i < n; _i = _i + 1 {
    let old_def = self._inputs.remove(self._inputs.length() - 1)
    match old_def {
      Some(old) => if old.del_use(Some(self)) { old.kill() }
      None => ()
    }
  }
}

///|
pub fn Node::kill(self : Node) -> Unit {
  self.unlock()
  if !self.is_unused() {
    panic()
  }
  // Scope carries guard keepers that must be released when abandoning the scope.
  if self.kind == Scope {
    for g in self._guards {
      if !g.is_cfg() {
        ignore(g.unkeep())
      }
    }
    self._guards = []
  }
  self._type = None
  while self.n_ins() > 0 {
    let old_def = self._inputs.remove(self._inputs.length() - 1)
    match old_def {
      Some(old) => {
        ignore(IterPeeps::add(old))
        if old.del_use(Some(self)) {
          old.kill()
        }
      }
      None => ()
    }
  }
  if !self.is_dead() {
    panic()
  }
}

///|
pub fn Node::is_dead(self : Node) -> Bool {
  self.is_unused() && self.n_ins() == 0 && self._type is None
}

///|
pub fn Node::keep(self : Node) -> Node {
  self.add_use(None)
  self
}

///|
pub fn Node::unkeep(self : Node) -> Node {
  ignore(self.del_use(None))
  self
}

///|
fn Node::subsume(self : Node, nnn : Node) -> Unit {
  if nnn == self {
    panic()
  }
  while self._outputs.length() > 0 {
    let user = self._outputs.remove(self._outputs.length() - 1)
    match user {
      None => nnn.add_use(None)
      Some(n) => {
        n.unlock()
        let idx = _find_use(n._inputs, Some(self))
        if idx < 0 {
          panic()
        }
        n._inputs[idx] = Some(nnn)
        nnn.add_use(Some(n))
      }
    }
  }
  self.kill()
}

///|
fn Node::dead_code_elim(self : Node, m : Node) -> Node {
  if m._nid != self._nid && self.is_unused() {
    ignore(m.keep())
    self.kill()
    ignore(m.unkeep())
  }
  m
}

///|
fn Node::eq_gvn(self : Node, other : Node) -> Bool {
  match self.kind {
    Constant => self._con == other._con
    CProj | Proj => self._proj_idx == other._proj_idx
    Region | Loop | Phi => !self.in_progress()
    New => false
    Load | Store => self._memop_alias == other._memop_alias
    _ => true
  }
}

///|
fn Node::hash_gvn(self : Node) -> Int {
  match self.kind {
    Constant =>
      match self._con {
        Some(con) => con.hash_code()
        None => 0
      }
    CProj | Proj => self._proj_idx
    New =>
      match self._con {
        Some(con) => con.hash_code()
        None => 0
      }
    Load | Store => self._memop_alias
    _ => 0
  }
}

///|
fn Node::hash_code(self : Node) -> Int {
  if self._hash != 0 {
    return self._hash
  }
  let mut hash = self.hash_gvn()
  for input in self._inputs {
    match input {
      Some(n) => hash = hash ^ (hash << 17) ^ (hash >> 13) ^ n._nid
      None => ()
    }
  }
  if hash == 0 {
    hash = -559038737
  }
  self._hash = hash
  hash
}

///|
fn Node::gvn_equals(self : Node, other : Node) -> Bool {
  if self.kind != other.kind {
    return false
  }
  if self.n_ins() != other.n_ins() {
    return false
  }
  for i = 0; i < self.n_ins(); i = i + 1 {
    match (self._inputs[i], other._inputs[i]) {
      (None, None) => ()
      (Some(n0), Some(n1)) if n0 == n1 => ()
      _ => return false
    }
  }
  self.eq_gvn(other)
}

///|
fn Node::unlock(self : Node) -> Unit {
  if self._hash == 0 {
    return
  }
  let h = self._hash
  match gvn.val.get(h) {
    None => ()
    Some(bucket) =>
      for i = 0; i < bucket.length(); i = i + 1 {
        if bucket[i] == self {
          ignore(_del(bucket, i))
          break
        }
      }
  }
  self._hash = 0
}

///|
fn Node::gvn_get(self : Node) -> Node? {
  let h = self.hash_code()
  match gvn.val.get(h) {
    None => None
    Some(bucket) => {
      for n in bucket {
        if n.gvn_equals(self) {
          return Some(n)
        }
      }
      None
    }
  }
}

///|
fn Node::gvn_put(self : Node) -> Unit {
  let h = if self._hash == 0 { self.hash_code() } else { self._hash }
  let bucket = match gvn.val.get(h) {
    Some(b) => b
    None => {
      let b : Array[Node] = []
      gvn.val[h] = b
      b
    }
  }
  bucket.push(self)
}

///|
fn Node::swap12(self : Node) -> Node {
  self.unlock()
  let tmp = self._inputs[1]
  self._inputs[1] = self._inputs[2]
  self._inputs[2] = tmp
  self
}

///|
pub fn Node::ty(self : Node) -> Type {
  match self._type {
    Some(t) => t
    None => bottom
  }
}

///|
fn _is_int_type(t : Type) -> Bool {
  match t {
    Int(_) => true
    _ => false
  }
}

///|
fn _is_float_type(t : Type) -> Bool {
  match t {
    Flt(_) => true
    _ => false
  }
}

///|
fn _add_overflow(x : Int64, y : Int64) -> Bool {
  if (x ^ y) < 0L {
    return false
  }
  (x ^ (x + y)) < 0L
}

///|
fn _unsigned_shift_right(x : Int64, shift : Int64) -> Int64 {
  let sh = shift.land(63L).to_int()
  (x.reinterpret_as_uint64() >> sh).reinterpret_as_int64()
}

///|
fn Node::bool_do_op(self : Node, lhs : Int64, rhs : Int64) -> Bool {
  match self.kind {
    BoolEq | BoolEqF => lhs == rhs
    BoolLt | BoolLtF => lhs < rhs
    BoolLe | BoolLeF => lhs <= rhs
    _ => false
  }
}

///|
fn Node::bool_do_op_f(self : Node, lhs : Double, rhs : Double) -> Bool {
  match self.kind {
    BoolEqF => lhs == rhs
    BoolLtF => lhs < rhs
    BoolLeF => lhs <= rhs
    _ => false
  }
}

///|
fn Node::has_float_input(self : Node) -> Bool {
  for i = 1; i < self.n_ins(); i = i + 1 {
    match self.input(i) {
      Some(n) if _is_float_type(n.ty()) => return true
      _ => ()
    }
  }
  false
}

///|
fn Node::copy_f(self : Node) -> Node? {
  match self.kind {
    Add => Some(Node::new_raw(AddF, [None, None, None]))
    Sub => Some(Node::new_raw(SubF, [None, None, None]))
    Mul => Some(Node::new_raw(MulF, [None, None, None]))
    Div => Some(Node::new_raw(DivF, [None, None, None]))
    Minus => Some(Node::new_raw(MinusF, [None, None]))
    BoolEq => Some(Node::new_raw(BoolEqF, [None, None, None]))
    BoolLt => Some(Node::new_raw(BoolLtF, [None, None, None]))
    BoolLe => Some(Node::new_raw(BoolLeF, [None, None, None]))
    _ => None
  }
}

///|
pub fn Node::widen(self : Node) -> Node {
  if !self.has_float_input() {
    return self
  }
  match self.copy_f() {
    None => self
    Some(flt) => {
      for i = 1; i < self.n_ins(); i = i + 1 {
        let inp = self.input_exn(i)
        let widened = if _is_float_type(inp.ty()) {
          inp
        } else {
          Node::new_to_float(inp).peephole()
        }
        ignore(flt.set_def(i, Some(widened)))
      }
      self.kill()
      flt
    }
  }
}

///|
fn Node::all_cons(self : Node, dep : Node) -> Bool {
  if self.kind == Phi {
    match self.input(0) {
      Some(region) =>
        if region.kind != Region && region.kind != Loop {
          return false
        } else {
          ignore(self.add_dep(dep))
          if region.in_progress() {
            return false
          }
        }
      None => return false
    }
  }
  for i = 1; i < self.n_ins(); i = i + 1 {
    match self._inputs[i] {
      Some(n) =>
        if !n.ty().is_constant() {
          ignore(n.add_dep(dep))
          return false
        }
      None => return false
    }
  }
  true
}

///|
fn Node::add_dep(self : Node, dep : Node) -> Node {
  if IterPeeps::mid_assert() {
    return self
  }
  match self._deps {
    None => self._deps = Some([])
    Some(_) => ()
  }
  let deps = match self._deps {
    Some(d) => d
    None => panic()
  }
  for d in deps {
    if d == dep {
      return self
    }
  }
  if _find_use(self._inputs, Some(dep)) >= 0 {
    return self
  }
  if _find_use(self._outputs, Some(dep)) >= 0 {
    return self
  }
  deps.push(dep)
  self
}

///|
pub fn Node::move_deps_to_worklist(self : Node) -> Unit {
  match self._deps {
    None => ()
    Some(deps) => {
      IterPeeps::add_all_nodes(deps)
      self._deps = Some([])
    }
  }
}

///|
fn Node::in_progress(self : Node) -> Bool {
  match self.kind {
    Region | Loop | Phi =>
      if self.n_ins() > 0 {
        self.input(self.n_ins() - 1) is None
      } else {
        false
      }
    _ => false
  }
}

///|
fn Node::copy(self : Node, lhs : Node, rhs : Node) -> Node {
  match self.kind {
    Add => Node::new_add(lhs, rhs)
    AddF => Node::new_addf(lhs, rhs)
    And => Node::new_and(lhs, rhs)
    Or => Node::new_or(lhs, rhs)
    Xor => Node::new_xor(lhs, rhs)
    Sub => Node::new_sub(lhs, rhs)
    SubF => Node::new_subf(lhs, rhs)
    Mul => Node::new_mul(lhs, rhs)
    MulF => Node::new_mulf(lhs, rhs)
    Div => Node::new_div(lhs, rhs)
    DivF => Node::new_divf(lhs, rhs)
    BoolEq => Node::new_bool_eq(lhs, rhs)
    BoolEqF => Node::new_bool_eqf(lhs, rhs)
    BoolLt => Node::new_bool_lt(lhs, rhs)
    BoolLtF => Node::new_bool_ltf(lhs, rhs)
    BoolLe => Node::new_bool_le(lhs, rhs)
    BoolLeF => Node::new_bool_lef(lhs, rhs)
    _ => panic()
  }
}

///|
fn Node::idepth(self : Node) -> Int {
  match self.kind {
    Start => 0
    _ =>
      if self._idepth != 0 {
        self._idepth
      } else {
        let mut d = 0
        match self.kind {
          Stop | Region =>
            for input in self._inputs {
              match input {
                Some(cfg) => {
                  let v = cfg.idepth() + 1
                  if v > d {
                    d = v
                  }
                }
                None => ()
              }
            }
          Loop =>
            match self.input(1) {
              Some(entry) => d = entry.idepth() + 1
              None => ()
            }
          _ =>
            match self.idom() {
              Some(idom) => d = idom.idepth() + 1
              None => ()
            }
        }
        self._idepth = d
        d
      }
  }
}

///|
fn Node::idom_lca(self : Node, rhs : Node?) -> Node {
  match rhs {
    None => self
    Some(rhs0) => {
      let mut lhs = self
      let mut rhs = rhs0
      while lhs != rhs {
        let comp = lhs.idepth() - rhs.idepth()
        if comp >= 0 {
          match lhs.idom() {
            Some(next) => lhs = next
            None => break
          }
        }
        if comp <= 0 {
          match rhs.idom() {
            Some(next) => rhs = next
            None => break
          }
        }
      }
      lhs
    }
  }
}

///|
fn Node::idom(self : Node) -> Node? {
  match self.kind {
    Start | Stop => None
    Region => self.region_idom()
    Loop => self.input(1)
    _ => self.input(0)
  }
}

///|
fn Node::region_idom(self : Node) -> Node? {
  let mut lca : Node? = None
  for i = 1; i < self.n_ins(); i = i + 1 {
    match self.input(i) {
      Some(cfg) => lca = Some(cfg.idom_lca(lca))
      None => ()
    }
  }
  lca
}

///|
fn Node::loop_depth(self : Node) -> Int {
  if self._loop_depth != 0 {
    return self._loop_depth
  }
  match self.kind {
    Start | Stop => {
      self._loop_depth = 1
      1
    }
    Region =>
      match self.input(1) {
        Some(entry) => {
          let d = entry.loop_depth()
          self._loop_depth = d
          d
        }
        None => {
          self._loop_depth = 1
          1
        }
      }
    Loop => {
      let entry = match self.input(1) {
        Some(entry) => entry
        None => {
          self._loop_depth = 1
          return 1
        }
      }
      let depth = entry.loop_depth() + 1
      self._loop_depth = depth
      match self.input(2) {
        Some(idom0) => {
          let mut idom = idom0
          while idom != self {
            idom._loop_depth = depth
            if idom.kind == CProj {
              let iff = idom.input_exn(0)
              for use_ in iff._outputs {
                match use_ {
                  Some(proj2) if proj2.kind == CProj && proj2 != idom =>
                    proj2._loop_depth = depth - 1
                  _ => ()
                }
              }
            }
            match idom.idom() {
              Some(next) => idom = next
              None => break
            }
          }
        }
        None => ()
      }
      depth
    }
    _ =>
      match self.input(0) {
        Some(idom) => {
          let d = idom.loop_depth()
          self._loop_depth = d
          d
        }
        None => {
          self._loop_depth = 1
          1
        }
      }
  }
}

///|
fn Node::force_exit(self : Node, stop : Node) -> Unit {
  if self.kind != Loop {
    panic()
  }
  let back = match self.input(2) {
    Some(back) => back
    None => return
  }
  let other_cproj = fn(iff : Node, idx : Int) -> Node? {
    for use_ in iff._outputs {
      match use_ {
        Some(proj) if proj.kind == CProj && proj._proj_idx == idx =>
          return Some(proj)
        _ => ()
      }
    }
    None
  }

  // If we find a loop exit on the backedge walk, this is not an infinite loop.
  // Match the reference: an If-side-exit is an exit if the other branch is at a
  // shallower loop depth.
  let self_depth = self.loop_depth()
  let mut x = back
  while x != self {
    if x.kind == CProj {
      let exit = x
      let iff = exit.input_exn(0)
      if iff.kind == If {
        match other_cproj(iff, 1 - exit._proj_idx) {
          Some(other) if other.loop_depth() < self_depth => return
          _ => ()
        }
      }
    }
    match x.idom() {
      Some(next) => x = next
      None => return
    }
  }
  let iff = Node::new_never(back)
  for use_ in self._outputs {
    match use_ {
      Some(phi) if phi.kind == Phi => ignore(iff.add_def(Some(phi)))
      _ => ()
    }
  }
  let t = Node::new_cproj(iff, 0, "True")
  let f = Node::new_cproj(iff, 1, "False")
  ignore(self.set_def(2, Some(f)))
  ignore(stop.add_return(Node::new_return0(Some(t), zero.val)))
}

///|
pub fn Node::compute(self : Node) -> Type {
  match self.kind {
    Start =>
      match self._type {
        Some(t) => t
        None => Tuple(Some(self._start_args))
      }
    Stop | Scope => bottom
    Mem => type_mem_bot
    Struct => bottom
    Return => {
      let ctrl_ty = match self._inputs[0] {
        Some(n) => n.ty()
        None => bottom
      }
      let expr_ty = match self._inputs[1] {
        Some(n) => n.ty()
        None => bottom
      }
      Tuple(Some([ctrl_ty, expr_ty]))
    }
    Constant =>
      match self._con {
        Some(con) => con
        None => bottom
      }
    XCtrl => xcontrol
    New =>
      match self._con {
        Some(MemPtr(obj, nil)) =>
          match obj._fields {
            None => bottom
            Some(fs) => {
              let ts : Array[Type] = Array::make(fs.length() + 2, bottom)
              ts[0] = control
              ts[1] = MemPtr(obj, nil)
              let len = fs.length()
              for i = 0; i < len; i = i + 1 {
                let f = fs[i]
                let mem = self.input_exn(i + 2).ty()
                let init = self.input_exn(2 + len + i).ty()
                let tfld = match mem {
                  Mem(m) => init.meet(m._t)
                  _ => init
                }
                ts[i + 2] = Type::mem(f._alias, t=tfld)
              }
              Tuple(Some(ts))
            }
          }
        _ => bottom
      }
    Load =>
      match self.input_exn(1).ty() {
        Mem(mem) =>
          if self._declared_type != mem._t && self.err() is None {
            self._declared_type.join(mem._t)
          } else {
            self._declared_type
          }
        _ => self._declared_type
      }
    Store => {
      let val_ty = self.input_exn(4).ty()
      match self.input_exn(1).ty() {
        Mem(mem) => {
          let t = if mem._alias == self._memop_alias {
            val_ty.meet(mem._t)
          } else {
            bottom
          }
          Type::mem(self._memop_alias, t~)
        }
        _ => type_mem_bot
      }
    }
    Cast => self.input_exn(1).ty().join(self._declared_type)
    ReadOnly => self.input_exn(1).ty().make_ro()
    ToFloat => {
      let t1 = self.input_exn(1).ty()
      match t1 {
        Int(i) =>
          if i.is_constant() {
            TypeFloat::constant(i.value_exn().to_double())
          } else {
            type_float_bot
          }
        _ => type_float_bot
      }
    }
    RoundF32 => {
      let t1 = self.input_exn(1).ty()
      match t1 {
        Flt(f) =>
          if f.is_constant() {
            TypeFloat::constant(Float::from_double(f.value_exn()).to_double())
          } else {
            t1
          }
        _ => t1
      }
    }
    CProj | Proj => {
      let ctrl_ty = self.input_exn(0).ty()
      match ctrl_ty {
        Tuple(Some(types)) if self._proj_idx < types.length() => types[self._proj_idx]
        _ => bottom
      }
    }
    If => {
      let ctrl_ty = self.ctrl().ty()
      if ctrl_ty != control && ctrl_ty != bottom {
        return type_tuple_if_neither
      }
      let pred_ty = self.input_exn(1).ty()
      if pred_ty == top || pred_ty == type_integer_top {
        return type_tuple_if_neither
      }
      match pred_ty {
        Int(i) =>
          if i.is_constant() {
            return if i.value_exn() == 0L {
              type_tuple_if_false
            } else {
              type_tuple_if_true
            }
          }
        _ => ()
      }
      type_tuple_if_both
    }
    Never => type_tuple_if_both
    Region => {
      if self.in_progress() {
        return control
      }
      let mut t = xcontrol
      for i = 1; i < self.n_ins(); i = i + 1 {
        t = t.meet(self.input_exn(i).ty())
      }
      t
    }
    Loop => {
      if self.in_progress() {
        return control
      }
      self.input_exn(1).ty()
    }
    Phi =>
      match self.input(0) {
        Some(region) =>
          if region.kind != Region && region.kind != Loop {
            if region.ty() == xcontrol {
              top
            } else {
              self.ty()
            }
          } else if region.in_progress() {
            self._declared_type
          } else {
            let mut t = self._declared_type.glb().dual()
            for i = 1; i < self.n_ins(); i = i + 1 {
              if region.input_exn(i).add_dep(self).ty() != xcontrol {
                t = t.meet(self.input_exn(i).ty())
              }
            }
            t
          }
        None => bottom
      }
    Add => {
      let t1 = self.input_exn(1).ty()
      let t2 = self.input_exn(2).ty()
      if t1.is_high() || t2.is_high() {
        return type_integer_top
      }
      match (t1, t2) {
        (Int(i1), Int(i2)) =>
          if i1.is_constant() && i2.is_constant() {
            TypeInteger::constant(i1.value_exn() + i2.value_exn())
          } else if !_add_overflow(i1._min, i2._min) &&
            !_add_overflow(i1._max, i2._max) {
            TypeInteger::make(i1._min + i2._min, i1._max + i2._max)
          } else {
            type_integer_bot
          }
        _ => type_integer_bot
      }
    }
    AddF => {
      let t1 = self.input_exn(1).ty()
      let t2 = self.input_exn(2).ty()
      match (t1, t2) {
        (Flt(f0), Flt(f1)) =>
          if f0.is_constant() && f1.is_constant() {
            TypeFloat::constant(f0.value_exn() + f1.value_exn())
          } else {
            t1.meet(t2)
          }
        _ => t1.meet(t2)
      }
    }
    Sub => {
      if self.input_exn(1) == self.input_exn(2) {
        return type_integer_zero
      }
      let t1 = self.input_exn(1).ty()
      let t2 = self.input_exn(2).ty()
      if t1.is_high() || t2.is_high() {
        return type_integer_top
      }
      match (t1, t2) {
        (Int(i1), Int(i2)) =>
          if i1.is_constant() && i2.is_constant() {
            TypeInteger::constant(i1.value_exn() - i2.value_exn())
          } else {
            type_integer_bot
          }
        _ => type_integer_bot
      }
    }
    SubF => {
      let t1 = self.input_exn(1).ty()
      let t2 = self.input_exn(2).ty()
      match (t1, t2) {
        (Flt(f0), Flt(f1)) =>
          if f0.is_constant() && f1.is_constant() {
            TypeFloat::constant(f0.value_exn() - f1.value_exn())
          } else {
            t1.meet(t2)
          }
        _ => t1.meet(t2)
      }
    }
    Mul => {
      let t1 = self.input_exn(1).ty()
      let t2 = self.input_exn(2).ty()
      if t1.is_high() || t2.is_high() {
        return type_integer_top
      }
      match (t1, t2) {
        (Int(i1), Int(i2)) =>
          if i1.is_constant() && i2.is_constant() {
            TypeInteger::constant(i1.value_exn() * i2.value_exn())
          } else {
            type_integer_bot
          }
        _ => type_integer_bot
      }
    }
    MulF => {
      let t1 = self.input_exn(1).ty()
      let t2 = self.input_exn(2).ty()
      match (t1, t2) {
        (Flt(f0), Flt(f1)) =>
          if f0.is_constant() && f1.is_constant() {
            TypeFloat::constant(f0.value_exn() * f1.value_exn())
          } else {
            t1.meet(t2)
          }
        _ => t1.meet(t2)
      }
    }
    Div => {
      let t1 = self.input_exn(1).ty()
      let t2 = self.input_exn(2).ty()
      if t1.is_high() || t2.is_high() {
        return type_integer_top
      }
      match (t1, t2) {
        (Int(i1), Int(i2)) =>
          if i1.is_constant() && i2.is_constant() {
            let rhs = i2.value_exn()
            if rhs == 0L {
              type_integer_zero
            } else {
              TypeInteger::constant(i1.value_exn() / rhs)
            }
          } else {
            type_integer_bot
          }
        _ => type_integer_bot
      }
    }
    DivF => {
      let t1 = self.input_exn(1).ty()
      let t2 = self.input_exn(2).ty()
      match (t1, t2) {
        (Flt(f0), Flt(f1)) =>
          if f0.is_constant() && f1.is_constant() {
            TypeFloat::constant(f0.value_exn() / f1.value_exn())
          } else {
            t1.meet(t2)
          }
        _ => t1.meet(t2)
      }
    }
    Minus => {
      let t1 = self.input_exn(1).ty()
      if t1.is_high() {
        return type_integer_top
      }
      match t1 {
        Int(i0) =>
          if t1 != type_integer_bot &&
            i0._min != long_min_value &&
            i0._max != long_min_value {
            TypeInteger::make(-i0._max, -i0._min)
          } else {
            type_integer_bot
          }
        _ => type_integer_bot
      }
    }
    MinusF => {
      let t1 = self.input_exn(1).ty()
      match t1 {
        Flt(f0) =>
          if f0.is_constant() {
            TypeFloat::constant(-f0.value_exn())
          } else {
            t1
          }
        _ => type_float_bot
      }
    }
    Not => {
      let t1 = self.input_exn(1).ty()
      if t1.is_high() {
        return type_integer_bool.dual()
      }
      match t1 {
        Int(i0) =>
          if i0._max < 0L || i0._min > 0L {
            type_integer_false
          } else if t1 == type_integer_zero {
            type_integer_true
          } else {
            type_integer_bot
          }
        Flt(f0) =>
          if f0.is_constant() {
            TypeInteger::constant(if f0.value_exn() == 0.0 { 1L } else { 0L })
          } else {
            t1
          }
        Nil => TypeInteger::constant(1L)
        Ptr(nil) =>
          if nil == 2 {
            TypeInteger::constant(0L)
          } else {
            type_integer_bot
          }
        MemPtr(_, nil) =>
          if nil == 2 {
            TypeInteger::constant(0L)
          } else {
            type_integer_bot
          }
        FunPtr(fp) =>
          if fp._nil == 2 {
            TypeInteger::constant(0L)
          } else {
            type_integer_bot
          }
        Top => top
        _ => bottom
      }
    }
    Shl => {
      let t1 = self.input_exn(1).ty()
      let t2 = self.input_exn(2).ty()
      if t1.is_high() || t2.is_high() {
        return type_integer_top
      }
      match (t1, t2) {
        (Int(i1), Int(i2)) =>
          if i1.is_constant() && i2.is_constant() {
            let sh = i2.value_exn().land(63L).to_int()
            TypeInteger::constant(i1.value_exn() << sh)
          } else {
            type_integer_bot
          }
        _ => type_integer_bot
      }
    }
    Shr => {
      let t1 = self.input_exn(1).ty()
      let t2 = self.input_exn(2).ty()
      if t1.is_high() || t2.is_high() {
        return type_integer_top
      }
      match (t1, t2) {
        (Int(i1), Int(i2)) =>
          if i1.is_constant() && i2.is_constant() {
            TypeInteger::constant(
              _unsigned_shift_right(i1.value_exn(), i2.value_exn()),
            )
          } else if i2._min < 0L || i2._max >= 64L {
            type_integer_bot
          } else {
            let sh = i2._min
            let s1 = _unsigned_shift_right(i1._min, sh)
            let s2 = _unsigned_shift_right(i1._max, sh)
            let wrap = i1._min < 0L && i1._max >= 0L
            TypeInteger::make(
              if wrap {
                0L
              } else if s1 < s2 {
                s1
              } else {
                s2
              },
              if s1 > s2 {
                s1
              } else {
                s2
              },
            )
          }
        _ => type_integer_bot
      }
    }
    Sar => {
      let t1 = self.input_exn(1).ty()
      let t2 = self.input_exn(2).ty()
      if t1.is_high() || t2.is_high() {
        return type_integer_top
      }
      match (t1, t2) {
        (Int(i1), Int(i2)) =>
          if i1.is_constant() && i2.is_constant() {
            let sh = i2.value_exn().land(63L).to_int()
            TypeInteger::constant(i1.value_exn() >> sh)
          } else if i2._min < 0L || i2._max >= 64L {
            type_integer_bot
          } else {
            let sh = i2._min.land(63L).to_int()
            TypeInteger::make(i1._min >> sh, i1._max >> sh)
          }
        _ => type_integer_bot
      }
    }
    And => {
      let t1 = self.input_exn(1).ty()
      let t2 = self.input_exn(2).ty()
      if t1.is_high() || t2.is_high() {
        return type_integer_top
      }
      match (t1, t2) {
        (Int(i0), Int(i1)) =>
          if i0.is_constant() && i1.is_constant() {
            TypeInteger::constant(i0.value_exn() & i1.value_exn())
          } else {
            let mask = i0.mask() & i1.mask()
            if mask < 0L {
              type_integer_bot
            } else {
              TypeInteger::make(0L, mask)
            }
          }
        _ => type_integer_bot
      }
    }
    Or => {
      let t1 = self.input_exn(1).ty()
      let t2 = self.input_exn(2).ty()
      if t1.is_high() || t2.is_high() {
        return type_integer_top
      }
      match (t1, t2) {
        (Int(i0), Int(i1)) =>
          if i0.is_constant() && i1.is_constant() {
            TypeInteger::constant(i0.value_exn() | i1.value_exn())
          } else {
            type_integer_bot
          }
        _ => type_integer_bot
      }
    }
    Xor => {
      let t1 = self.input_exn(1).ty()
      let t2 = self.input_exn(2).ty()
      if t1.is_high() || t2.is_high() {
        return type_integer_top
      }
      match (t1, t2) {
        (Int(i0), Int(i1)) =>
          if i0.is_constant() && i1.is_constant() {
            TypeInteger::constant(i0.value_exn() ^ i1.value_exn())
          } else {
            type_integer_bot
          }
        _ => type_integer_bot
      }
    }
    BoolEq | BoolEqF | BoolLt | BoolLtF | BoolLe | BoolLeF => {
      let t1 = self.input_exn(1).ty()
      let t2 = self.input_exn(2).ty()
      if t1.is_high() || t2.is_high() {
        return type_integer_bool.dual()
      }
      if self.input_exn(1) == self.input_exn(2) {
        return match self.kind {
          BoolEq | BoolEqF | BoolLe | BoolLeF => type_integer_true
          BoolLt | BoolLtF => type_integer_false
          _ => type_integer_bool
        }
      }
      match (t1, t2) {
        (Int(i1), Int(i2)) =>
          match self.kind {
            BoolEq | BoolEqF =>
              if i1 == i2 && i1.is_constant() {
                type_integer_true
              } else if i1._max < i2._min || i1._min > i2._max {
                type_integer_false
              } else {
                type_integer_bool
              }
            BoolLt | BoolLtF =>
              if i1._max < i2._min {
                type_integer_true
              } else if i1._min >= i2._max {
                type_integer_false
              } else {
                type_integer_bool
              }
            BoolLe | BoolLeF =>
              if i1._max <= i2._min {
                type_integer_true
              } else if i1._min > i2._max {
                type_integer_false
              } else {
                type_integer_bool
              }
            _ => type_integer_bool
          }
        (Flt(f1), Flt(f2)) =>
          if self.kind == BoolEqF ||
            self.kind == BoolLtF ||
            self.kind == BoolLeF {
            if f1.is_constant() && f2.is_constant() {
              TypeInteger::constant(
                if self.bool_do_op_f(f1.value_exn(), f2.value_exn()) {
                  1L
                } else {
                  0L
                },
              )
            } else {
              type_integer_bool
            }
          } else {
            type_integer_bool
          }
        _ => type_integer_bool
      }
    }
  }
}

///|
fn _spline_cmp(hi : Node, lo : Node, dep : Node) -> Bool {
  if lo.ty().is_constant() {
    return false
  }
  if hi.ty().is_constant() {
    return true
  }
  if lo.kind == Phi && lo.input_exn(0).ty() == xcontrol {
    return false
  }
  if hi.kind == Phi && hi.input_exn(0).ty() == xcontrol {
    return false
  }
  if lo.kind == Phi && lo.all_cons(dep) {
    return false
  }
  if hi.kind == Phi && hi.all_cons(dep) {
    return true
  }
  if lo.kind == Phi && hi.kind != Phi {
    return true
  }
  if hi.kind == Phi && lo.kind != Phi {
    return false
  }
  lo._nid > hi._nid
}

///|
fn Node::pcon(op : Node, dep : Node) -> Node? {
  if op.kind == Phi && op.all_cons(dep) {
    Some(op)
  } else {
    None
  }
}

///|
fn Node::phi_con(self : Node, rotate : Bool) -> Node? {
  let lhs = self.input_exn(1)
  let rhs = self.input_exn(2)
  let mut lphi = Node::pcon(lhs, self)
  if rotate && lphi is None && lhs.n_ins() > 2 {
    if lhs.kind != self.kind {
      return None
    }
    lphi = Node::pcon(lhs.input_exn(2), self)
  }
  let lphi_node = match lphi {
    Some(phi) => phi
    None => return None
  }
  let rhs_phi = Node::pcon(rhs, self)
  if rhs.kind != Constant && rhs_phi is None {
    return None
  }
  match rhs_phi {
    Some(rphi) => if lphi_node.input_exn(0) != rphi.input_exn(0) { return None }
    None => ()
  }
  let ns : Array[Node?] = Array::make(lphi_node.n_ins(), None)
  ns[0] = lphi_node.input(0)
  for i = 1; i < ns.length(); i = i + 1 {
    let rhs_in = match rhs_phi {
      Some(rphi) => rphi.input_exn(i)
      None => rhs
    }
    ns[i] = Some(self.copy(lphi_node.input_exn(i), rhs_in).peephole())
  }
  let label = lphi_node._phi_label +
    (match rhs_phi {
      Some(rphi) => rphi._phi_label
      None => ""
    })
  let phi = Node::new_phi(label, lphi_node._declared_type, ns).peephole()
  if lhs == lphi_node {
    Some(phi)
  } else {
    Some(self.copy(lhs.input_exn(1), phi))
  }
}

///|
fn Node::idealize_addf(self : Node) -> Node? {
  let lhs = self.input_exn(1)
  match self.input_exn(2).ty() {
    Flt(f) if f.is_constant() && f.value_exn() == 0.0 => Some(lhs)
    _ => None
  }
}

///|
fn Node::idealize_subf(self : Node) -> Node? {
  let lhs = self.input_exn(1)
  match self.input_exn(2).ty() {
    Flt(f) if f.is_constant() && f.value_exn() == 0.0 => Some(lhs)
    _ => None
  }
}

///|
fn Node::idealize_mulf(self : Node) -> Node? {
  let lhs = self.input_exn(1)
  let rhs = self.input_exn(2)
  let t1 = lhs.ty()
  let t2 = rhs.ty()
  match t2 {
    Flt(f) if f.is_constant() && f.value_exn() == 1.0 => return Some(lhs)
    _ => ()
  }
  if t1.is_constant() && !t2.is_constant() {
    ignore(self.swap12())
    return Some(self)
  }
  None
}

///|
fn Node::idealize_divf(self : Node) -> Node? {
  let lhs = self.input_exn(1)
  match self.input_exn(2).ty() {
    Flt(f) if f.is_constant() && f.value_exn() == 1.0 => Some(lhs)
    _ => None
  }
}

///|
fn Node::idealize_minusf(self : Node) -> Node? {
  let input = self.input_exn(1)
  if input.kind == MinusF {
    Some(input.input_exn(1))
  } else {
    None
  }
}

///|
fn Node::idealize_round_f32(self : Node) -> Node? {
  let lhs = self.input_exn(1)
  match lhs.ty() {
    Flt(f) if f._sz == 32 => Some(lhs)
    _ => None
  }
}

///|
fn Node::idealize_sub(self : Node) -> Node? {
  // x - (-y) is x+y
  if self.input_exn(2).kind == Minus {
    return Some(
      Node::new_add(self.input_exn(1), self.input_exn(2).input_exn(1)),
    )
  }

  // (-x) - y is -(x+y)
  if self.input_exn(1).kind == Minus {
    let minus = self.input_exn(1)
    return Some(
      Node::new_minus(
        Node::new_add(minus.input_exn(1), self.input_exn(2)).peephole(),
      ),
    )
  }
  None
}

///|
fn Node::idealize_minus(self : Node) -> Node? {
  // -(-x) is x
  if self.input_exn(1).kind == Minus {
    Some(self.input_exn(1).input_exn(1))
  } else {
    None
  }
}

///|
fn Node::idealize_shl(self : Node) -> Node? {
  let lhs = self.input_exn(1)
  match self.input_exn(2).ty() {
    Int(i) if i.is_constant() && (i.value_exn() & 63L) == 0L => Some(lhs)
    _ => None
  }
}

///|
fn Node::idealize_shr(self : Node) -> Node? {
  let lhs = self.input_exn(1)
  match self.input_exn(2).ty() {
    Int(i) if i.is_constant() && (i.value_exn() & 63L) == 0L => Some(lhs)
    _ => None
  }
}

///|
fn Node::idealize_sar(self : Node) -> Node? {
  let lhs = self.input_exn(1)
  match self.input_exn(2).ty() {
    Int(i) if i.is_constant() && (i.value_exn() & 63L) == 0L => Some(lhs)
    _ => None
  }
}

///|
fn Node::idealize_and(self : Node) -> Node? {
  let lhs = self.input_exn(1)
  let rhs = self.input_exn(2)
  let t1 = lhs.ty()
  let t2 = rhs.ty()

  // And of -1.
  match t2 {
    Int(i) if i.is_constant() && i.value_exn() == -1L => return Some(lhs)
    _ => ()
  }

  // Move constants to RHS
  if t1.is_constant() && !t2.is_constant() {
    ignore(self.swap12())
    return Some(self)
  }
  self.phi_con(true)
}

///|
fn Node::idealize_or(self : Node) -> Node? {
  let lhs = self.input_exn(1)
  let rhs = self.input_exn(2)
  let t1 = lhs.ty()
  let t2 = rhs.ty()

  // Or of 0.
  match t2 {
    Int(i) if i.is_constant() && i.value_exn() == 0L => return Some(lhs)
    _ => ()
  }

  // Move constants to RHS
  if t1.is_constant() && !t2.is_constant() {
    ignore(self.swap12())
    return Some(self)
  }
  self.phi_con(true)
}

///|
fn Node::idealize_xor(self : Node) -> Node? {
  let lhs = self.input_exn(1)
  let rhs = self.input_exn(2)
  let t1 = lhs.ty()
  let t2 = rhs.ty()

  // Xor of 0.
  match t2 {
    Int(i) if i.is_constant() && i.value_exn() == 0L => return Some(lhs)
    _ => ()
  }

  // Move constants to RHS
  if t1.is_constant() && !t2.is_constant() {
    ignore(self.swap12())
    return Some(self)
  }
  self.phi_con(true)
}

///|
fn Node::idealize_add(self : Node) -> Node? {
  let lhs = self.input_exn(1)
  let rhs = self.input_exn(2)
  let t2 = rhs.ty()
  match t2 {
    Int(i) if i.is_constant() && i.value_exn() == 0L => return Some(lhs)
    _ => ()
  }
  if lhs == rhs {
    let two = Node::new_constant(TypeInteger::constant(2L)).peephole()
    return Some(Node::new_mul(lhs, two))
  }
  if lhs.kind != Add && rhs.kind == Add {
    ignore(self.swap12())
    return Some(self)
  }
  // x+(-y) becomes x-y
  if rhs.kind == Minus {
    return Some(Node::new_sub(lhs, rhs.input_exn(1)))
  }
  if rhs.kind == Add {
    let add_lhs = rhs.input_exn(1)
    let add_rhs = rhs.input_exn(2)
    let left = Node::new_add(lhs, add_lhs).peephole()
    return Some(Node::new_add(left, add_rhs))
  }
  if lhs.kind != Add {
    if _spline_cmp(lhs, rhs, self) {
      ignore(self.swap12())
      return Some(self)
    }
    return self.phi_con(true)
  }
  // Dead data cycle; comes about from dead infinite loops.  Do nothing,
  // the loop will peep as dead after a bit.
  if lhs.input_exn(1) == lhs {
    return None
  }
  let lhs_rhs = lhs.input_exn(2)
  if lhs_rhs.add_dep(self).ty().is_constant() && t2.is_constant() {
    let folded = Node::new_add(lhs_rhs, rhs).peephole()
    return Some(Node::new_add(lhs.input_exn(1), folded))
  }
  match self.phi_con(true) {
    Some(n) => return Some(n)
    None => ()
  }
  if _spline_cmp(lhs_rhs, rhs, self) {
    let left = Node::new_add(lhs.input_exn(1), rhs).peephole()
    return Some(Node::new_add(left, lhs_rhs))
  }
  None
}

///|
fn Node::idealize_mul(self : Node) -> Node? {
  let lhs = self.input_exn(1)
  let rhs = self.input_exn(2)
  let t1 = lhs.ty()
  let t2 = rhs.ty()
  match t2 {
    Int(i) if i.is_constant() && i.value_exn() == 1L => return Some(lhs)
    _ => ()
  }
  if t1.is_constant() && !t2.is_constant() {
    ignore(self.swap12())
    return Some(self)
  }
  self.phi_con(true)
}

///|
fn Node::idealize_div(self : Node) -> Node? {
  let rhs = self.input_exn(2)
  match rhs.ty() {
    Int(i) if i.is_constant() && i.value_exn() == 1L => Some(self.input_exn(1))
    _ => None
  }
}

///|
fn Node::idealize_bool(self : Node) -> Node? {
  if self.input_exn(1) == self.input_exn(2) {
    let value = if self.bool_do_op(3L, 3L) { 1L } else { 0L }
    return Some(Node::new_constant(TypeInteger::constant(value)))
  }
  let is_eq = self.kind == BoolEq || self.kind == BoolEqF
  if is_eq {
    let lhs = self.input_exn(1)
    let rhs = self.input_exn(2)
    if rhs.kind != Constant {
      if lhs.kind == Constant {
        let swapped = if self.kind == BoolEqF {
          Node::new_bool_eqf(rhs, lhs)
        } else {
          Node::new_bool_eq(rhs, lhs)
        }
        return Some(swapped)
      }
      if lhs._nid > rhs._nid {
        let swapped = if self.kind == BoolEqF {
          Node::new_bool_eqf(rhs, lhs)
        } else {
          Node::new_bool_eq(rhs, lhs)
        }
        return Some(swapped)
      }
    }
    let rhs_t = rhs.ty()
    if rhs_t == type_integer_zero || rhs_t == type_nil {
      return Some(Node::new_not(lhs))
    }
    if rhs_t == type_integer_true && lhs.ty() == type_integer_bool {
      return Some(lhs)
    }
  }
  self.phi_con(is_eq)
}

///|
fn Node::idealize_cast(self : Node) -> Node? {
  if self.input_exn(1).ty().isa(self._declared_type) {
    Some(self.input_exn(1))
  } else {
    None
  }
}

///|
fn Node::idealize_read_only(self : Node) -> Node? {
  if self.input_exn(1).ty().is_final() {
    Some(self.input_exn(1))
  } else {
    None
  }
}

///|
fn Node::check_no_use_beyond(self : Node, that : Node) -> Bool {
  if self.n_outs() == 1 {
    return true
  }
  for use_ in self._outputs {
    match use_ {
      Some(u) if u != that => ignore(u.add_dep(that))
      _ => ()
    }
  }
  false
}

///|
fn Node::idealize_store(self : Node) -> Node? {
  let mem = self.input_exn(1)
  if mem.kind == Store &&
    mem._memop_alias == self._memop_alias &&
    self.input_exn(2) == mem.input_exn(2) &&
    self.input_exn(3) == mem.input_exn(3) {
    match self.input_exn(2).ty() {
      MemPtr(_, _) =>
        if mem.check_no_use_beyond(self) {
          ignore(self.set_def(1, mem.input(1)))
          return Some(self)
        }
      _ => ()
    }
  }
  None
}

///|
fn Node::idealize_load(self : Node) -> Node? {
  let mem = self.input_exn(1)
  let ptr0 = self.input_exn(2)
  let off = self.input_exn(3)

  // Read-only is a deep property, and cannot be cast-away.
  let cast_ro = fn(rez : Node) -> Node {
    if ptr0.ty().is_final() && !rez.ty().is_final() {
      Node::new_read_only(rez).peephole()
    } else {
      rez
    }
  }
  let new_init_for_alias = fn(nnn : Node, alias_id : Int) -> Node {
    match nnn._con {
      Some(MemPtr(obj, _)) =>
        match obj._fields {
          Some(fs) => {
            let idx = obj.find_alias(alias_id)
            if idx < 0 {
              panic()
            }
            nnn.input_exn(2 + fs.length() + idx)
          }
          None => panic()
        }
      _ => panic()
    }
  }

  // Simple Load-after-Store on same address.
  if mem.kind == Store && ptr0 == mem.input_exn(2) && off == mem.input_exn(3) {
    return Some(mem.input_exn(4))
  }

  // Simple Load-after-New on same address.
  if mem.kind == Proj &&
    mem.input_exn(0).kind == New &&
    ptr0.kind == Proj &&
    ptr0.input_exn(0) == mem.input_exn(0) &&
    ptr0._proj_idx == 1 {
    return Some(new_init_for_alias(mem.input_exn(0), self._memop_alias))
  }

  // Load-after-Store on same address, but bypassing provably unrelated stores/news.
  let ptr = if ptr0.kind == ReadOnly { ptr0.input_exn(1) } else { ptr0 }
  let never_alias = fn(ptr1 : Node, ptr2 : Node) -> Bool {
    ptr1.input(0) != ptr2.input(0) &&
    ptr1.kind == Proj &&
    ptr1.input_exn(0).kind == New &&
    ptr2.kind == Proj &&
    ptr2.input_exn(0).kind == New
  }
  let mut mem0 = mem
  while true {
    match mem0.kind {
      Store => {
        let st = mem0
        if ptr == st.input_exn(2) && off == st.input_exn(3) {
          return Some(cast_ro(st.input_exn(4)))
        }
        if !off.ty().join(st.input_exn(3).ty()).is_high() &&
          !never_alias(ptr, st.input_exn(2)) {
          break
        }
        mem0 = st.input_exn(1)
      }
      Phi => break
      Proj => {
        let mproj = mem0
        let base = mproj.input_exn(0)
        if base.kind == New {
          if ptr.kind == Proj && ptr.input_exn(0) == base {
            return Some(cast_ro(new_init_for_alias(base, self._memop_alias)))
          }
          if ptr.kind != Proj || ptr.input_exn(0).kind != New {
            break
          }
          mem0 = base.input_exn(self._memop_alias)
        } else {
          break
        }
      }
      _ => break
    }
  }

  // Push a Load up through a Phi, as long as it collapses on at least one arm.
  if mem.kind == Phi &&
    mem.input_exn(0).ty() == control &&
    mem.n_ins() == 3 &&
    off.kind == Constant {
    let memphi = mem
    let region = memphi.input_exn(0)
    let profit = fn(idx : Int) -> Bool {
      match memphi.input(idx) {
        None => false
        Some(px) =>
          match px.ty() {
            Mem(mem) if mem._t.is_high_or_const() => {
              ignore(px.add_dep(self))
              true
            }
            _ =>
              if px.kind == Store &&
                ptr0 == px.input_exn(2) &&
                off == px.input_exn(3) {
                ignore(px.add_dep(self))
                true
              } else {
                false
              }
          }
      }
    }
    let ld = fn(idx : Int) -> Node {
      let mem_in = memphi.input_exn(idx)
      let ptr_in = if ptr0.kind == Phi &&
        ptr0.input_exn(0) == memphi.input_exn(0) {
        ptr0.input_exn(idx)
      } else {
        ptr0
      }
      Node::new_load(
        self._memop_name,
        self._memop_alias,
        self._declared_type,
        mem_in,
        ptr_in,
        off,
      ).peephole()
    }
    if profit(2) || (region.kind != Loop && profit(1)) {
      let ld1 = ld(1)
      let ld2 = ld(2)
      return Some(
        Node::new_phi(self._memop_name, self._declared_type, [
          Some(region),
          Some(ld1),
          Some(ld2),
        ]),
      )
    }
  }
  None
}

///|
fn Node::idealize_proj(self : Node) -> Node? {
  let ctrl = self.input_exn(0)
  let other = 1 - self._proj_idx
  match ctrl.ty() {
    Tuple(Some(types)) =>
      if other >= 0 && other < types.length() && types[other] == xcontrol {
        return Some(ctrl.input_exn(0))
      }
    _ => ()
  }

  // Flip a negating if-test, to remove the not
  if ctrl.kind == If && ctrl.input_exn(1).add_dep(self).kind == Not {
    let not = ctrl.input_exn(1)
    let iff = Node::new_if(ctrl.input(0), not.input_exn(1)).peephole()
    return Some(
      Node::new_cproj(
        iff,
        1 - self._proj_idx,
        if self._proj_idx == 0 {
          "False"
        } else {
          "True"
        },
      ),
    )
  }
  None
}

///|
fn Node::idealize_if(self : Node) -> Node? {
  // Hunt up the immediate dominator tree. If we find an identical if test on
  // either the true or false branch, that side wins.
  if self.input_exn(1).ty().is_high_or_const() {
    return None
  }
  let mut dom = self.idom()
  let mut prior : Node = self
  while dom is Some(d) {
    if d.add_dep(self).kind == If &&
      d.input_exn(1).add_dep(self) == self.input_exn(1) &&
      prior.kind == CProj {
      let value = if prior._proj_idx == 0 { 1L } else { 0L }
      ignore(
        self.set_def(
          1,
          Some(Node::new_constant(TypeInteger::constant(value)).peephole()),
        ),
      )
      return Some(self)
    }
    prior = d
    dom = d.idom()
  }
  None
}

///|
fn Node::find_dead_input(self : Node) -> Int {
  for i = 1; i < self.n_ins(); i = i + 1 {
    if self.input_exn(i).ty() == xcontrol {
      return i
    }
  }
  0
}

///|
fn Node::has_phi(self : Node) -> Bool {
  for out in self._outputs {
    match out {
      Some(phi) if phi.kind == Phi => return true
      _ => ()
    }
  }
  false
}

///|
fn Node::idealize_region(self : Node) -> Node? {
  if self.in_progress() {
    return None
  }
  let path = self.find_dead_input()
  if path != 0 && !(self.kind == Loop && self.input(1) == self.input(path)) {
    // Cannot use the obvious output iterator here, because a Phi deleting an
    // input might recursively delete itself. This shuffles the output array,
    // and we might miss iterating an unrelated Phi.
    let mut nouts = 0
    while nouts != self.n_outs() {
      nouts = self.n_outs()
      for i = 0; i < self.n_outs(); i = i + 1 {
        match self._outputs[i] {
          Some(phi) if phi.kind == Phi && phi.n_ins() == self.n_ins() =>
            ignore(phi.del_def(path))
          _ => ()
        }
      }
    }
    self._idom = None
    if self.is_dead() {
      return Some(xctrl.val)
    }
    return Some(self.del_def(path))
  }
  // If down to a single input, become that input (no Phis; 1-input Phis will
  // collapse on their own).
  if self.n_ins() == 2 && !self.has_phi() {
    self._idom = None
    return Some(self.input_exn(1))
  }
  None
}

///|
fn Node::idealize_return(self : Node) -> Node? {
  if self.ctrl().ty() == xcontrol {
    Some(self.ctrl())
  } else {
    None
  }
}

///|
fn Node::idealize_stop(self : Node) -> Node? {
  let len = self.n_ins()
  let mut i = 0
  while i < self.n_ins() {
    if self.input_exn(i).ty() == xcontrol {
      ignore(self.del_def(i))
      i = i - 1
    }
    i = i + 1
  }
  if len != self.n_ins() {
    Some(self)
  } else {
    None
  }
}

///|
fn Node::phi_same_op(self : Node) -> Bool {
  let k = self.input_exn(1).kind
  for i = 2; i < self.n_ins(); i = i + 1 {
    if self.input_exn(i).kind != k {
      return false
    }
  }
  true
}

///|
fn Node::single_unique_input(self : Node) -> Node? {
  let region = self.input_exn(0)
  if region.kind == Loop && region.input_exn(1).ty() == xcontrol {
    return None
  }
  let mut live : Node? = None
  for i = 1; i < self.n_ins(); i = i + 1 {
    if region.input_exn(i).add_dep(self).ty() != xcontrol &&
      self.input_exn(i) != self {
      let in_i = self.input_exn(i)
      match live {
        None => live = Some(in_i)
        Some(l) => if l != in_i { return None }
      }
    }
  }
  live
}

///|
fn Node::idealize_phi(self : Node) -> Node? {
  let region = match self.input(0) {
    Some(region) => region
    None => return None
  }
  if region.kind != Region && region.kind != Loop {
    return Some(self.input_exn(1))
  }
  if region.in_progress() || region.n_ins() <= 1 {
    return None
  }
  match self.single_unique_input() {
    Some(live) => return Some(live)
    None => ()
  }
  let op = self.input_exn(1)
  if op.n_ins() == 3 &&
    op.input(0) is None &&
    !op.is_cfg() &&
    self.phi_same_op() {
    let lhss : Array[Node?] = Array::make(self.n_ins(), None)
    let rhss : Array[Node?] = Array::make(self.n_ins(), None)
    lhss[0] = self.input(0)
    rhss[0] = self.input(0)
    for i = 1; i < self.n_ins(); i = i + 1 {
      lhss[i] = self.input_exn(i).input(1)
      rhss[i] = self.input_exn(i).input(2)
    }
    let phi_lhs = Node::new_phi(self._phi_label, self._declared_type, lhss).peephole()
    let phi_rhs = Node::new_phi(self._phi_label, self._declared_type, rhss).peephole()
    return Some(op.copy(phi_lhs, phi_rhs))
  }

  // If merging Phi(N, cast(N)) - we are losing the cast JOIN effects, so just remove.
  if self.n_ins() == 3 {
    let in1 = self.input_exn(1)
    let in2 = self.input_exn(2)
    if in1.kind == Cast && in1.input_exn(1).add_dep(self) == in2 {
      return Some(in2)
    }
    if in2.kind == Cast && in2.input_exn(1).add_dep(self) == in1 {
      return Some(in1)
    }
  }

  // If merging a null-checked null and the checked value, just use the value.
  // if( val ) ..; phi(Region,False=0/null,True=val);
  // then replace with plain val.
  if self.n_ins() == 3 {
    let mut nullx = -1
    let t1 = self.input_exn(1).ty()
    if t1 == t1.make_init() {
      nullx = 1
    }
    let t2 = self.input_exn(2).ty()
    if t2 == t2.make_init() {
      nullx = 2
    }
    if nullx != -1 {
      let val0 = self.input_exn(3 - nullx)
      let val = if val0.kind == Cast { val0.input_exn(1) } else { val0 }
      match region.idom() {
        Some(iff) if iff.kind == If && iff.input_exn(1).add_dep(self) == val => {
          let mut idom = region.input_exn(nullx)
          while idom.input(0) != Some(iff) {
            match idom.idom() {
              Some(next) => idom = next
              None => return None
            }
          }
          if idom.kind == CProj && idom._proj_idx == 1 {
            return Some(val)
          }
        }
        _ => ()
      }
    }
  }
  None
}

///|
pub fn Node::idealize(self : Node) -> Node? {
  match self.kind {
    Add => self.idealize_add()
    AddF => self.idealize_addf()
    And => self.idealize_and()
    Or => self.idealize_or()
    Xor => self.idealize_xor()
    Mul => self.idealize_mul()
    MulF => self.idealize_mulf()
    Div => self.idealize_div()
    DivF => self.idealize_divf()
    Shl => self.idealize_shl()
    Shr => self.idealize_shr()
    Sar => self.idealize_sar()
    Sub => self.idealize_sub()
    Cast => self.idealize_cast()
    ReadOnly => self.idealize_read_only()
    RoundF32 => self.idealize_round_f32()
    Minus => self.idealize_minus()
    If => self.idealize_if()
    BoolEq | BoolEqF | BoolLt | BoolLtF | BoolLe | BoolLeF =>
      self.idealize_bool()
    CProj => self.idealize_proj()
    Load => self.idealize_load()
    Store => self.idealize_store()
    Return => self.idealize_return()
    Stop => self.idealize_stop()
    Region => self.idealize_region()
    Loop => self.idealize_region()
    Phi => self.idealize_phi()
    SubF => self.idealize_subf()
    MinusF => self.idealize_minusf()
    _ => None
  }
}

///|
pub fn Node::set_type(self : Node, typ : Type) -> Type? {
  let old = self._type
  match old {
    Some(o) => if !typ.isa(o) { panic() } else if o == typ { return old }
    None => ()
  }
  self._type = Some(typ)
  IterPeeps::add_all(self._outputs)
  self.move_deps_to_worklist()
  old
}

///|
pub fn Node::peephole_opt(self : Node) -> Node? {
  iter_cnt.val += 1
  let old = self.set_type(self.compute())

  // Replace constant computations from non-constants with a constant node
  let typ = self.ty()
  if self.kind != Constant && self.kind != XCtrl && typ.is_high_or_const() {
    let con = if typ == xcontrol {
      Node::new_xctrl()
    } else {
      Node::new_constant(typ)
    }
    return match con.peephole_opt() {
      Some(n) => Some(n)
      None => Some(con)
    }
  }

  // Global Value Numbering
  if self._hash == 0 {
    match self.gvn_get() {
      None => self.gvn_put()
      Some(n) => {
        ignore(n.set_type(n.ty().join(typ)))
        self._hash = 0
        return Some(self.dead_code_elim(n))
      }
    }
  }
  match self.idealize() {
    Some(n) => Some(n)
    None => {
      let same = match old {
        Some(o) => o == typ
        None => false
      }
      if same {
        iter_nop_cnt.val += 1
        None
      } else {
        Some(self)
      }
    }
  }
}

///|
pub fn Node::peephole(self : Node) -> Node {
  if disable_peephole.val {
    self._type = Some(self.compute())
    return self
  }
  match self.peephole_opt() {
    None => self
    Some(n) => {
      // Match refs/simple: only recurse when the replacement is a freshly created node.
      let nn = if n._nid >= self._nid { n.peephole() } else { n }
      self.dead_code_elim(nn)
    }
  }
}

///|
pub fn Node::add_return(self : Node, node : Node) -> Node {
  if self.kind != Stop {
    panic()
  }
  match self.add_def(Some(node)) {
    Some(n) => n
    None => node
  }
}

///|
pub fn Node::iterate(
  self : Node,
  show? : Bool = false,
) -> Node raise ParseError {
  if self.kind != Stop {
    panic()
  }
  let stop = IterPeeps::iterate(self)
  match stop.walk_err() {
    Some(err) => raise ParseError::Msg(err)
    None => ()
  }
  GlobalCodeMotion::fix_loops(stop)
  if show {
    ignore(show)
  }
  GlobalCodeMotion::build_cfg(stop)
  stop
}

///|
fn Node::err(self : Node) -> String? {
  match self.kind {
    Load | Store => {
      let ptr_node = self.input_exn(2)
      let ptr = ptr_node.ty()
      match ptr {
        Bot => ()
        MemPtr(_, nil) if nil == 1 || nil == 2 => ()
        _ => return Some("Might be null accessing '\{self._memop_name}'")
      }
      if self.kind == Store {
        let ptr_for_final = if ptr_node.kind == ReadOnly {
          ptr_node.input_exn(1).ty()
        } else {
          ptr
        }
        match ptr_for_final {
          MemPtr(obj, _) =>
            match obj._fields {
              None => ()
              Some(fields) => {
                let idx = obj.find(self._memop_name)
                if idx >= 0 && fields[idx]._final {
                  return Some("Cannot modify final field '\{self._memop_name}'")
                }
              }
            }
          _ => ()
        }
      }
      if self.kind == Store && !self._memop_init {
        let value_ty = self.input_exn(4).ty()
        if !value_ty.isa(self._declared_type) {
          return Some(
            "Cannot store \{value_ty} into field \{self._declared_type} \{self._memop_name}",
          )
        }
      }
      None
    }
    Add | Mul => {
      let t1 = self.input_exn(1).ty()
      if !_is_int_type(t1) {
        return Some("Cannot '\{self.label()}' \{t1}")
      }
      let t2 = self.input_exn(2).ty()
      if !_is_int_type(t2) {
        return Some("Cannot '\{self.label()}' \{t2}")
      }
      None
    }
    And | Or | Xor | Shl | Shr | Sar => {
      let t1 = self.input_exn(1).ty()
      if !_is_int_type(t1) {
        let op = match self.kind {
          And => "&"
          Or => "|"
          Xor => "^"
          Shl => "<<"
          Shr => ">>>"
          Sar => ">>"
          _ => "?"
        }
        return Some("Cannot '\{op}' \{t1}")
      }
      let t2 = self.input_exn(2).ty()
      if !_is_int_type(t2) {
        let op = match self.kind {
          And => "&"
          Or => "|"
          Xor => "^"
          Shl => "<<"
          Shr => ">>>"
          Sar => ">>"
          _ => "?"
        }
        return Some("Cannot '\{op}' \{t2}")
      }
      None
    }
    _ => None
  }
}

///|
fn Node::walk_err(self : Node) -> String? {
  let visited : Array[Bool] = Array::make(_unique_id.val + 1, false)
  self._walk_err(visited)
}

///|
fn Node::_walk_err(self : Node, visited : Array[Bool]) -> String? {
  if self._nid >= 0 && self._nid < visited.length() && visited[self._nid] {
    return None
  }
  if self._nid >= 0 && self._nid < visited.length() {
    visited[self._nid] = true
  }
  match self.err() {
    Some(err) => return Some(err)
    None => ()
  }
  for def in self._inputs {
    match def {
      Some(n) =>
        match n._walk_err(visited) {
          Some(err) => return Some(err)
          None => ()
        }
      None => ()
    }
  }
  for use_ in self._outputs {
    match use_ {
      Some(n) =>
        match n._walk_err(visited) {
          Some(err) => return Some(err)
          None => ()
        }
      None => ()
    }
  }
  None
}

///|
pub fn Node::print(self : Node) -> String {
  let sb = StringBuilder::new()
  let visited : Array[Bool] = Array::make(_unique_id.val + 1, false)
  self._print0(sb, visited)
  sb.to_string()
}

///|
fn Node::_print0(
  self : Node,
  sb : StringBuilder,
  visited : Array[Bool],
) -> Unit {
  if self._nid >= 0 &&
    self._nid < visited.length() &&
    visited[self._nid] &&
    self.kind != Constant {
    sb.write_string(self.label())
    return
  }
  if self._nid >= 0 && self._nid < visited.length() {
    visited[self._nid] = true
  }
  if self.is_dead() {
    sb.write_string(self.unique_name())
    sb.write_string(":DEAD")
  } else {
    self._print1(sb, visited)
  }
}

///|
fn Node::_print1(
  self : Node,
  sb : StringBuilder,
  visited : Array[Bool],
) -> Unit {
  match self.kind {
    Start => sb.write_string(self.label())
    Stop => {
      if self.n_ins() == 1 {
        match self.input(0) {
          Some(ret) => return ret._print0(sb, visited)
          None => ()
        }
      }
      sb.write_string("Stop[ ")
      for input in self._inputs {
        match input {
          Some(ret) => {
            ret._print0(sb, visited)
            sb.write_string(" ")
          }
          None => ()
        }
      }
      sb.write_string("]")
    }
    Return => {
      sb.write_string("return ")
      self.expr()._print0(sb, visited)
      sb.write_string(";")
    }
    Constant =>
      match self._con {
        Some(con) => con.print_to(sb)
        None => bottom.print_to(sb)
      }
    XCtrl => sb.write_string("Xctrl")
    Mem => {
      sb.write_string("MEM[ ")
      let mut first = true
      for i = 2; i < self.n_ins(); i = i + 1 {
        if !first {
          sb.write_string(" ")
        }
        first = false
        sb.write_string("\{i}:")
        let mut n = self.input(i)
        while true {
          match n {
            Some(loop_scope) if loop_scope.kind == Scope => {
              sb.write_string("Lazy_")
              n = loop_scope.input(i)
            }
            _ => break
          }
        }
        match n {
          Some(n) => n._print0(sb, visited)
          None => sb.write_string("___")
        }
      }
      sb.write_string("]")
    }
    Struct =>
      match self._struct_ts {
        Some(ts) => {
          sb.write_string(ts._name)
          sb.write_string(" {")
          match ts._fields {
            None => sb.write_string("}")
            Some(fields) => {
              for i, f in fields {
                if i > 0 {
                  sb.write_string("; ")
                }
                sb.write_string(f._fname)
                sb.write_string(":")
                f._type.print_to(sb)
              }
              sb.write_string("}")
            }
          }
        }
        None => sb.write_string("STRUCT?")
      }
    New =>
      match self._con {
        Some(MemPtr(obj, _)) => {
          sb.write_string("new ")
          sb.write_string(obj.str())
        }
        _ => sb.write_string("new")
      }
    Load => {
      sb.write_string(".")
      sb.write_string(self._memop_name)
    }
    Store => {
      sb.write_string(".")
      sb.write_string(self._memop_name)
      sb.write_string("=")
      self.input_exn(3)._print0(sb, visited)
      sb.write_string(";")
    }
    Cast => {
      sb.write_string(self.label())
      self.input_exn(1)._print0(sb, visited)
    }
    ReadOnly => {
      sb.write_string("(const)")
      self.input_exn(1)._print0(sb, visited)
    }
    ToFloat => {
      sb.write_string("(flt)")
      self.input_exn(1)._print0(sb, visited)
    }
    RoundF32 => {
      sb.write_string("((f32)")
      self.input_exn(1)._print0(sb, visited)
      sb.write_string(")")
    }
    Add | AddF => {
      sb.write_string("(")
      self.input_exn(1)._print0(sb, visited)
      sb.write_string("+")
      self.input_exn(2)._print0(sb, visited)
      sb.write_string(")")
    }
    Sub | SubF => {
      sb.write_string("(")
      self.input_exn(1)._print0(sb, visited)
      sb.write_string("-")
      self.input_exn(2)._print0(sb, visited)
      sb.write_string(")")
    }
    Mul | MulF => {
      sb.write_string("(")
      self.input_exn(1)._print0(sb, visited)
      sb.write_string("*")
      self.input_exn(2)._print0(sb, visited)
      sb.write_string(")")
    }
    Div | DivF => {
      sb.write_string("(")
      self.input_exn(1)._print0(sb, visited)
      sb.write_string("/")
      self.input_exn(2)._print0(sb, visited)
      sb.write_string(")")
    }
    Minus | MinusF => {
      sb.write_string("(-")
      self.input_exn(1)._print0(sb, visited)
      sb.write_string(")")
    }
    Not => {
      sb.write_string("(!")
      self.input_exn(1)._print0(sb, visited)
      sb.write_string(")")
    }
    Shl | Shr | Sar | And | Or | Xor => {
      let op = match self.kind {
        Shl => "<<"
        Shr => ">>>"
        Sar => ">>"
        And => "&"
        Or => "|"
        Xor => "^"
        _ => "?"
      }
      sb.write_string("(")
      self.input_exn(1)._print0(sb, visited)
      sb.write_string(op)
      self.input_exn(2)._print0(sb, visited)
      sb.write_string(")")
    }
    If => {
      sb.write_string("if( ")
      self.input_exn(1)._print0(sb, visited)
      sb.write_string(" )")
    }
    Never => sb.write_string("Never")
    CProj | Proj => sb.write_string(self._proj_label)
    BoolEq | BoolEqF | BoolLt | BoolLtF | BoolLe | BoolLeF => {
      let op = match self.kind {
        BoolEq | BoolEqF => "=="
        BoolLt | BoolLtF => "<"
        BoolLe | BoolLeF => "<="
        _ => "?"
      }
      sb.write_string("(")
      self.input_exn(1)._print0(sb, visited)
      sb.write_string(op)
      self.input_exn(2)._print0(sb, visited)
      sb.write_string(")")
    }
    Region => sb.write_string("Region")
    Loop => sb.write_string("Loop")
    Phi => {
      match self.input(0) {
        Some(region) => if region.in_progress() { sb.write_string("Z") }
        None => ()
      }
      sb.write_string("Phi(")
      let mut first = true
      for input in self._inputs {
        if !first {
          sb.write_string(",")
        }
        first = false
        match input {
          Some(n) => n._print0(sb, visited)
          None => sb.write_string("____")
        }
      }
      sb.write_string(")")
    }
    Scope => {
      sb.write_string("Scope[ ")
      let names = self.reverse_names()
      for i = 0; i < self.n_ins(); i = i + 1 {
        if i > 0 {
          sb.write_string(" ")
        }
        sb.write_string(names[i])
        sb.write_string(":")
        let mut n = self.input(i)
        while true {
          match n {
            Some(loop_scope) if loop_scope.kind == Scope => {
              sb.write_string("Lazy_")
              n = loop_scope.input(i)
            }
            _ => break
          }
        }
        match n {
          Some(n) => n._print0(sb, visited)
          None => sb.write_string("____")
        }
      }
      sb.write_string("]")
    }
  }
}

///|
pub impl Eq for Node with equal(self, other) {
  self._nid == other._nid
}

///|
pub fn Node::push(self : Node, in_con? : Bool = false) -> Unit {
  if self.kind != Scope {
    panic()
  }
  if self._lex_size.length() != self._in_cons.length() {
    panic()
  }
  self._lex_size.push(self._vars.length())
  self._in_cons.push(in_con)
}

///|
pub fn Node::pop(self : Node) -> Unit {
  if self.kind != Scope {
    panic()
  }
  if self._lex_size.length() != self._in_cons.length() {
    panic()
  }
  let n = match self._lex_size.pop() {
    Some(n) => n
    None => panic()
  }
  match self._in_cons.pop() {
    Some(_) => ()
    None => panic()
  }
  let popn = self.n_ins() - n
  if popn > 0 {
    self.pop_n(popn)
  }
  while self._vars.length() > n {
    ignore(self._vars.pop())
  }
}

///|
pub fn Node::in_con(self : Node) -> Bool {
  if self.kind != Scope {
    panic()
  }
  match self._in_cons.last() {
    Some(b) => b
    None => panic()
  }
}

///|
pub fn Node::add_guards(
  self : Node,
  ctrl : Node,
  pred : Node?,
  invert : Bool,
) -> Unit {
  if self.kind != Scope {
    panic()
  }
  if !ctrl.is_cfg() {
    panic()
  }
  // Marker to distinguish 0/1/2 guards.
  self._guards.push(ctrl)
  match pred {
    None => return
    Some(pred0) => {
      if ctrl.ty() == xcontrol || pred0.is_dead() {
        return
      }
      let pred = if invert {
        if pred0.kind == Not {
          pred0.input_exn(1)
        } else {
          IterPeeps::add(Node::new_not(pred0).peephole())
        }
      } else {
        pred0
      }

      // This is a zero/null test.  Compute the positive test type.
      let tnz = pred.ty().non_zero()
      let tcast = tnz.join(pred.ty())
      if tcast != pred.ty() && !tcast.is_high() {
        let cast = Node::new_cast(tcast, Some(ctrl), pred.keep())
          .peephole()
          .keep()
        self._guards.push(pred)
        self._guards.push(cast)
        ignore(self.replace(pred, cast))
      }

      // Compute the negative test type.
      if pred.kind == Not {
        let npred = pred.input_exn(1)
        let tzero = npred.ty().make_zero()
        let tzcast = tzero.join(npred.ty())
        if tzcast != npred.ty() && !tzcast.is_high() {
          let cast = Node::new_cast(tzcast, Some(ctrl), npred.keep())
            .peephole()
            .keep()
          self._guards.push(npred)
          self._guards.push(cast)
          ignore(self.replace(npred, cast))
        }
      }
    }
  }
}

///|
pub fn Node::remove_guards(self : Node, ctrl : Node) -> Unit {
  if self.kind != Scope {
    panic()
  }
  if !ctrl.is_cfg() {
    panic()
  }
  // 0/1/2 guards.
  while true {
    let g = match self._guards.pop() {
      Some(g) => g
      None => panic()
    }
    if g == ctrl {
      break
    }
    if g.is_cfg() {
      continue
    }
    // Pop/kill cast, then pred.
    ignore(g.unkeep())
    let p = match self._guards.pop() {
      Some(p) => p
      None => panic()
    }
    ignore(p.unkeep())
  }
}

///|
pub fn Node::upcast_guard(self : Node, pred : Node) -> Node {
  if self.kind != Scope {
    panic()
  }
  // If finding a guarded instance of pred, replace with cast.
  let mut i = self._guards.length()
  while i > 0 {
    i = i - 1
    let cast = self._guards[i]
    if cast.is_cfg() {
      continue
    }
    if i == 0 {
      break
    }
    i = i - 1
    let xpred = self._guards[i]
    if xpred == pred {
      return cast
    }
  }
  pred
}

///|
pub fn Node::define_(
  self : Node,
  name : String,
  declared_type : Type,
  xfinal : Bool,
  init : Node,
) -> Bool {
  if self.kind != Scope {
    panic()
  }
  if name.has_prefix("$".to_string_view()) && self._lex_size.length() != 1 {
    panic()
  }
  if self._lex_size.length() > 1 {
    let lexlen = match self._lex_size.last() {
      Some(n) => n
      None => panic()
    }
    let mut i = self._vars.length()
    while i > lexlen {
      i = i - 1
      if self._vars[i]._name == name {
        return false
      }
    }
  }
  let idx = self.n_ins()
  self._vars.push({
    _idx: idx,
    _name: name,
    _type: declared_type,
    _final: xfinal,
  })
  ignore(self.add_def(Some(init)))
  true
}

///|
pub fn Node::lookup(self : Node, name : String) -> Var? {
  if self.kind != Scope {
    panic()
  }
  let idx = self._find(name)
  if idx == -1 {
    return None
  }
  Some(self._update_var(self._vars[idx], None))
}

///|
pub fn Node::update(self : Node, name : String, n : Node) -> Unit {
  if self.kind != Scope {
    panic()
  }
  let idx = self._find(name)
  if idx == -1 {
    panic()
  }
  ignore(self._update_var(self._vars[idx], Some(n)))
}

///|
fn Node::_find(self : Node, name : String) -> Int {
  let mut i = self._vars.length()
  while i > 0 {
    i = i - 1
    if self._vars[i]._name == name {
      return i
    }
  }
  -1
}

///|
pub fn Node::lookup_declared_type(self : Node, name : String) -> Type? {
  if self.kind != Scope {
    panic()
  }
  match self.lookup(name) {
    Some(v) => Some(v._type)
    None => None
  }
}

///|
pub fn Node::reverse_names(self : Node) -> Array[String] {
  if self.kind != Scope {
    panic()
  }
  let names : Array[String] = Array::make(self.n_ins(), "")
  for v in self._vars {
    names[v._idx] = v._name
  }
  names
}

///|
pub fn Node::mem(self : Node) -> Node {
  if self.kind != Scope {
    panic()
  }
  self.input_exn(1)
}

///|
pub fn Node::mem_alias(self : Node, alias_id : Int) -> Node {
  self.mem()._mem(alias_id, None)
}

///|
pub fn Node::mem_alias_set(self : Node, alias_id : Int, st : Node) -> Unit {
  ignore(self.mem()._mem(alias_id, Some(st)))
}

///|
fn Node::_update_var(self : Node, v : Var, st : Node?) -> Var {
  let idx = v._idx
  let mut old = self.input(idx)
  match old {
    Some(loop_scope) if loop_scope.kind == Scope => {
      let loop_def = loop_scope.input(idx)
      let phi = match loop_def {
        Some(p) if p.kind == Phi && p.input_exn(0) == loop_scope.ctrl() => p
        _ => {
          let in_v = loop_scope._update_var(v, None)
          let in_ = loop_scope.input_exn(in_v._idx)
          let declared_type = match v._type {
            MemPtr(_, _) => v._type
            _ => v._type.glb()
          }
          let phi = Node::new_phi(v._name, declared_type, [
            Some(loop_scope.ctrl()),
            Some(in_),
            None,
          ]).peephole()
          ignore(loop_scope.set_def(idx, Some(phi)))
          phi
        }
      }
      ignore(self.set_def(idx, Some(phi)))
      old = Some(phi)
    }
    _ => ()
  }
  match st {
    None => ()
    Some(n) => ignore(self.set_def(idx, Some(n)))
  }
  v
}

///|
fn Node::_alias(self : Node, alias_id : Int) -> Node {
  if self.kind != Mem {
    panic()
  }
  if alias_id < self.n_ins() {
    match self.input(alias_id) {
      Some(n) => return n
      None => ()
    }
  }
  self.input_exn(1)
}

///|
fn Node::_alias_set(self : Node, alias_id : Int, st : Node) -> Node {
  if self.kind != Mem {
    panic()
  }
  while alias_id >= self.n_ins() {
    ignore(self.add_def(None))
  }
  ignore(self.set_def(alias_id, Some(st)))
  st
}

///|
fn Node::_mem(self : Node, alias_id : Int, st : Node?) -> Node {
  if self.kind != Mem {
    panic()
  }
  let mut old = self._alias(alias_id)
  if old.kind == Scope {
    let loop_scope = old
    let loop_mem = loop_scope.mem()
    let memdef = loop_mem._alias(alias_id)
    let phi = if memdef.kind == Phi && memdef.input_exn(0) == loop_scope.ctrl() {
      memdef
    } else {
      let phi = Node::new_phi(Parser::mem_name(alias_id), type_mem_bot, [
        Some(loop_scope.ctrl()),
        Some(loop_mem._mem(alias_id, None)),
        None,
      ]).peephole()
      ignore(loop_mem._alias_set(alias_id, phi))
      phi
    }
    old = phi
    ignore(self._alias_set(alias_id, phi))
  }
  match st {
    None => old
    Some(n) => self._alias_set(alias_id, n)
  }
}

///|
fn Node::_merge_mem(self : Node, that : Node, r : Node) -> Unit {
  if self.kind != Mem || that.kind != Mem {
    panic()
  }
  let len = if self.n_ins() > that.n_ins() {
    self.n_ins()
  } else {
    that.n_ins()
  }
  for i = 2; i < len; i = i + 1 {
    if self._alias(i) != that._alias(i) {
      let lhs = self._mem(i, None)
      let rhs = that._mem(i, None)
      let phi = Node::new_phi(Parser::mem_name(i), type_mem_bot, [
        Some(r),
        Some(lhs),
        Some(rhs),
      ]).peephole()
      ignore(self._alias_set(i, phi))
    }
  }
}

///|
fn Node::_merge_scope(self : Node, that : Node, r : Node) -> Unit {
  for i = 2; i < self.n_ins(); i = i + 1 {
    if self.input(i) != that.input(i) {
      let v = self._vars[i]
      ignore(self._update_var(v, None))
      ignore(that._update_var(v, None))
      let phi = Node::new_phi(v._name, v._type, [
        Some(r),
        Some(self.input_exn(i)),
        Some(that.input_exn(i)),
      ]).peephole()
      ignore(self.set_def(i, Some(phi)))
    }
  }
}

///|
fn Node::_end_loop_mem(
  self : Node,
  scope : Node,
  back : Node,
  exit : Node,
) -> Unit {
  if self.kind != Mem ||
    scope.kind != Scope ||
    back.kind != Mem ||
    exit.kind != Mem {
    panic()
  }
  for i = 2; i < back.n_ins(); i = i + 1 {
    if back.input(i) != Some(scope) {
      let phi = self.input_exn(i)
      if phi.kind != Phi ||
        phi.input_exn(0) != scope.ctrl() ||
        phi.input(2) is Some(_) {
        panic()
      }
      ignore(phi.set_def(2, back.input(i)))
    }
    if exit._alias(i) == scope {
      ignore(exit._alias_set(i, self.input_exn(i)))
    }
  }
}

///|
fn Node::_end_loop_scope(
  self : Node,
  scope : Node,
  back : Node,
  exit : Node,
) -> Unit {
  if self.kind != Scope ||
    scope.kind != Scope ||
    back.kind != Scope ||
    exit.kind != Scope {
    panic()
  }
  for i = 2; i < self.n_ins(); i = i + 1 {
    if back.input(i) != Some(scope) {
      let phi = self.input_exn(i)
      if phi.kind != Phi ||
        phi.input_exn(0) != scope.ctrl() ||
        phi.input(2) is Some(_) {
        panic()
      }
      ignore(phi.set_def(2, back.input(i)))
    }
    if exit.input(i) == Some(scope) {
      ignore(exit.set_def(i, self.input(i)))
    }
  }
}

///|
fn Node::_useless_mem(self : Node) -> Unit {
  if self.kind != Mem {
    panic()
  }
  for i = 2; i < self.n_ins(); i = i + 1 {
    match self.input(i) {
      Some(phi) if phi.kind == Phi => {
        let in_ = phi.peephole()
        IterPeeps::add_all(phi._outputs)
        phi.move_deps_to_worklist()
        if in_ != phi {
          phi.subsume(in_)
          ignore(self.set_def(i, Some(in_)))
        }
      }
      _ => ()
    }
  }
}

///|
fn Node::_useless_scope(self : Node) -> Unit {
  if self.kind != Scope {
    panic()
  }
  for i = 2; i < self.n_ins(); i = i + 1 {
    match self.input(i) {
      Some(phi) if phi.kind == Phi => {
        let in_ = phi.peephole()
        IterPeeps::add_all(phi._outputs)
        phi.move_deps_to_worklist()
        if in_ != phi {
          phi.subsume(in_)
          ignore(self.set_def(i, Some(in_)))
        }
      }
      _ => ()
    }
  }
}

///|
pub fn Node::dup(self : Node, is_loop? : Bool = false) -> Node {
  if self.kind != Scope {
    panic()
  }
  let dup = Node::new_scope()
  for v in self._vars {
    dup._vars.push(v)
  }
  for n in self._lex_size {
    dup._lex_size.push(n)
  }
  for b in self._in_cons {
    dup._in_cons.push(b)
  }
  for g in self._guards {
    if !g.is_cfg() {
      ignore(g.keep())
    }
    dup._guards.push(g)
  }
  ignore(dup.add_def(Some(self.ctrl())))
  let mem = self.mem()
  let memdup = Node::new_mem()
  ignore(memdup.add_def(None))
  ignore(memdup.add_def(if is_loop { Some(self) } else { mem.input(1) }))
  for i = 2; i < mem.n_ins(); i = i + 1 {
    ignore(memdup.add_def(if is_loop { Some(self) } else { mem.input(i) }))
  }
  ignore(dup.add_def(Some(memdup)))
  for i = 2; i < self.n_ins(); i = i + 1 {
    ignore(dup.add_def(if is_loop { Some(self) } else { self.input(i) }))
  }
  dup
}

///|
pub fn Node::merge_scopes(self : Node, that : Node) -> Node {
  if self.kind != Scope || that.kind != Scope {
    panic()
  }
  let r = Node::new_region(self.input(0), that.input(0)).keep()
  ignore(self.set_def(0, Some(r)))
  self.mem()._merge_mem(that.mem(), r)
  self._merge_scope(that, r)
  that.kill()
  r.unkeep().peephole()
}

///|
pub fn Node::end_loop(self : Node, back : Node, exit : Node) -> Unit {
  if self.kind != Scope || back.kind != Scope || exit.kind != Scope {
    panic()
  }
  let ctrl = self.ctrl()
  if ctrl.kind != Loop || !ctrl.in_progress() {
    panic()
  }
  ignore(ctrl.set_def(2, Some(back.ctrl())))
  self.mem()._end_loop_mem(self, back.mem(), exit.mem())
  self._end_loop_scope(self, back, exit)
  back.kill()
  self.mem()._useless_mem()
  self._useless_scope()

  // The exit mem's lazy default value had been the loop top,
  // now it goes back to predating the loop.
  ignore(exit.mem().set_def(1, self.mem().input(1)))
}

///|
pub fn Node::upcast_(
  self : Node,
  ctrl : Node,
  pred : Node,
  invert : Bool,
) -> Node? {
  if self.kind != Scope {
    panic()
  }
  if ctrl.ty() == xcontrol {
    return None
  }
  let pred = if invert {
    if pred.kind == Not {
      pred.input_exn(1)
    } else {
      Node::new_not(pred).peephole()
    }
  } else {
    pred
  }

  // Direct use of a value as predicate. This is a zero/null test.
  if _find_use(self._inputs, Some(pred)) != -1 {
    match pred.ty() {
      MemPtr(_, _) =>
        if pred.ty().isa(type_mem_ptr_voidptr) {
          return None
        } else {
          let cast = Node::new_cast(type_mem_ptr_voidptr, Some(ctrl), pred).peephole()
          return Some(self.replace(pred, cast))
        }
      _ => return None
    }
  }
  if pred.kind == Not {
    let x = pred.input_exn(1)
    if _find_use(self._inputs, Some(x)) != -1 {
      let tinit = x.ty().make_init()
      if x.ty().isa(tinit) {
        return None
      }
      return Some(self.replace(x, Node::new_constant(tinit).peephole()))
    }
  }
  None
}

///|
fn Node::replace(self : Node, old : Node, cast : Node) -> Node {
  for i = 0; i < self.n_ins(); i = i + 1 {
    if self.input(i) == Some(old) {
      ignore(self.set_def(i, Some(cast)))
    }
  }
  cast
}
