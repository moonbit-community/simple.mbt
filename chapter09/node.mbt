///|
pub enum NodeKind {
  Start
  Stop
  Return
  Constant
  Add
  Sub
  Mul
  Div
  Minus
  Not
  If
  Proj
  BoolEq
  BoolLt
  BoolLe
  Region
  Loop
  Phi
  Scope
} derive(Eq, Show)

///|
pub struct Node {
  _nid : Int
  mut _inputs : Array[Node?]
  mut _outputs : Array[Node?]
  mut _type : Type?
  mut _idepth : Int
  mut _idom : Node?
  mut _deps : Array[Node]?
  mut _hash : Int
  kind : NodeKind
  mut _con : Type?
  mut _scopes : Array[Map[String, Int]]
  mut _proj_idx : Int
  mut _proj_label : String
  mut _start_args : Array[Type]
  mut _phi_label : String
}

///|
pub let scope_ctrl : String = "$ctrl"

///|
pub let scope_arg0 : String = "arg"

///|
let _unique_id : Ref[Int] = Ref::{ val: 1 }

///|
pub let start : Ref[Node] = Ref::{
  val: Node::new_start([control, type_integer_bot]),
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
    _deps: None,
    _hash: 0,
    kind,
    _con: None,
    _scopes: [],
    _proj_idx: 0,
    _proj_label: "",
    _start_args: [],
    _phi_label: "",
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
  node._type = Some(Tuple(args))
  node
}

///|
pub fn Node::new_stop() -> Node {
  Node::new_raw(Stop, [])
}

///|
pub fn Node::new_return(ctrl : Node?, data : Node) -> Node {
  Node::new_raw(Return, [ctrl, Some(data)])
}

///|
pub fn Node::new_constant(con : Type) -> Node {
  let node = Node::new_raw(Constant, [Some(start.val)])
  node._con = Some(con)
  node
}

///|
pub fn Node::new_add(lhs : Node, rhs : Node) -> Node {
  Node::new_raw(Add, [None, Some(lhs), Some(rhs)])
}

///|
pub fn Node::new_sub(lhs : Node, rhs : Node) -> Node {
  Node::new_raw(Sub, [None, Some(lhs), Some(rhs)])
}

///|
pub fn Node::new_mul(lhs : Node, rhs : Node) -> Node {
  Node::new_raw(Mul, [None, Some(lhs), Some(rhs)])
}

///|
pub fn Node::new_div(lhs : Node, rhs : Node) -> Node {
  Node::new_raw(Div, [None, Some(lhs), Some(rhs)])
}

///|
pub fn Node::new_minus(input : Node) -> Node {
  Node::new_raw(Minus, [None, Some(input)])
}

///|
pub fn Node::new_not(input : Node) -> Node {
  Node::new_raw(Not, [None, Some(input)])
}

///|
pub fn Node::new_if(ctrl : Node?, pred : Node) -> Node {
  Node::new_raw(If, [ctrl, Some(pred)])
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
pub fn Node::new_bool_lt(lhs : Node, rhs : Node) -> Node {
  Node::new_raw(BoolLt, [None, Some(lhs), Some(rhs)])
}

///|
pub fn Node::new_bool_le(lhs : Node, rhs : Node) -> Node {
  Node::new_raw(BoolLe, [None, Some(lhs), Some(rhs)])
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
pub fn Node::new_phi(label : String, inputs : Array[Node?]) -> Node {
  let node = Node::new_raw(Phi, inputs)
  node._phi_label = label
  node
}

///|
pub fn Node::new_scope() -> Node {
  let node = Node::new_raw(Scope, [])
  node._type = Some(bottom)
  node
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
    Add => "Add"
    Sub => "Sub"
    Mul => "Mul"
    Div => "Div"
    Minus => "Minus"
    Not => "Not"
    If => "If"
    Proj => self._proj_label
    BoolEq => "EQ"
    BoolLt => "LT"
    BoolLe => "LE"
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
    Add => "+"
    Sub => "-"
    Mul => "*"
    Div => "//"
    Minus => "-"
    Not => "!"
    BoolEq => "=="
    BoolLt => "<"
    BoolLe => "<="
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
    Start | Stop | Return | If | Region | Loop => true
    Proj => self._proj_idx == 0 || self.input_exn(0).kind == If
    _ => false
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
    Proj => self._proj_idx == other._proj_idx
    Region | Loop | Phi => !self.in_progress()
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
    Proj => self._proj_idx
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
fn Node::ty(self : Node) -> Type {
  match self._type {
    Some(t) => t
    None => bottom
  }
}

///|
fn _is_int_type(t : Type) -> Bool {
  match t {
    IntTop | IntBot | Int(_) => true
    _ => false
  }
}

///|
fn Node::bool_do_op(self : Node, lhs : Int64, rhs : Int64) -> Bool {
  match self.kind {
    BoolEq => lhs == rhs
    BoolLt => lhs < rhs
    BoolLe => lhs <= rhs
    _ => false
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
    Sub => Node::new_sub(lhs, rhs)
    Mul => Node::new_mul(lhs, rhs)
    Div => Node::new_div(lhs, rhs)
    BoolEq => Node::new_bool_eq(lhs, rhs)
    BoolLt => Node::new_bool_lt(lhs, rhs)
    BoolLe => Node::new_bool_le(lhs, rhs)
    _ => panic()
  }
}

///|
fn Node::idom(self : Node) -> Node? {
  match self.kind {
    Start => None
    Region => self.region_idom()
    Loop =>
      match self.input(1) {
        Some(entry) => {
          if entry._idepth == 0 {
            ignore(entry.idom())
          }
          if self._idepth == 0 {
            self._idepth = entry._idepth + 1
          }
          Some(entry)
        }
        None => None
      }
    _ =>
      match self.input(0) {
        Some(idom) => {
          if idom._idepth == 0 {
            ignore(idom.idom())
          }
          if self._idepth == 0 {
            self._idepth = idom._idepth + 1
          }
          Some(idom)
        }
        None => None
      }
  }
}

///|
fn Node::region_idom(self : Node) -> Node? {
  match self._idom {
    Some(idom) =>
      if idom.is_dead() {
        self._idom = None
      } else {
        return Some(idom)
      }
    None => ()
  }
  if self.n_ins() == 2 {
    return Some(self.input_exn(1))
  }
  if self.n_ins() != 3 {
    return None
  }
  let mut lhs = self.input_exn(1).idom()
  let mut rhs = self.input_exn(2).idom()
  while lhs != rhs {
    match (lhs, rhs) {
      (Some(l), Some(r)) => {
        let comp = l._idepth - r._idepth
        if comp >= 0 {
          lhs = l.idom()
        }
        if comp <= 0 {
          rhs = r.idom()
        }
      }
      _ => return None
    }
  }
  match lhs {
    Some(l) => {
      self._idepth = l._idepth + 1
      if !IterPeeps::mid_assert() {
        self._idom = Some(l)
      }
      Some(l)
    }
    None => None
  }
}

///|
pub fn Node::compute(self : Node) -> Type {
  match self.kind {
    Start =>
      match self._type {
        Some(t) => t
        None => Tuple(self._start_args)
      }
    Stop | Scope => bottom
    Return => {
      let ctrl_ty = match self._inputs[0] {
        Some(n) => n.ty()
        None => bottom
      }
      let expr_ty = match self._inputs[1] {
        Some(n) => n.ty()
        None => bottom
      }
      Tuple([ctrl_ty, expr_ty])
    }
    Constant =>
      match self._con {
        Some(con) => con
        None => bottom
      }
    Proj => {
      let ctrl_ty = self.input_exn(0).ty()
      match ctrl_ty {
        Tuple(types) if self._proj_idx < types.length() => types[self._proj_idx]
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
        Int(v) =>
          return if v == 0L { type_tuple_if_false } else { type_tuple_if_true }
        _ => ()
      }
      type_tuple_if_both
    }
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
    Phi => {
      match self.input(0) {
        Some(region) =>
          if region.kind != Region && region.kind != Loop {
            if region.ty() == xcontrol { top } else { self.ty() }
          } else if region.in_progress() {
            bottom
          } else {
            let mut t = top
            for i = 1; i < self.n_ins(); i = i + 1 {
              if region.input_exn(i).add_dep(self).ty() != xcontrol && self.input_exn(i) != self {
                t = t.meet(self.input_exn(i).ty())
              }
            }
            t
          }
        None => bottom
      }
    }
    Add => {
      let t1 = self.input_exn(1).ty()
      let t2 = self.input_exn(2).ty()
      if _is_int_type(t1) && _is_int_type(t2) {
        match (t1, t2) {
          (Int(v0), Int(v1)) => TypeInteger::constant(v0 + v1)
          _ => t1.meet(t2)
        }
      } else {
        bottom
      }
    }
    Sub => {
      if self.input_exn(1) == self.input_exn(2) {
        return type_integer_zero
      }
      let t1 = self.input_exn(1).ty()
      let t2 = self.input_exn(2).ty()
      if _is_int_type(t1) && _is_int_type(t2) {
        match (t1, t2) {
          (Int(v0), Int(v1)) => TypeInteger::constant(v0 - v1)
          _ => t1.meet(t2)
        }
      } else {
        bottom
      }
    }
    Mul => {
      let t1 = self.input_exn(1).ty()
      let t2 = self.input_exn(2).ty()
      if _is_int_type(t1) && _is_int_type(t2) {
        match (t1, t2) {
          (Int(v0), Int(v1)) => TypeInteger::constant(v0 * v1)
          _ => t1.meet(t2)
        }
      } else {
        bottom
      }
    }
    Div => {
      let t1 = self.input_exn(1).ty()
      let t2 = self.input_exn(2).ty()
      if _is_int_type(t1) && _is_int_type(t2) {
        match (t1, t2) {
          (Int(v0), Int(v1)) =>
            if v1 == 0L {
              type_integer_zero
            } else {
              TypeInteger::constant(v0 / v1)
            }
          _ => t1.meet(t2)
        }
      } else {
        bottom
      }
    }
    Minus => {
      let t1 = self.input_exn(1).ty()
      match t1 {
        Int(v) => TypeInteger::constant(-v)
        IntTop | IntBot => t1
        _ => bottom
      }
    }
    Not => {
      let t1 = self.input_exn(1).ty()
      match t1 {
        Int(v) => TypeInteger::constant(if v == 0L { 1L } else { 0L })
        IntTop | IntBot => t1
        _ => bottom
      }
    }
    BoolEq | BoolLt | BoolLe => {
      let t1 = self.input_exn(1).ty()
      let t2 = self.input_exn(2).ty()
      if _is_int_type(t1) && _is_int_type(t2) {
        match (t1, t2) {
          (Int(v0), Int(v1)) =>
            TypeInteger::constant(if self.bool_do_op(v0, v1) { 1L } else { 0L })
          _ => t1.meet(t2)
        }
      } else {
        bottom
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
  let phi = Node::new_phi(label, ns).peephole()
  if lhs == lphi_node {
    Some(phi)
  } else {
    Some(self.copy(lhs.input_exn(1), phi))
  }
}

///|
fn Node::idealize_add(self : Node) -> Node? {
  let lhs = self.input_exn(1)
  let rhs = self.input_exn(2)
  let t2 = rhs.ty()
  match t2 {
    Int(v) if v == 0L => return Some(lhs)
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
    Int(v) if v == 1L => return Some(lhs)
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
    Int(v) if v == 1L => Some(self.input_exn(1))
    _ => None
  }
}

///|
fn Node::idealize_bool(self : Node) -> Node? {
  if self.input_exn(1) == self.input_exn(2) {
    let value = if self.bool_do_op(3L, 3L) { 1L } else { 0L }
    return Some(Node::new_constant(TypeInteger::constant(value)))
  }
  self.phi_con(false)
}

///|
fn Node::idealize_proj(self : Node) -> Node? {
  let other = 1 - self._proj_idx
  match self.input_exn(0).ty() {
    Tuple(types) =>
      if other >= 0 && other < types.length() && types[other] == xcontrol {
        Some(self.input_exn(0).input_exn(0))
      } else {
        None
      }
    _ => None
  }
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
      prior.kind == Proj {
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
  if path != 0 &&
    !(self.kind == Loop && self.input(1) == self.input(path)) {
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
      return Some(Node::new_constant(xcontrol))
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
    if region.input_exn(i).add_dep(self).ty() != xcontrol && self.input_exn(i) != self {
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
  match self.input(0) {
    Some(region) =>
      if region.kind != Region && region.kind != Loop {
        return Some(self.input_exn(1))
      } else if region.in_progress() || region.n_ins() <= 1 {
        return None
      }
    None => return None
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
    let phi_lhs = Node::new_phi(self._phi_label, lhss).peephole()
    let phi_rhs = Node::new_phi(self._phi_label, rhss).peephole()
    return Some(op.copy(phi_lhs, phi_rhs))
  }
  None
}

///|
pub fn Node::idealize(self : Node) -> Node? {
  match self.kind {
    Add => self.idealize_add()
    Mul => self.idealize_mul()
    Div => self.idealize_div()
    If => self.idealize_if()
    BoolEq | BoolLt | BoolLe => self.idealize_bool()
    Proj => self.idealize_proj()
    Return => self.idealize_return()
    Stop => self.idealize_stop()
    Region => self.idealize_region()
    Loop => self.idealize_region()
    Phi => self.idealize_phi()
    _ => None
  }
}

///|
pub fn Node::set_type(self : Node, typ : Type) -> Type? {
  let old = self._type
  match old {
    Some(o) =>
      if !typ.isa(o) {
        panic()
      } else if o == typ {
        return old
      }
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
  if self.kind != Constant && typ.is_high_or_const() {
    let con = Node::new_constant(typ)
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
    Some(n) => self.dead_code_elim(n.peephole())
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
pub fn Node::iterate(self : Node, show? : Bool = false) -> Node {
  if self.kind != Stop {
    panic()
  }
  IterPeeps::iterate(self, show=show)
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
    Add => {
      sb.write_string("(")
      self.input_exn(1)._print0(sb, visited)
      sb.write_string("+")
      self.input_exn(2)._print0(sb, visited)
      sb.write_string(")")
    }
    Sub => {
      sb.write_string("(")
      self.input_exn(1)._print0(sb, visited)
      sb.write_string("-")
      self.input_exn(2)._print0(sb, visited)
      sb.write_string(")")
    }
    Mul => {
      sb.write_string("(")
      self.input_exn(1)._print0(sb, visited)
      sb.write_string("*")
      self.input_exn(2)._print0(sb, visited)
      sb.write_string(")")
    }
    Div => {
      sb.write_string("(")
      self.input_exn(1)._print0(sb, visited)
      sb.write_string("/")
      self.input_exn(2)._print0(sb, visited)
      sb.write_string(")")
    }
    Minus => {
      sb.write_string("(-")
      self.input_exn(1)._print0(sb, visited)
      sb.write_string(")")
    }
    Not => {
      sb.write_string("(!")
      self.input_exn(1)._print0(sb, visited)
      sb.write_string(")")
    }
    If => {
      sb.write_string("if( ")
      self.input_exn(1)._print0(sb, visited)
      sb.write_string(" )")
    }
    Proj => sb.write_string(self._proj_label)
    BoolEq | BoolLt | BoolLe => {
      let op = match self.kind {
        BoolEq => "=="
        BoolLt => "<"
        BoolLe => "<="
        _ => "?"
      }
      sb.write_string("(")
      self.input_exn(1)._print0(sb, visited)
      sb.write_string(op)
      self.input_exn(2)._print0(sb, visited)
      sb.write_string(")")
    }
    Region => sb.write_string("Region\{self._nid}")
    Loop => sb.write_string("Loop\{self._nid}")
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
pub fn Node::push(self : Node) -> Unit {
  if self.kind != Scope {
    panic()
  }
  let syms : Map[String, Int] = Map::new()
  self._scopes.push(syms)
}

///|
pub fn Node::pop(self : Node) -> Unit {
  if self.kind != Scope {
    panic()
  }
  match self._scopes.pop() {
    Some(syms) => self.pop_n(syms.length())
    None => panic()
  }
}

///|
pub fn Node::define(self : Node, name : String, n : Node) -> Node? {
  if self.kind != Scope {
    panic()
  }
  match self._scopes.last() {
    Some(syms) =>
      if syms.contains(name) {
        None
      } else {
        let idx = self.n_ins()
        syms[name] = idx
        self.add_def(Some(n))
      }
    None => panic()
  }
}

///|
pub fn Node::lookup(self : Node, name : String) -> Node? {
  if self.kind != Scope {
    panic()
  }
  self._update(name, None, self._scopes.length() - 1)
}

///|
pub fn Node::update(self : Node, name : String, n : Node) -> Node? {
  if self.kind != Scope {
    panic()
  }
  self._update(name, Some(n), self._scopes.length() - 1)
}

///|
fn Node::_update(
  self : Node,
  name : String,
  n : Node?,
  nesting_level : Int,
) -> Node? {
  if nesting_level < 0 {
    return None
  }
  let syms = self._scopes[nesting_level]
  match syms.get(name) {
    None => self._update(name, n, nesting_level - 1)
    Some(idx) => {
      let mut old = self._inputs[idx]
      match old {
        Some(loop_scope) if loop_scope.kind == Scope => {
          let loop_def = loop_scope.input(idx)
          let phi = match loop_def {
            Some(p) if p.kind == Phi && p.input_exn(0) == loop_scope.ctrl() => p
            _ => {
              let in_ = match loop_scope._update(name, None, nesting_level) {
                Some(v) => v
                None => panic()
              }
              let phi = Node::new_phi(name, [
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
      match n {
        None => old
        Some(n) => self.set_def(idx, Some(n))
      }
    }
  }
}

///|
pub fn Node::reverse_names(self : Node) -> Array[String] {
  if self.kind != Scope {
    panic()
  }
  let names : Array[String] = Array::make(self.n_ins(), "")
  for syms in self._scopes {
    for name, idx in syms {
      names[idx] = name
    }
  }
  names
}

///|
fn _clone_map(m : Map[String, Int]) -> Map[String, Int] {
  let m2 : Map[String, Int] = Map::new()
  for k, v in m {
    m2[k] = v
  }
  m2
}

///|
pub fn Node::dup(self : Node, is_loop? : Bool = false) -> Node {
  if self.kind != Scope {
    panic()
  }
  let dup = Node::new_scope()
  for syms in self._scopes {
    dup._scopes.push(_clone_map(syms))
  }
  ignore(dup.add_def(Some(self.ctrl())))
  for i = 1; i < self.n_ins(); i = i + 1 {
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
  let names = self.reverse_names()
  for i = 1; i < self.n_ins(); i = i + 1 {
    if self.input(i) != that.input(i) {
      let name = names[i]
      let lhs = match self.lookup(name) {
        Some(n) => Some(n)
        None => panic()
      }
      let rhs = match that.lookup(name) {
        Some(n) => Some(n)
        None => panic()
      }
      let phi = Node::new_phi(name, [Some(r), lhs, rhs]).peephole()
      ignore(self.set_def(i, Some(phi)))
    }
  }
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
  for i = 1; i < self.n_ins(); i = i + 1 {
    if back.input(i) != Some(self) {
      let phi = self.input_exn(i)
      if phi.kind != Phi || phi.input_exn(0) != ctrl || phi.input(2) is Some(_) {
        panic()
      }
      ignore(phi.set_def(2, back.input(i)))
    }
    if exit.input(i) == Some(self) {
      ignore(exit.set_def(i, self.input(i)))
    }
  }
  back.kill()
  for i = 1; i < self.n_ins(); i = i + 1 {
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
