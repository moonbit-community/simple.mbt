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
pub fn Node::reset() -> Unit {
  _unique_id.val = 1
  disable_peephole.val = false
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
    Start | Stop | Return | If | Region => true
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
pub fn Node::del_def(self : Node, idx : Int) -> Unit {
  let old_def = self._inputs[idx]
  match old_def {
    Some(old) => if old.del_use(Some(self)) { old.kill() }
    None => ()
  }
  let last = self._inputs.remove(self._inputs.length() - 1)
  if idx < self._inputs.length() {
    self._inputs[idx] = last
  }
}

///|
pub fn Node::add_def(self : Node, new_def : Node?) -> Node? {
  self._inputs.push(new_def)
  match new_def {
    Some(n) => n.add_use(Some(self))
    None => ()
  }
  new_def
}

///|
pub fn Node::pop_n(self : Node, n : Int) -> Unit {
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
  if !self.is_unused() {
    panic()
  }
  self.pop_n(self.n_ins())
  self._type = None
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
fn Node::dead_code_elim(self : Node, m : Node) -> Node {
  if m._nid != self._nid && self.is_unused() {
    ignore(m.keep())
    self.kill()
    ignore(m.unkeep())
  }
  m
}

///|
fn Node::swap12(self : Node) -> Node {
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
pub fn Node::all_cons(self : Node) -> Bool {
  for i = 1; i < self.n_ins(); i = i + 1 {
    match self._inputs[i] {
      Some(n) => if !n.ty().is_constant() { return false }
      None => return false
    }
  }
  true
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
    Some(idom) => return Some(idom)
    None => ()
  }
  if self.n_ins() != 3 {
    return None
  }
  match (self.input(1), self.input(2)) {
    (Some(n1), Some(n2)) => {
      let mut lhs = n1.idom()
      let mut rhs = n2.idom()
      while true {
        match (lhs, rhs) {
          (Some(l), Some(r)) if l == r => {
            self._idepth = l._idepth + 1
            self._idom = Some(l)
            return Some(l)
          }
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
      None
    }
    _ => None
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
      if self.ctrl().ty() != control {
        return type_tuple_if_neither
      }
      match self.input_exn(1).ty() {
        Int(v) =>
          return if v == 0L { type_tuple_if_false } else { type_tuple_if_true }
        _ => ()
      }
      let mut dom = self.idom()
      let mut prior : Node = self
      while dom is Some(d) {
        if d.kind == If && d.input_exn(1) == self.input_exn(1) {
          if prior.kind == Proj {
            return if prior._proj_idx == 0 {
              type_tuple_if_true
            } else {
              type_tuple_if_false
            }
          }
          return type_tuple_if_both
        }
        prior = d
        dom = d.idom()
      }
      type_tuple_if_both
    }
    Region => {
      let mut t = xcontrol
      for i = 1; i < self.n_ins(); i = i + 1 {
        t = t.meet(self.input_exn(i).ty())
      }
      t
    }
    Phi => {
      let mut t = top
      for i = 1; i < self.n_ins(); i = i + 1 {
        t = t.meet(self.input_exn(i).ty())
      }
      t
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
fn _spline_cmp(hi : Node, lo : Node) -> Bool {
  if lo.ty().is_constant() {
    return false
  }
  if hi.ty().is_constant() {
    return true
  }
  if lo.kind == Phi && lo.all_cons() {
    return false
  }
  if hi.kind == Phi && hi.all_cons() {
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
fn Node::pcon(op : Node) -> Node? {
  if op.kind == Phi && op.all_cons() {
    Some(op)
  } else {
    None
  }
}

///|
fn Node::phi_con(self : Node, rotate : Bool) -> Node? {
  let lhs = self.input_exn(1)
  let rhs = self.input_exn(2)
  let mut lphi = Node::pcon(lhs)
  if rotate && lphi is None && lhs.n_ins() > 2 {
    if lhs.kind != self.kind {
      return None
    }
    lphi = Node::pcon(lhs.input_exn(2))
  }
  let lphi_node = match lphi {
    Some(phi) => phi
    None => return None
  }
  let rhs_phi = Node::pcon(rhs)
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
  if rhs.kind == Add {
    let add_lhs = rhs.input_exn(1)
    let add_rhs = rhs.input_exn(2)
    let left = Node::new_add(lhs, add_lhs).peephole()
    return Some(Node::new_add(left, add_rhs))
  }
  if lhs.kind != Add {
    if _spline_cmp(lhs, rhs) {
      ignore(self.swap12())
      return Some(self)
    }
    return self.phi_con(true)
  }
  let lhs_rhs = lhs.input_exn(2)
  if lhs_rhs.ty().is_constant() && t2.is_constant() {
    let folded = Node::new_add(lhs_rhs, rhs).peephole()
    return Some(Node::new_add(lhs.input_exn(1), folded))
  }
  match self.phi_con(true) {
    Some(n) => return Some(n)
    None => ()
  }
  if _spline_cmp(lhs_rhs, rhs) {
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
fn Node::find_dead_input(self : Node) -> Int {
  for i = 1; i < self.n_ins(); i = i + 1 {
    if self.input_exn(i).ty() == xcontrol {
      return i
    }
  }
  0
}

///|
fn Node::idealize_region(self : Node) -> Node? {
  let path = self.find_dead_input()
  if path != 0 {
    for out in self._outputs {
      match out {
        Some(phi) if phi.kind == Phi => phi.del_def(path)
        _ => ()
      }
    }
    self.del_def(path)
    if self.n_ins() == 2 {
      for out in self._outputs {
        match out {
          Some(phi) if phi.kind == Phi => panic()
          _ => ()
        }
      }
      return Some(self.input_exn(1))
    }
    return Some(self)
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
      self.del_def(i)
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
  let mut live : Node? = None
  for i = 1; i < self.n_ins(); i = i + 1 {
    let is_alive = match region.input(i) {
      Some(ctrl) => ctrl.ty() != xcontrol
      None => false
    }
    if is_alive {
      let in_i = self.input_exn(i)
      if in_i != self {
        match live {
          None => live = Some(in_i)
          Some(l) => if l != in_i { return None }
        }
      }
    }
  }
  live
}

///|
fn Node::idealize_phi(self : Node) -> Node? {
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
    BoolEq | BoolLt | BoolLe => self.idealize_bool()
    Proj => self.idealize_proj()
    Return => self.idealize_return()
    Stop => self.idealize_stop()
    Region => self.idealize_region()
    Phi => self.idealize_phi()
    _ => None
  }
}

///|
pub fn Node::peephole(self : Node) -> Node {
  let typ = self.compute()
  self._type = Some(typ)
  if disable_peephole.val {
    return self
  }
  if self.kind != Constant && typ.is_constant() {
    let con = Node::new_constant(typ).peephole()
    return self.dead_code_elim(con)
  }
  match self.idealize() {
    Some(n) => self.dead_code_elim(n.peephole())
    None => self
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
pub fn Node::print(self : Node) -> String {
  let sb = StringBuilder::new()
  self._print0(sb)
  sb.to_string()
}

///|
fn Node::_print0(self : Node, sb : StringBuilder) -> Unit {
  if self.is_dead() {
    sb.write_string(self.unique_name())
    sb.write_string(":DEAD")
  } else {
    self._print1(sb)
  }
}

///|
fn Node::_print1(self : Node, sb : StringBuilder) -> Unit {
  match self.kind {
    Start => sb.write_string(self.label())
    Stop => {
      if self.n_ins() == 1 {
        match self.input(0) {
          Some(ret) => return ret._print0(sb)
          None => ()
        }
      }
      sb.write_string("Stop[ ")
      for input in self._inputs {
        match input {
          Some(ret) => {
            ret._print0(sb)
            sb.write_string(" ")
          }
          None => ()
        }
      }
      sb.write_string("]")
    }
    Return => {
      sb.write_string("return ")
      self.expr()._print0(sb)
      sb.write_string(";")
    }
    Constant =>
      match self._con {
        Some(con) => con.print_to(sb)
        None => bottom.print_to(sb)
      }
    Add => {
      sb.write_string("(")
      self.input_exn(1)._print0(sb)
      sb.write_string("+")
      self.input_exn(2)._print0(sb)
      sb.write_string(")")
    }
    Sub => {
      sb.write_string("(")
      self.input_exn(1)._print0(sb)
      sb.write_string("-")
      self.input_exn(2)._print0(sb)
      sb.write_string(")")
    }
    Mul => {
      sb.write_string("(")
      self.input_exn(1)._print0(sb)
      sb.write_string("*")
      self.input_exn(2)._print0(sb)
      sb.write_string(")")
    }
    Div => {
      sb.write_string("(")
      self.input_exn(1)._print0(sb)
      sb.write_string("/")
      self.input_exn(2)._print0(sb)
      sb.write_string(")")
    }
    Minus => {
      sb.write_string("(-")
      self.input_exn(1)._print0(sb)
      sb.write_string(")")
    }
    Not => {
      sb.write_string("(!")
      self.input_exn(1)._print0(sb)
      sb.write_string(")")
    }
    If => {
      sb.write_string("if( ")
      self.input_exn(1)._print0(sb)
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
      self.input_exn(1)._print0(sb)
      sb.write_string(op)
      self.input_exn(2)._print0(sb)
      sb.write_string(")")
    }
    Region => sb.write_string("Region\{self._nid}")
    Phi => {
      sb.write_string("Phi(")
      let mut first = true
      for input in self._inputs {
        if !first {
          sb.write_string(",")
        }
        first = false
        match input {
          Some(n) => n._print0(sb)
          None => sb.write_string("null")
        }
      }
      sb.write_string(")")
    }
    Scope => {
      sb.write_string(self.label())
      for scope in self._scopes {
        sb.write_string("[")
        let mut first = true
        for name, idx in scope {
          if !first {
            sb.write_string(", ")
          }
          first = false
          sb.write_string(name)
          sb.write_string(":")
          match self._inputs[idx] {
            Some(n) => n._print0(sb)
            None => sb.write_string("null")
          }
        }
        sb.write_string("]")
      }
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
pub fn Node::define_(self : Node, name : String, n : Node) -> Node? {
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
    Some(idx) =>
      match n {
        None => self._inputs[idx]
        Some(n) => self.set_def(idx, Some(n))
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
pub fn Node::dup(self : Node) -> Node {
  if self.kind != Scope {
    panic()
  }
  let dup = Node::new_scope()
  for syms in self._scopes {
    dup._scopes.push(_clone_map(syms))
  }
  ignore(dup.add_def(self.input(0)))
  for i = 1; i < self.n_ins(); i = i + 1 {
    ignore(dup.add_def(self.input(i)))
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
      let phi = Node::new_phi(names[i], [Some(r), self.input(i), that.input(i)]).peephole()
      ignore(self.set_def(i, Some(phi)))
    }
  }
  that.kill()
  r.unkeep().peephole()
}
