///|
pub enum NodeKind {
  Start
  Return
  Constant
  Add
  Sub
  Mul
  Div
  Minus
} derive(Eq, Show)

///|
pub struct Node {
  _nid : Int
  mut _inputs : Array[Node?]
  mut _outputs : Array[Node]
  mut _type : Type?
  kind : NodeKind
  _con : Type?
}

///|
let _unique_id : Ref[Int] = Ref::{ val: 1 }

///|
pub let start : Ref[Node] = Ref::{ val: Node::new_start() }

///|
pub let disable_peephole : Ref[Bool] = Ref::{ val: false }

///|
pub fn Node::reset() -> Unit {
  _unique_id.val = 1
}

///|
fn _find_node(ary : Array[Node], node : Node) -> Int {
  for i, x in ary {
    if x._nid == node._nid {
      return i
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
fn Node::new_raw(kind : NodeKind, inputs : Array[Node?], con? : Type) -> Node {
  let nid = _unique_id.val
  _unique_id.val += 1
  let node : Node = {
    _nid: nid,
    _inputs: inputs,
    _outputs: [],
    _type: None,
    kind,
    _con: con,
  }
  for input in node._inputs {
    match input {
      Some(n) => n._outputs.push(node)
      None => ()
    }
  }
  node
}

///|
pub fn Node::new_start() -> Node {
  Node::new_raw(Start, [])
}

///|
pub fn Node::new_return(ctrl : Node, data : Node) -> Node {
  Node::new_raw(Return, [Some(ctrl), Some(data)])
}

///|
pub fn Node::new_constant(con : Type) -> Node {
  Node::new_raw(Constant, [Some(start.val)], con~)
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
pub fn Node::label(self : Node) -> String {
  match self.kind {
    Start => "Start"
    Return => "Return"
    Constant => {
      let con = match self._con {
        Some(con) => con
        None => bottom
      }
      "#\{con}"
    }
    Add => "Add"
    Sub => "Sub"
    Mul => "Mul"
    Div => "Div"
    Minus => "Minus"
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
  self.kind is Start || self.kind is Return
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
fn Node::add_use(self : Node, user : Node) -> Unit {
  self._outputs.push(user)
}

///|
fn Node::del_use(self : Node, user : Node) -> Bool {
  let idx = _find_node(self._outputs, user)
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
    Some(n) => n.add_use(self)
    None => ()
  }
  match old_def {
    Some(old) => if old.del_use(self) { old.kill() }
    None => ()
  }
  self._inputs[idx] = new_def
  new_def
}

///|
pub fn Node::kill(self : Node) -> Unit {
  if !self.is_unused() {
    panic()
  }
  for i = 0; i < self.n_ins(); i = i + 1 {
    ignore(self.set_def(i, None))
  }
  self._inputs.clear()
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
pub fn Node::compute(self : Node) -> Type {
  match self.kind {
    Start | Return => bottom
    Constant =>
      match self._con {
        Some(con) => con
        None => bottom
      }
    Add => {
      let t1 = self.input_exn(1)._type
      let t2 = self.input_exn(2)._type
      match (t1, t2) {
        (Some(Int(v0)), Some(Int(v1))) =>
          if Int(v0).is_constant() && Int(v1).is_constant() {
            TypeInteger::constant(v0 + v1)
          } else {
            bottom
          }
        _ => bottom
      }
    }
    Sub => {
      let t1 = self.input_exn(1)._type
      let t2 = self.input_exn(2)._type
      match (t1, t2) {
        (Some(Int(v0)), Some(Int(v1))) =>
          if Int(v0).is_constant() && Int(v1).is_constant() {
            TypeInteger::constant(v0 - v1)
          } else {
            bottom
          }
        _ => bottom
      }
    }
    Mul => {
      let t1 = self.input_exn(1)._type
      let t2 = self.input_exn(2)._type
      match (t1, t2) {
        (Some(Int(v0)), Some(Int(v1))) =>
          if Int(v0).is_constant() && Int(v1).is_constant() {
            TypeInteger::constant(v0 * v1)
          } else {
            bottom
          }
        _ => bottom
      }
    }
    Div => {
      let t1 = self.input_exn(1)._type
      let t2 = self.input_exn(2)._type
      match (t1, t2) {
        (Some(Int(v0)), Some(Int(v1))) =>
          if Int(v0).is_constant() && Int(v1).is_constant() {
            if v1 == 0L {
              type_integer_zero
            } else {
              TypeInteger::constant(v0 / v1)
            }
          } else {
            bottom
          }
        _ => bottom
      }
    }
    Minus => {
      let t1 = self.input_exn(1)._type
      match t1 {
        Some(Int(v0)) =>
          if Int(v0).is_constant() {
            TypeInteger::constant(-v0)
          } else {
            Int(v0)
          }
        _ => bottom
      }
    }
  }
}

///|
pub fn Node::idealize(_self : Node) -> Node? {
  None
}

///|
pub fn Node::peephole(self : Node) -> Node {
  let typ = self.compute()
  self._type = Some(typ)
  if disable_peephole.val {
    return self
  }
  if self.kind != Constant && typ.is_constant() {
    self.kill()
    return Node::new_constant(typ).peephole()
  }
  match self.idealize() {
    Some(n) => n
    None => self
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
    Return => {
      sb.write_string("return ")
      self.expr()._print0(sb)
      sb.write_string(";")
    }
    Constant =>
      match self._con {
        Some(con) => con.print_to(sb)
        None => sb.write_string("0")
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
  }
}

///|
pub impl Eq for Node with equal(self, other) {
  self._nid == other._nid
}
