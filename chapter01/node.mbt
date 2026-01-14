///|
pub enum NodeKind {
  Start
  Return
  Constant
} derive(Eq, Show)

///|
pub struct Node {
  _nid : Int
  mut _inputs : Array[Node?]
  mut _outputs : Array[Node]
  kind : NodeKind
  _value : Int64
}

///|
let _unique_id : Ref[Int] = Ref::{ val: 1 }

///|
pub let start : Ref[Node] = Ref::{ val: Node::new_start() }

///|
pub fn Node::reset() -> Unit {
  _unique_id.val = 1
}

///|
fn Node::new_raw(
  kind : NodeKind,
  inputs : Array[Node?],
  value? : Int64 = 0L,
) -> Node {
  let nid = _unique_id.val
  _unique_id.val += 1
  let node : Node = {
    _nid: nid,
    _inputs: inputs,
    _outputs: [],
    kind,
    _value: value,
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
pub fn Node::new_constant(value : Int64) -> Node {
  Node::new_raw(Constant, [Some(start.val)], value~)
}

///|
pub fn Node::new_return(ctrl : Node, data : Node) -> Node {
  Node::new_raw(Return, [Some(ctrl), Some(data)])
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
pub impl Eq for Node with equal(self, other) {
  self._nid == other._nid
}

///|
pub impl Show for Node with output(self, logger) {
  match self.kind {
    Start => logger.write_string("Start#\{self._nid}")
    Return => logger.write_string("Return#\{self._nid}")
    Constant => logger.write_string("Constant#\{self._nid}(\{self._value})")
  }
}
