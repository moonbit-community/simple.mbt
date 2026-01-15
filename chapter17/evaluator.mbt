///|
pub enum EvalValue {
  Int(Int64)
  Float(Double)
  Obj(Obj)
  Null
  Mem(Int)
  Tuple(Array[EvalValue])
} derive(Show)

///|
pub struct Obj {
  id : Int
  struct_ : TypeStruct
  fields : Array[EvalValue]
} derive(Show)

///|
pub enum EvalStatus {
  Value(EvalValue)
  Fallthrough
  Timeout
} derive(Show)

///|
struct Evaluator {
  schedule : Map[Int, Array[Node]]
  nodes : Array[Node?]
  values : Array[EvalValue?]
  mut next_obj_id : Int
}

///|
fn Evaluator::new(graph : Node) -> Evaluator {
  let nodes : Array[Node?] = Array::make(Node::uid() + 1, None)
  let visited_find : Array[Bool] = Array::make(Node::uid() + 1, false)
  match Evaluator::find_start(visited_find, Some(graph)) {
    None => { schedule: Map::new(), nodes, values: [], next_obj_id: 1 }
    Some(start) => {
      let visited_collect : Array[Bool] = Array::make(Node::uid() + 1, false)
      Evaluator::collect_nodes(nodes, visited_collect, start)
      let schedule = Evaluator::build_schedule(nodes)
      let values : Array[EvalValue?] = Array::make(Node::uid() + 1, None)
      { schedule, nodes, values, next_obj_id: 1 }
    }
  }
}

///|
fn _ensure_bool(visited : Array[Bool], nid : Int) -> Unit {
  while visited.length() <= nid {
    visited.push(false)
  }
}

///|
fn Evaluator::find_start(visited : Array[Bool], node : Node?) -> Node? {
  match node {
    None => None
    Some(node) =>
      if node.kind == Start {
        Some(node)
      } else {
        _ensure_bool(visited, node._nid)
        if visited[node._nid] {
          return None
        }
        visited[node._nid] = true
        for def in node._inputs {
          match Evaluator::find_start(visited, def) {
            Some(start) => return Some(start)
            None => ()
          }
        }
        for user in node._outputs {
          match Evaluator::find_start(visited, user) {
            Some(start) => return Some(start)
            None => ()
          }
        }
        None
      }
  }
}

///|
fn Evaluator::collect_nodes(
  nodes : Array[Node?],
  visited : Array[Bool],
  n : Node,
) -> Unit {
  _ensure_bool(visited, n._nid)
  if visited[n._nid] {
    return
  }
  visited[n._nid] = true
  nodes[n._nid] = Some(n)
  for def in n._inputs {
    match def {
      Some(nn) => Evaluator::collect_nodes(nodes, visited, nn)
      None => ()
    }
  }
  for use_ in n._outputs {
    match use_ {
      Some(nn) => Evaluator::collect_nodes(nodes, visited, nn)
      None => ()
    }
  }
}

///|
fn _push_map(m : Map[Int, Array[Node]], key : Int, value : Node) -> Unit {
  let ary = match m.get(key) {
    Some(a) => a
    None => {
      let a : Array[Node] = []
      m[key] = a
      a
    }
  }
  ary.push(value)
}

///|
fn Evaluator::build_schedule(nodes : Array[Node?]) -> Map[Int, Array[Node]] {
  let by_anchor : Map[Int, Array[Node]] = Map::new()
  for n in nodes {
    match n {
      None => ()
      Some(nn) => {
        if nn.is_cfg() || nn.kind == Phi {
          continue
        }
        let anchor = match nn.kind {
          Proj => nn.input_exn(0).cfg0()
          _ =>
            match nn.input(0) {
              Some(anchor) => anchor
              None => continue
            }
        }
        _push_map(by_anchor, anchor._nid, nn)
      }
    }
  }
  let ordered : Map[Int, Array[Node]] = Map::new()
  for key, group in by_anchor {
    ordered[key] = Evaluator::topo_sort(group)
  }
  ordered
}

///|
fn Evaluator::topo_sort(group : Array[Node]) -> Array[Node] {
  let in_group : Map[Int, Bool] = Map::new()
  for n in group {
    in_group[n._nid] = true
  }
  let state : Array[Int] = Array::make(Node::uid() + 1, 0)
  let order : Array[Node] = []
  fn visit(
    n : Node,
    in_group : Map[Int, Bool],
    state : Array[Int],
    order : Array[Node],
  ) -> Unit {
    let nid = n._nid
    if nid < state.length() {
      if state[nid] == 2 {
        return
      }
      if state[nid] == 1 {
        panic()
      }
      state[nid] = 1
    }
    for i = 0; i < n.n_ins(); i = i + 1 {
      match n.input(i) {
        Some(inp) if in_group.contains(inp._nid) =>
          visit(inp, in_group, state, order)
        _ => ()
      }
    }
    if nid < state.length() {
      state[nid] = 2
    }
    order.push(n)
  }

  for n in group {
    visit(n, in_group, state, order)
  }
  order
}

///|
fn Evaluator::ensure_values(self : Evaluator, nid : Int) -> Unit {
  while self.values.length() <= nid {
    self.values.push(None)
  }
}

///|
fn Evaluator::set_value(
  self : Evaluator,
  node : Node,
  value : EvalValue,
) -> Unit {
  self.ensure_values(node._nid)
  self.values[node._nid] = Some(value)
}

///|
fn Evaluator::get_value(self : Evaluator, node : Node) -> EvalValue {
  self.ensure_values(node._nid)
  match self.values[node._nid] {
    Some(v) => v
    None =>
      match node.kind {
        Constant => self.exec(node)
        _ => panic()
      }
  }
}

///|
fn Evaluator::default_value(t : Type) -> EvalValue {
  match t {
    Type::Int(_) => EvalValue::Int(0L)
    Type::Flt(_) => EvalValue::Float(0.0)
    Type::MemPtr(_, _) => EvalValue::Null
    _ => EvalValue::Null
  }
}

///|
fn Evaluator::off_to_idx(off : Int64, t : TypeStruct) -> Int64 {
  let off = off - Int64::from_int(t.ary_base())
  let scale = t.ary_scale()
  let mask = (1L << scale) - 1L
  if (off & mask) != 0L {
    panic()
  }
  off >> scale
}

///|
fn Evaluator::alloc(self : Evaluator, ptr : Type, size : Int64) -> Obj {
  let obj = match ptr {
    Type::MemPtr(obj, _) => obj
    _ => panic()
  }
  let struct_fields = match obj._fields {
    None => panic()
    Some(fs) => fs
  }
  let fields = if obj.is_ary() {
    let len = Evaluator::off_to_idx(size, obj)
    if len < 0L {
      panic()
    }
    let header_len = struct_fields.length() - 1
    let body_len = len.to_int()
    let out : Array[EvalValue] = Array::make(
      header_len + body_len,
      EvalValue::Null,
    )
    for i = 0; i < header_len; i = i + 1 {
      out[i] = Evaluator::default_value(struct_fields[i]._type)
    }
    let body_type = struct_fields[struct_fields.length() - 1]._type
    for i = 0; i < body_len; i = i + 1 {
      out[header_len + i] = Evaluator::default_value(body_type)
    }
    out
  } else {
    let out : Array[EvalValue] = Array::make(
      struct_fields.length(),
      EvalValue::Null,
    )
    for i = 0; i < struct_fields.length(); i = i + 1 {
      out[i] = Evaluator::default_value(struct_fields[i]._type)
    }
    out
  }
  let id = self.next_obj_id
  self.next_obj_id += 1
  { id, struct_: obj, fields }
}

///|
fn Evaluator::as_int(v : EvalValue) -> Int64 {
  match v {
    EvalValue::Int(i) => i
    _ => panic()
  }
}

///|
fn Evaluator::as_float(v : EvalValue) -> Double {
  match v {
    EvalValue::Float(f) => f
    _ => panic()
  }
}

///|
fn Evaluator::is_true(v : EvalValue) -> Bool {
  match v {
    EvalValue::Null => false
    EvalValue::Int(i) => i != 0L
    EvalValue::Float(f) => f != 0.0
    EvalValue::Obj(_) => true
    _ => true
  }
}

///|
fn Evaluator::eq(lhs : EvalValue, rhs : EvalValue) -> Bool {
  match (lhs, rhs) {
    (EvalValue::Null, EvalValue::Null) => true
    (EvalValue::Int(a), EvalValue::Int(b)) => a == b
    (EvalValue::Float(a), EvalValue::Float(b)) => a == b
    (EvalValue::Obj(a), EvalValue::Obj(b)) => a.id == b.id
    (EvalValue::Null, EvalValue::Obj(_))
    | (EvalValue::Obj(_), EvalValue::Null) => false
    _ => false
  }
}

///|
fn Evaluator::exec(self : Evaluator, node : Node) -> EvalValue {
  let value = match node.kind {
    Constant =>
      match node.compute() {
        Type::Int(i) => EvalValue::Int(i.value_exn())
        Type::Flt(f) => EvalValue::Float(f.value_exn())
        Type::Ctrl | Type::XCtrl => EvalValue::Mem(-1)
        MemPtr(_, _) => EvalValue::Null
        Mem(tm) => EvalValue::Mem(tm._alias)
        _ => panic()
      }
    Proj => {
      let base = self.get_value(node.input_exn(0))
      match base {
        EvalValue::Tuple(values) => values[node._proj_idx]
        _ => panic()
      }
    }
    Add =>
      EvalValue::Int(
        Evaluator::as_int(self.get_value(node.input_exn(1))) +
        Evaluator::as_int(self.get_value(node.input_exn(2))),
      )
    AddF =>
      EvalValue::Float(
        Evaluator::as_float(self.get_value(node.input_exn(1))) +
        Evaluator::as_float(self.get_value(node.input_exn(2))),
      )
    Sub =>
      EvalValue::Int(
        Evaluator::as_int(self.get_value(node.input_exn(1))) -
        Evaluator::as_int(self.get_value(node.input_exn(2))),
      )
    SubF =>
      EvalValue::Float(
        Evaluator::as_float(self.get_value(node.input_exn(1))) -
        Evaluator::as_float(self.get_value(node.input_exn(2))),
      )
    Mul =>
      EvalValue::Int(
        Evaluator::as_int(self.get_value(node.input_exn(1))) *
        Evaluator::as_int(self.get_value(node.input_exn(2))),
      )
    MulF =>
      EvalValue::Float(
        Evaluator::as_float(self.get_value(node.input_exn(1))) *
        Evaluator::as_float(self.get_value(node.input_exn(2))),
      )
    Div => {
      let rhs = Evaluator::as_int(self.get_value(node.input_exn(2)))
      if rhs == 0L {
        EvalValue::Int(0L)
      } else {
        EvalValue::Int(
          Evaluator::as_int(self.get_value(node.input_exn(1))) / rhs,
        )
      }
    }
    DivF =>
      EvalValue::Float(
        Evaluator::as_float(self.get_value(node.input_exn(1))) /
        Evaluator::as_float(self.get_value(node.input_exn(2))),
      )
    Minus =>
      EvalValue::Int(-Evaluator::as_int(self.get_value(node.input_exn(1))))
    MinusF =>
      EvalValue::Float(-Evaluator::as_float(self.get_value(node.input_exn(1))))
    Shl => {
      let lhs = Evaluator::as_int(self.get_value(node.input_exn(1)))
      let rhs = Evaluator::as_int(self.get_value(node.input_exn(2)))
      EvalValue::Int(lhs << rhs.land(63L).to_int())
    }
    Shr => {
      let lhs = Evaluator::as_int(self.get_value(node.input_exn(1)))
      let rhs = Evaluator::as_int(self.get_value(node.input_exn(2)))
      EvalValue::Int(
        (lhs.reinterpret_as_uint64() >> rhs.land(63L).to_int()).reinterpret_as_int64(),
      )
    }
    Sar => {
      let lhs = Evaluator::as_int(self.get_value(node.input_exn(1)))
      let rhs = Evaluator::as_int(self.get_value(node.input_exn(2)))
      EvalValue::Int(lhs >> rhs.land(63L).to_int())
    }
    And =>
      EvalValue::Int(
        Evaluator::as_int(self.get_value(node.input_exn(1))) &
        Evaluator::as_int(self.get_value(node.input_exn(2))),
      )
    Or =>
      EvalValue::Int(
        Evaluator::as_int(self.get_value(node.input_exn(1))) |
        Evaluator::as_int(self.get_value(node.input_exn(2))),
      )
    Xor =>
      EvalValue::Int(
        Evaluator::as_int(self.get_value(node.input_exn(1))) ^
        Evaluator::as_int(self.get_value(node.input_exn(2))),
      )
    Not =>
      EvalValue::Int(
        if Evaluator::is_true(self.get_value(node.input_exn(1))) {
          0L
        } else {
          1L
        },
      )
    BoolEq =>
      EvalValue::Int(
        if Evaluator::eq(
            self.get_value(node.input_exn(1)),
            self.get_value(node.input_exn(2)),
          ) {
          1L
        } else {
          0L
        },
      )
    BoolEqF =>
      EvalValue::Int(
        if Evaluator::as_float(self.get_value(node.input_exn(1))) ==
          Evaluator::as_float(self.get_value(node.input_exn(2))) {
          1L
        } else {
          0L
        },
      )
    BoolLt =>
      EvalValue::Int(
        if Evaluator::as_int(self.get_value(node.input_exn(1))) <
          Evaluator::as_int(self.get_value(node.input_exn(2))) {
          1L
        } else {
          0L
        },
      )
    BoolLtF =>
      EvalValue::Int(
        if Evaluator::as_float(self.get_value(node.input_exn(1))) <
          Evaluator::as_float(self.get_value(node.input_exn(2))) {
          1L
        } else {
          0L
        },
      )
    BoolLe =>
      EvalValue::Int(
        if Evaluator::as_int(self.get_value(node.input_exn(1))) <=
          Evaluator::as_int(self.get_value(node.input_exn(2))) {
          1L
        } else {
          0L
        },
      )
    BoolLeF =>
      EvalValue::Int(
        if Evaluator::as_float(self.get_value(node.input_exn(1))) <=
          Evaluator::as_float(self.get_value(node.input_exn(2))) {
          1L
        } else {
          0L
        },
      )
    ToFloat =>
      EvalValue::Float(
        Evaluator::as_int(self.get_value(node.input_exn(1))).to_double(),
      )
    RoundF32 =>
      EvalValue::Float(
        Float::from_double(
          Evaluator::as_float(self.get_value(node.input_exn(1))),
        ).to_double(),
      )
    Cast => self.get_value(node.input_exn(1))
    ReadOnly => self.get_value(node.input_exn(1))
    New => {
      let ptr = match node._con {
        Some(ptr) => ptr
        None => panic()
      }
      let size = Evaluator::as_int(self.get_value(node.input_exn(1)))
      let obj = self.alloc(ptr, size)
      let struct_fields = match obj.struct_._fields {
        Some(fs) => fs
        None => panic()
      }
      let len = struct_fields.length()
      if obj.struct_.is_ary() {
        // Only need to set the array length; body already default-initialized.
        obj.fields[0] = self.get_value(node.input_exn(2 + len))
      } else {
        for i = 0; i < len; i = i + 1 {
          obj.fields[i] = self.get_value(node.input_exn(2 + len + i))
        }
      }
      let vals : Array[EvalValue] = Array::make(
        struct_fields.length() + 2,
        EvalValue::Mem(-1),
      )
      vals[0] = EvalValue::Mem(-1)
      vals[1] = EvalValue::Obj(obj)
      for i = 0; i < struct_fields.length(); i = i + 1 {
        vals[i + 2] = EvalValue::Mem(struct_fields[i]._alias)
      }
      EvalValue::Tuple(vals)
    }
    Load => {
      ignore(self.get_value(node.input_exn(1)))
      let ptr = self.get_value(node.input_exn(2))
      let obj = match ptr {
        EvalValue::Obj(o) => o
        _ => panic()
      }
      let idx = obj.struct_.find(node._memop_name)
      if idx < 0 {
        panic()
      }
      let struct_fields = match obj.struct_._fields {
        Some(fs) => fs
        None => panic()
      }
      if obj.struct_.is_ary() && idx == struct_fields.length() - 1 {
        let off = Evaluator::as_int(self.get_value(node.input_exn(3)))
        let i = Evaluator::off_to_idx(off, obj.struct_).to_int()
        let header_len = struct_fields.length() - 1
        let len = obj.fields.length() - header_len
        if i < 0 || i >= len {
          panic()
        }
        obj.fields[header_len + i]
      } else {
        obj.fields[idx]
      }
    }
    Store => {
      ignore(self.get_value(node.input_exn(1)))
      let ptr = self.get_value(node.input_exn(2))
      let obj = match ptr {
        EvalValue::Obj(o) => o
        _ => panic()
      }
      let idx = obj.struct_.find(node._memop_name)
      if idx < 0 {
        panic()
      }
      let struct_fields = match obj.struct_._fields {
        Some(fs) => fs
        None => panic()
      }
      if obj.struct_.is_ary() && idx == struct_fields.length() - 1 {
        let off = Evaluator::as_int(self.get_value(node.input_exn(3)))
        let i = Evaluator::off_to_idx(off, obj.struct_).to_int()
        let header_len = struct_fields.length() - 1
        let len = obj.fields.length() - header_len
        if i < 0 || i >= len {
          panic()
        }
        obj.fields[header_len + i] = self.get_value(node.input_exn(4))
      } else {
        obj.fields[idx] = self.get_value(node.input_exn(4))
      }
      EvalValue::Mem(node._memop_alias)
    }
    CProj => {
      let base = self.get_value(node.input_exn(0))
      match base {
        EvalValue::Tuple(values) => values[node._proj_idx]
        _ => panic()
      }
    }
    _ => panic()
  }
  self.set_value(node, value)
  value
}

///|
fn Evaluator::exec_anchor(self : Evaluator, anchor : Node) -> Unit {
  match self.schedule.get(anchor._nid) {
    None => ()
    Some(nodes) =>
      for n in nodes {
        ignore(self.exec(n))
      }
  }
}

///|
fn Evaluator::find_control(control : Node) -> Node? {
  for user in control._outputs {
    match user {
      Some(n) if n.is_cfg() => return Some(n)
      _ => ()
    }
  }
  None
}

///|
fn Evaluator::find_projection(node : Node, idx : Int) -> Node? {
  for user in node._outputs {
    match user {
      Some(proj) if (proj.kind == Proj || proj.kind == CProj) &&
        proj._proj_idx == idx => return Some(proj)
      _ => ()
    }
  }
  None
}

///|
fn Evaluator::find_input_idx(region : Node, prev : Node) -> Int {
  for i, input in region._inputs {
    match input {
      Some(n) if n == prev => return i
      _ => ()
    }
  }
  -1
}

///|
fn Evaluator::latch_phis(self : Evaluator, region : Node, prev : Node) -> Unit {
  let idx = Evaluator::find_input_idx(region, prev)
  if idx <= 0 {
    panic()
  }
  let phis : Array[Node] = []
  let values : Array[EvalValue] = []
  for user in region._outputs {
    match user {
      Some(phi) if phi.kind == Phi => {
        let v = self.get_value(phi.input_exn(idx))
        phis.push(phi)
        values.push(v)
      }
      _ => ()
    }
  }
  for i = 0; i < phis.length(); i = i + 1 {
    self.set_value(phis[i], values[i])
  }
}

///|
fn Evaluator::run(
  self : Evaluator,
  start : Node,
  parameter : Int64,
  loops : Int,
) -> EvalStatus {
  let start_ty = start.compute()
  let start_tuple = match start_ty {
    Tuple(types) => {
      let vals : Array[EvalValue] = Array::make(
        types.length(),
        EvalValue::Mem(-1),
      )
      if types.length() > 0 {
        vals[0] = EvalValue::Mem(-1)
      }
      if types.length() > 1 {
        vals[1] = EvalValue::Mem(-1)
      }
      if types.length() > 2 {
        vals[2] = EvalValue::Int(parameter)
      }
      vals
    }
    _ => panic()
  }
  self.set_value(start, EvalValue::Tuple(start_tuple))
  self.exec_anchor(start)
  let mut loops = loops
  let mut control = Evaluator::find_projection(start, 0)
  let mut prev = start
  while control is Some(ctrl_node) {
    let next = match ctrl_node.kind {
      Region | Loop => {
        if ctrl_node.kind == Loop && ctrl_node.input_exn(1) != prev {
          if loops <= 0 {
            return Timeout
          }
          loops -= 1
        }
        self.latch_phis(ctrl_node, prev)
        self.exec_anchor(ctrl_node)
        Evaluator::find_control(ctrl_node)
      }
      If | Never => {
        self.exec_anchor(ctrl_node)
        let pred = self.get_value(ctrl_node.input_exn(1))
        Evaluator::find_projection(
          ctrl_node,
          if Evaluator::is_true(pred) {
            0
          } else {
            1
          },
        )
      }
      Return => {
        self.exec_anchor(ctrl_node)
        return Value(self.get_value(ctrl_node.input_exn(1)))
      }
      CProj => {
        self.exec_anchor(ctrl_node)
        Evaluator::find_control(ctrl_node)
      }
      XCtrl => None
      _ => panic()
    }
    prev = ctrl_node
    control = next
  }
  Fallthrough
}

///|
pub fn Evaluator::evaluate(
  graph : Node,
  parameter? : Int64 = 0L,
  loops? : Int = 1000,
) -> EvalValue {
  match Evaluator::evaluate_with_result(graph, parameter~, loops~) {
    Value(v) => v
    Timeout => panic()
    Fallthrough => EvalValue::Int(0L)
  }
}

///|
pub fn Evaluator::evaluate_with_result(
  graph : Node,
  parameter? : Int64 = 0L,
  loops? : Int = 1000,
) -> EvalStatus {
  let eval = Evaluator::new(graph)
  if eval.nodes.length() == 0 {
    return Timeout
  }
  let visited : Array[Bool] = []
  match Evaluator::find_start(visited, Some(graph)) {
    None => Timeout
    Some(start) => eval.run(start, parameter, loops)
  }
}
