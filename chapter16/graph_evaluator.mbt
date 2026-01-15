///|
pub enum EvalResultType {
  Value
  Fallthrough
  Timeout
} derive(Eq, Show)

///|
pub struct EvalResult {
  typ : EvalResultType
  value : Int64
} derive(Eq, Show)

///|
pub struct GraphEvaluator {
  mut _cache_values : Array[Int64?]
}

///|
fn GraphEvaluator::new() -> GraphEvaluator {
  { _cache_values: [] }
}

///|
fn GraphEvaluator::_ensure_cache(self : GraphEvaluator, nid : Int) -> Unit {
  while self._cache_values.length() <= nid {
    self._cache_values.push(None)
  }
}

///|
fn GraphEvaluator::_get_cache(self : GraphEvaluator, node : Node) -> Int64? {
  self._ensure_cache(node._nid)
  self._cache_values[node._nid]
}

///|
fn GraphEvaluator::_set_cache(
  self : GraphEvaluator,
  node : Node,
  value : Int64,
) -> Unit {
  self._ensure_cache(node._nid)
  self._cache_values[node._nid] = Some(value)
}

///|
fn GraphEvaluator::_find_start(visited : Array[Bool], node : Node?) -> Node? {
  match node {
    None => None
    Some(node) =>
      if node.kind == Start {
        Some(node)
      } else {
        while visited.length() <= node._nid {
          visited.push(false)
        }
        if visited[node._nid] {
          return None
        }
        visited[node._nid] = true
        for def in node._inputs {
          match GraphEvaluator::_find_start(visited, def) {
            Some(start) => return Some(start)
            None => ()
          }
        }
        for user in node._outputs {
          match GraphEvaluator::_find_start(visited, user) {
            Some(start) => return Some(start)
            None => ()
          }
        }
        None
      }
  }
}

///|
fn GraphEvaluator::_find_control(control : Node) -> Node? {
  for user in control._outputs {
    match user {
      Some(n) if n.is_cfg() => return Some(n)
      _ => ()
    }
  }
  None
}

///|
fn GraphEvaluator::_find_projection(node : Node, idx : Int) -> Node? {
  for user in node._outputs {
    match user {
      Some(proj) if (proj.kind == Proj || proj.kind == CProj) && proj._proj_idx == idx =>
        return Some(proj)
      _ => ()
    }
  }
  None
}

///|
fn GraphEvaluator::_find_input_idx(region : Node, prev : Node) -> Int {
  for i, input in region._inputs {
    match input {
      Some(n) if n == prev => return i
      _ => ()
    }
  }
  -1
}

///|
fn GraphEvaluator::_div(self : GraphEvaluator, div : Node) -> Int64 {
  let rhs = self._get_value(div.input_exn(2))
  if rhs == 0L {
    0L
  } else {
    self._get_value(div.input_exn(1)) / rhs
  }
}

///|
fn GraphEvaluator::_get_value(self : GraphEvaluator, node : Node) -> Int64 {
  match self._get_cache(node) {
    Some(v) => return v
    None => ()
  }
  match node.kind {
    Constant =>
      match node.compute() {
        Type::Int(i) => i.value_exn()
        _ => panic()
      }
    Add =>
      self._get_value(node.input_exn(1)) + self._get_value(node.input_exn(2))
    BoolEq =>
      if self._get_value(node.input_exn(1)) ==
        self._get_value(node.input_exn(2)) {
        1L
      } else {
        0L
      }
    BoolLe =>
      if self._get_value(node.input_exn(1)) <=
        self._get_value(node.input_exn(2)) {
        1L
      } else {
        0L
      }
    BoolLt =>
      if self._get_value(node.input_exn(1)) < self._get_value(node.input_exn(2)) {
        1L
      } else {
        0L
      }
    Div => self._div(node)
    Minus => -self._get_value(node.input_exn(1))
    Mul =>
      self._get_value(node.input_exn(1)) * self._get_value(node.input_exn(2))
    Not => if self._get_value(node.input_exn(1)) == 0L { 1L } else { 0L }
    Sub =>
      self._get_value(node.input_exn(1)) - self._get_value(node.input_exn(2))
    _ => panic()
  }
}

///|
fn GraphEvaluator::_latch_phis(
  self : GraphEvaluator,
  region : Node,
  prev : Node,
) -> Unit {
  let idx = GraphEvaluator::_find_input_idx(region, prev)
  if idx <= 0 {
    panic()
  }
  for user in region._outputs {
    match user {
      Some(phi) if phi.kind == Phi => {
        let value = self._get_value(phi.input_exn(idx))
        self._set_cache(phi, value)
      }
      _ => ()
    }
  }
}

///|
fn GraphEvaluator::_latch_loop_phis(
  self : GraphEvaluator,
  region : Node,
  prev : Node,
) -> Unit {
  let idx = GraphEvaluator::_find_input_idx(region, prev)
  if idx <= 0 {
    panic()
  }
  let values : Array[Int64] = []
  for user in region._outputs {
    match user {
      Some(phi) if phi.kind == Phi =>
        values.push(self._get_value(phi.input_exn(idx)))
      _ => ()
    }
  }
  let mut i = 0
  for user in region._outputs {
    match user {
      Some(phi) if phi.kind == Phi => {
        self._set_cache(phi, values[i])
        i += 1
      }
      _ => ()
    }
  }
}

///|
fn GraphEvaluator::_evaluate(
  self : GraphEvaluator,
  start : Node,
  parameter : Int64,
  loops : Int,
) -> EvalResult {
  let mut loops = loops
  match GraphEvaluator::_find_projection(start, 2) {
    Some(parameter1) => self._set_cache(parameter1, parameter)
    None => ()
  }
  let mut control = GraphEvaluator::_find_projection(start, 0)
  let mut prev = start
  while control is Some(ctrl_node) {
    let next = match ctrl_node.kind {
      Region | Loop => {
        if ctrl_node.kind == Loop && ctrl_node.input_exn(1) != prev {
          if loops <= 0 {
            return { typ: Timeout, value: 0L }
          }
          loops -= 1
          self._latch_loop_phis(ctrl_node, prev)
        } else {
          self._latch_phis(ctrl_node, prev)
        }
        GraphEvaluator::_find_control(ctrl_node)
      }
      If =>
        GraphEvaluator::_find_projection(
          ctrl_node,
          if self._get_value(ctrl_node.input_exn(1)) != 0L {
            0
          } else {
            1
          },
        )
      Return =>
        return { typ: Value, value: self._get_value(ctrl_node.input_exn(1)) }
      CProj | Proj => GraphEvaluator::_find_control(ctrl_node)
      XCtrl => None
      _ => panic()
    }
    prev = ctrl_node
    control = next
  }
  { typ: Fallthrough, value: 0L }
}

///|
pub fn GraphEvaluator::evaluate(graph : Node, parameter? : Int64 = 0L) -> Int64 {
  GraphEvaluator::evaluate_with_loops(graph, parameter~)
}

///|
pub fn GraphEvaluator::evaluate_with_loops(
  graph : Node,
  parameter? : Int64 = 0L,
  loops? : Int = 1000,
) -> Int64 {
  let res = GraphEvaluator::evaluate_with_result(graph, parameter~, loops~)
  match res.typ {
    Timeout => panic()
    _ => res.value
  }
}

///|
pub fn GraphEvaluator::evaluate_with_result(
  graph : Node,
  parameter? : Int64 = 0L,
  loops? : Int = 1000,
) -> EvalResult {
  let visited : Array[Bool] = []
  match GraphEvaluator::_find_start(visited, Some(graph)) {
    None => { typ: Timeout, value: 0L }
    Some(start) => GraphEvaluator::new()._evaluate(start, parameter, loops)
  }
}
