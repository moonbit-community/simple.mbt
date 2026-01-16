///|
pub struct ListScheduler {}

///|
priv struct XSched {
  _n : Node
  mut _bcnt : Int
  mut _rcnt : Int
  mut _ruse : Bool
  mut _rdef : Bool
  mut _single : Bool
}

///|
fn _ensure_bool_sched(visited : Array[Bool], nid : Int) -> Unit {
  while visited.length() <= nid {
    visited.push(false)
  }
}

///|
fn _type_has_mem(t : Type) -> Bool {
  match t {
    Mem(_) => true
    Tuple(Some(ts)) => {
      for tt in ts {
        if _type_has_mem(tt) {
          return true
        }
      }
      false
    }
    _ => false
  }
}

///|
fn _node_is_mem(n : Node) -> Bool {
  _type_has_mem(n.ty())
}

///|
fn ListScheduler::rpo_cfg(
  n : Node,
  visit : Array[Bool],
  rpo : Array[Node],
) -> Unit {
  if !n.is_cfg() {
    return
  }
  _ensure_bool_sched(visit, n._nid)
  if visit[n._nid] {
    return
  }
  visit[n._nid] = true
  for use_ in n._outputs {
    match use_ {
      Some(cfg) => ListScheduler::rpo_cfg(cfg, visit, rpo)
      None => ()
    }
  }
  rpo.push(n)
}

///|
fn ListScheduler::cfg_blocks(start : Node) -> Array[Node] {
  let rpo : Array[Node] = []
  let visit : Array[Bool] = []
  ListScheduler::rpo_cfg(start, visit, rpo)
  let blocks : Array[Node] = []
  for i = rpo.length() - 1; i >= 0; i = i - 1 {
    blocks.push(rpo[i])
  }
  blocks
}

///|
fn ListScheduler::xsched_get(
  xs : Array[Ref[XSched]?],
  n : Node?,
) -> Ref[XSched]? {
  match n {
    None => None
    Some(node) => {
      let target = if node.kind == Proj {
        node.input_exn(0)
      } else {
        node
      }
      if target._nid >= 0 && target._nid < xs.length() {
        xs[target._nid]
      } else {
        None
      }
    }
  }
}

///|
fn ListScheduler::xsched_alloc(
  bb : Node,
  n : Node,
  xs : Array[Ref[XSched]?],
) -> Unit {
  let sched = Ref::{
    val: {
      _n: n,
      _bcnt: 0,
      _rcnt: 0,
      _ruse: false,
      _rdef: false,
      _single: false,
    },
  }
  if n.kind != Phi {
    for def in n._inputs {
      match def {
        Some(d) if d != bb => {
          match d.input(0) {
            Some(_) =>
              if d.cfg0() == bb {
                sched.val._bcnt = sched.val._bcnt + 1
              } else if !_node_is_mem(d) {
                sched.val._ruse = true
              }
            None => ()
          }
        }
        _ => ()
      }
    }
  }
  for use_ in n._outputs {
    match use_ {
      Some(use_node) =>
        match use_node.input(0) {
          Some(_) => if use_node.cfg0() != bb { sched.val._rdef = true }
          None => ()
        }
      _ => ()
    }
  }
  xs[n._nid] = Some(sched)
}

///|
fn ListScheduler::ready_up(xs : Array[Ref[XSched]?], use_ : Node) -> Unit {
  match ListScheduler::xsched_get(xs, Some(use_)) {
    Some(x) =>
      if use_.kind != Phi && x.val._bcnt > 0 {
        x.val._bcnt = x.val._bcnt - 1
        x.val._rcnt = x.val._rcnt + 1
      }
    None => ()
  }
}

///|
fn ListScheduler::is_ready(xs : Array[Ref[XSched]?], n : Node) -> Bool {
  match ListScheduler::xsched_get(xs, Some(n)) {
    None => false
    Some(x) =>
      if x.val._bcnt > 0 || x.val._rcnt > 0 {
        false
      } else {
        for use_ in x.val._n._outputs {
          match use_ {
            Some(use_) => ListScheduler::ready_up(xs, use_)
            None => ()
          }
        }
        true
      }
  }
}

///|
fn ListScheduler::dec_is_ready(xs : Array[Ref[XSched]?], n : Node) -> Bool {
  match ListScheduler::xsched_get(xs, Some(n)) {
    None => false
    Some(x) => {
      if x.val._rcnt <= 0 {
        false
      } else {
        x.val._rcnt = x.val._rcnt - 1
        ListScheduler::is_ready(xs, n)
      }
    }
  }
}

///|
fn ListScheduler::ready(
  bb : Node,
  use_ : Node,
  ready : Int,
  outputs : Array[Node],
  xs : Array[Ref[XSched]?],
) -> Int {
  if use_.kind != Phi {
    match use_.input(0) {
      Some(ctrl) if ctrl._nid == bb._nid =>
        if ListScheduler::dec_is_ready(xs, use_) {
          outputs[ready] = use_
          return ready + 1
        }
      _ => ()
    }
  }
  ready
}

///|
fn ListScheduler::swap(outputs : Array[Node], i : Int, j : Int) -> Unit {
  if i == j {
    return
  }
  let tmp = outputs[i]
  outputs[i] = outputs[j]
  outputs[j] = tmp
}

///|
fn ListScheduler::best(
  outputs : Array[Node],
  sched : Int,
  ready : Int,
  trace : Bool,
  xs : Array[Ref[XSched]?],
) -> Int {
  let mut pick = sched
  let mut score = ListScheduler::score(outputs[pick], xs)
  if trace {
    println("\{score} N\{outputs[pick]._nid} \{outputs[pick].print()}")
  }
  for i = sched + 1; i < ready; i = i + 1 {
    let n = outputs[i]
    let nscore = ListScheduler::score(n, xs)
    if trace {
      println("\{nscore} N\{n._nid} \{n.print()}")
    }
    if nscore > score {
      score = nscore
      pick = i
    }
  }
  pick
}

///|
fn ListScheduler::score(n : Node, xs : Array[Ref[XSched]?]) -> Int {
  if n.kind == Proj || n.kind == CProj {
    return 1001
  }
  if n.kind == Phi {
    return 1000
  }
  if n.is_cfg() {
    return 1
  }
  let mut score = 500
  if n.kind != Mach {
    return score
  }
  match ListScheduler::xsched_get(xs, Some(n)) {
    Some(x) if x.val._rdef => score = 200
    _ => ()
  }
  score
}

///|
fn ListScheduler::schedule_block(bb : Node, trace : Bool) -> Unit {
  let outputs : Array[Node] = []
  for out in bb._outputs {
    match out {
      Some(n) => outputs.push(n)
      None => ()
    }
  }
  let len = outputs.length()
  if len == 0 {
    return
  }
  let xs : Array[Ref[XSched]?] = Array::make(Node::uid() + 1, None)
  for n in outputs {
    ListScheduler::xsched_alloc(bb, n, xs)
  }

  let mut ready = 0
  for i = 0; i < len; i = i + 1 {
    if ListScheduler::is_ready(xs, outputs[i]) {
      ListScheduler::swap(outputs, ready, i)
      ready = ready + 1
    }
  }

  let mut sched = 0
  while sched < len {
    if sched >= ready {
      break
    }
    let pick = ListScheduler::best(outputs, sched, ready, trace, xs)
    let best = outputs[pick]
    ListScheduler::swap(outputs, pick, sched)
    sched = sched + 1
    for use_ in best._outputs {
      match use_ {
        Some(use_node) if use_node.kind == Proj =>
          for useuse in use_node._outputs {
            match useuse {
              Some(useuse) => {
                ready = ListScheduler::ready(bb, useuse, ready, outputs, xs)
              }
              None => ()
            }
          }
        Some(use_node) => {
          ready = ListScheduler::ready(bb, use_node, ready, outputs, xs)
        }
        None => ()
      }
    }
  }

  let new_outs : Array[Node?] = []
  for n in outputs {
    new_outs.push(Some(n))
  }
  bb._outputs = new_outs
}

///|
pub fn ListScheduler::sched(code : CodeGen) -> Unit {
  let blocks = ListScheduler::cfg_blocks(code._start)
  for bb in blocks {
    if bb.block_head() {
      ListScheduler::schedule_block(bb, false)
    }
  }
}

///|
fn ListScheduler::block_nodes(bb : Node) -> Array[Node] {
  let group : Array[Node] = []
  for out in bb._outputs {
    match out {
      Some(n) if n.cfg0() == bb => group.push(n)
      _ => ()
    }
  }
  if local_scheduled.val {
    group
  } else {
    Evaluator::topo_sort(group)
  }
}
