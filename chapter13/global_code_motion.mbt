///|
pub struct GlobalCodeMotion {}

///|
pub fn GlobalCodeMotion::build_cfg(stop : Node) -> Unit {
  GlobalCodeMotion::sched_early()
  scheduled.val = true
  GlobalCodeMotion::sched_late(stop)
}

///|
fn _ensure_visited(visit : Array[Bool], nid : Int) -> Unit {
  while visit.length() <= nid {
    visit.push(false)
  }
}

///|
fn _unreach_add(unreach : Map[Int, Node], n : Node) -> Unit {
  unreach[n._nid] = n
}

///|
fn _unreach_remove(unreach : Map[Int, Node], n : Node) -> Unit {
  ignore(unreach.remove(n._nid))
}

///|
fn GlobalCodeMotion::walk_unreach(
  n : Node,
  visit : Array[Bool],
  unreach : Map[Int, Node],
) -> Unit {
  _ensure_visited(visit, n._nid)
  if visit[n._nid] {
    return
  }
  visit[n._nid] = true
  GlobalCodeMotion::walk_unreach0(n, visit, unreach)
  _unreach_remove(unreach, n)
}

///|
fn GlobalCodeMotion::walk_unreach0(
  n : Node,
  visit : Array[Bool],
  unreach : Map[Int, Node],
) -> Unit {
  match n.kind {
    Start => ()
    Region | Loop => {
      for i = 1; i < n.n_ins(); i = i + 1 {
        match n.input(i) {
          Some(cfg) => GlobalCodeMotion::walk_unreach(cfg, visit, unreach)
          None => ()
        }
      }
    }
    If | Never => {
      for use_ in n._outputs {
        match use_ {
          Some(proj) if proj.kind == CProj && proj._loop_depth == 0 =>
            _unreach_add(unreach, proj)
          _ => ()
        }
      }
      match n.input(0) {
        Some(cfg) => GlobalCodeMotion::walk_unreach(cfg, visit, unreach)
        None => ()
      }
    }
    _ =>
      match n.input(0) {
        Some(cfg) => GlobalCodeMotion::walk_unreach(cfg, visit, unreach)
        None => ()
      }
  }
}

///|
pub fn GlobalCodeMotion::fix_loops(stop : Node) -> Unit {
  let visit : Array[Bool] = []
  let unreach : Map[Int, Node] = Map::new()
  _unreach_add(unreach, start.val)
  for input in stop._inputs {
    match input {
      Some(ret) => GlobalCodeMotion::walk_unreach(ret, visit, unreach)
      None => ()
    }
  }
  if unreach.length() == 0 {
    return
  }

  // Forwards walk from unreachable, looking for loops with no exit test.
  let visit2 : Array[Bool] = []
  for _nid, cfg in unreach {
    GlobalCodeMotion::walk_infinite(cfg, visit2, stop)
  }

  // Backwards walk again to confirm reachability from Stop.
  visit.clear()
  unreach.clear()
  for input in stop._inputs {
    match input {
      Some(ret) => GlobalCodeMotion::walk_unreach(ret, visit, unreach)
      None => ()
    }
  }
}

///|
fn GlobalCodeMotion::walk_infinite(
  n : Node,
  visit : Array[Bool],
  stop : Node,
) -> Unit {
  _ensure_visited(visit, n._nid)
  if visit[n._nid] {
    return
  }
  visit[n._nid] = true
  if n.kind == Loop {
    n.force_exit(stop)
  }
  for use_ in n._outputs {
    match use_ {
      Some(cfg) if cfg.is_cfg() => GlobalCodeMotion::walk_infinite(cfg, visit, stop)
      _ => ()
    }
  }
}

///|
fn GlobalCodeMotion::sched_early() -> Unit {
  let rpo : Array[Node] = []
  let visit : Array[Bool] = []
  GlobalCodeMotion::rpo_cfg(start.val, visit, rpo)
  for j = rpo.length() - 1; j >= 0; j = j - 1 {
    let cfg = rpo[j]
    ignore(cfg.loop_depth())
    for n in cfg._inputs {
      match n {
        Some(nn) => GlobalCodeMotion::sched_early0(nn, visit)
        None => ()
      }
    }
    match cfg.kind {
      Region | Loop => {
        let len = cfg.n_outs()
        for i = 0; i < len; i = i + 1 {
          match cfg._outputs[i] {
            Some(phi) if phi.kind == Phi => GlobalCodeMotion::sched_early0(phi, visit)
            _ => ()
          }
        }
      }
      _ => ()
    }
  }
}

///|
fn GlobalCodeMotion::rpo_cfg(
  n : Node,
  visit : Array[Bool],
  rpo : Array[Node],
) -> Unit {
  if !n.is_cfg() {
    return
  }
  _ensure_visited(visit, n._nid)
  if visit[n._nid] {
    return
  }
  visit[n._nid] = true
  for use_ in n._outputs {
    match use_ {
      Some(use_) => GlobalCodeMotion::rpo_cfg(use_, visit, rpo)
      None => ()
    }
  }
  rpo.push(n)
}

///|
fn GlobalCodeMotion::sched_early0(n : Node, visit : Array[Bool]) -> Unit {
  _ensure_visited(visit, n._nid)
  if visit[n._nid] {
    return
  }
  visit[n._nid] = true
  for def in n._inputs {
    match def {
      Some(d) if !d.is_pinned() => GlobalCodeMotion::sched_early0(d, visit)
      _ => ()
    }
  }
  if !n.is_pinned() {
    let mut early = start.val
    for i = 1; i < n.n_ins(); i = i + 1 {
      match n.input(i) {
        Some(inp) => {
          let cfg = inp.cfg0()
          if cfg.idepth() > early.idepth() {
            early = cfg
          }
        }
        None => ()
      }
    }
    ignore(n.set_def(0, Some(early)))
  }
}

///|
fn _is_mem_type(t : Type) -> Bool {
  match t {
    Mem(_) => true
    _ => false
  }
}

///|
fn GlobalCodeMotion::sched_late(stop : Node) -> Unit {
  let len = Node::uid() + 1
  let late : Array[Node?] = Array::make(len, None)
  let ns : Array[Node?] = Array::make(len, None)
  GlobalCodeMotion::breadth(stop, ns, late)
  for i = 0; i < late.length(); i = i + 1 {
    match (ns[i], late[i]) {
      (Some(n), Some(cfg)) => ignore(n.set_def(0, Some(cfg)))
      _ => ()
    }
  }
}

///|
fn GlobalCodeMotion::breadth(
  stop : Node,
  ns : Array[Node?],
  late : Array[Node?],
) -> Unit {
  let work : Array[Node] = [stop]
  while work.length() > 0 {
    let n = work.remove(work.length() - 1)
    if n._nid >= late.length() || late[n._nid] is Some(_) {
      continue
    }
    if n.is_cfg() {
      late[n._nid] = Some(if n.block_head() { n } else { n.cfg0() })
    } else if n.kind == Phi {
      late[n._nid] = Some(n.input_exn(0))
    } else if n.is_pinned() {
      late[n._nid] = Some(n.cfg0())
    } else {
      // All uses done?
      let mut ready = true
      for use_ in n._outputs {
        match use_ {
          Some(use_) if late[use_._nid] is None => {
            ready = false
            break
          }
          _ => ()
        }
      }
      if ready && n.kind == Load {
        // Loads need their memory inputs' uses also done
        let mem = n.input_exn(1)
        for memuse in mem._outputs {
          match memuse {
            Some(memuse) if _is_mem_type(memuse.ty()) && late[memuse._nid] is None => {
              ready = false
              break
            }
            _ => ()
          }
        }
      }
      if !ready {
        continue
      }
      GlobalCodeMotion::do_sched_late(n, ns, late)
    }

    // Walk all inputs and put on worklist, as their last-use might now be done
    for def in n._inputs {
      match def {
        Some(def) if late[def._nid] is None => {
          work.push(def)
          // if the def has a load use, maybe the load can fire
          for ld in def._outputs {
            match ld {
              Some(ld) if ld.kind == Load && late[ld._nid] is None => work.push(ld)
              _ => ()
            }
          }
        }
        _ => ()
      }
    }
  }
}

///|
fn GlobalCodeMotion::do_sched_late(
  n : Node,
  ns : Array[Node?],
  late : Array[Node?],
) -> Unit {
  let early = match n.input(0) {
    Some(cfg) => cfg
    None => start.val
  }
  let mut lca : Node? = None
  for use_ in n._outputs {
    match use_ {
      Some(use_) => lca = Some(GlobalCodeMotion::use_block(n, use_, late).idom_lca(lca))
      None => ()
    }
  }
  let mut lca0 = match lca {
    Some(cfg) => cfg
    None => early
  }

  if n.kind == Load {
    lca0 = GlobalCodeMotion::find_anti_dep(lca0, n, early, late)
  }

  let mut best = lca0
  let stop_at = early.idom()
  let mut cur = best.idom()
  while cur is Some(c) {
    if stop_at is Some(stop) && c == stop {
      break
    }
    if GlobalCodeMotion::better(c, best) {
      best = c
    }
    cur = c.idom()
  }
  ns[n._nid] = Some(n)
  late[n._nid] = Some(best)
}

///|
fn GlobalCodeMotion::use_block(n : Node, user : Node, late : Array[Node?]) -> Node {
  if user.kind != Phi {
    match late[user._nid] {
      Some(cfg) => cfg
      None => panic()
    }
  } else {
    let phi = user
    let region = phi.input_exn(0)
    let mut found : Node? = None
    for i = 1; i < phi.n_ins(); i = i + 1 {
      if phi.input(i) == Some(n) {
        match found {
          None => found = region.input(i)
          Some(_) => ()
        }
      }
    }
    match found {
      Some(cfg) => cfg
      None => panic()
    }
  }
}

///|
fn GlobalCodeMotion::better(lca : Node, best : Node) -> Bool {
  lca.loop_depth() < best.loop_depth() ||
  (lca.idepth() > best.idepth() || best.kind == If || best.kind == Never)
}

///|
///|
fn _has_input(n : Node, x : Node) -> Bool {
  for input in n._inputs {
    match input {
      Some(in_) if in_ == x => return true
      _ => ()
    }
  }
  false
}

///|
fn GlobalCodeMotion::find_anti_dep(
  lca : Node,
  load : Node,
  early : Node,
  late : Array[Node?],
) -> Node {
  let stop_at = early.idom()
  let mut cfg = lca
  while true {
    if stop_at is Some(stop) && cfg == stop {
      break
    }
    cfg._anti = load._nid
    match cfg.idom() {
      Some(next) => cfg = next
      None => break
    }
  }

  let mem = load.input_exn(1)
  let mut lca0 = lca
  for use_ in mem._outputs {
    match use_ {
      Some(st) if st.kind == Store =>
        match late[st._nid] {
          Some(stblk) => lca0 = GlobalCodeMotion::anti_dep(load, stblk, st.cfg0(), lca0, Some(st))
          None => ()
        }
      Some(phi) if phi.kind == Phi => {
        let region = phi.input_exn(0)
        for i = 1; i < phi.n_ins(); i = i + 1 {
          if phi.input(i) == Some(mem) {
            match region.input(i) {
              Some(stblk) => lca0 = GlobalCodeMotion::anti_dep(load, stblk, mem.cfg0(), lca0, None)
              None => ()
            }
          }
        }
      }
      _ => ()
    }
  }
  lca0
}

///|
fn GlobalCodeMotion::anti_dep(
  load : Node,
  stblk : Node,
  defblk : Node,
  lca : Node,
  st : Node?,
) -> Node {
  let stop_at = defblk.idom()
  let mut stblk = stblk
  let mut lca = lca
  while true {
    if stop_at is Some(stop) && stblk == stop {
      break
    }
    if stblk._anti == load._nid {
      lca = stblk.idom_lca(Some(lca))
      match st {
        Some(store) =>
          if lca == stblk && !_has_input(store, load) {
            ignore(store.add_def(Some(load)))
          }
        None => ()
      }
      return lca
    }
    match stblk.idom() {
      Some(next) => stblk = next
      None => break
    }
  }
  lca
}
