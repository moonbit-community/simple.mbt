///|
struct RegAlloc {
  mut _next_reg : Int
  _reg_map : Map[Int, Int]
}

///|
fn RegAlloc::new() -> RegAlloc {
  { _next_reg: 0, _reg_map: Map::new() }
}

///|
fn RegAlloc::assign(self : RegAlloc, n : Node) -> Int {
  match self._reg_map.get(n._nid) {
    Some(reg) => reg
    None => {
      let reg = self._next_reg
      self._next_reg = self._next_reg + 1
      self._reg_map[n._nid] = reg
      reg
    }
  }
}

///|
fn RegAlloc::regnum(self : RegAlloc, n : Node) -> Int {
  match self._reg_map.get(n._nid) {
    Some(reg) => reg
    None => -1
  }
}

///|
fn RegAlloc::run(code : CodeGen) -> RegAlloc {
  let alloc = RegAlloc::new()
  let blocks = ListScheduler::cfg_blocks(code._start)
  for bb in blocks {
    if !bb.block_head() {
      continue
    }
    let nodes = ListScheduler::block_nodes(bb)
    for n in nodes {
      if n.kind == Mach {
        ignore(alloc.assign(n))
      }
    }
  }
  alloc
}

///|
fn RegAlloc::dump(self : RegAlloc, code : CodeGen) -> String {
  let sb = StringBuilder::new()
  let mut first = true
  let blocks = ListScheduler::cfg_blocks(code._start)
  for bb in blocks {
    if !bb.block_head() {
      continue
    }
    let nodes = ListScheduler::block_nodes(bb)
    for n in nodes {
      if n.kind == Mach {
        if first {
          first = false
        } else {
          sb.write_string("\n")
        }
        let reg = self.regnum(n)
        sb.write_string(n._mach_op)
        sb.write_string(" -> v")
        sb.write_string(reg.to_string())
      }
    }
  }
  sb.to_string()
}
