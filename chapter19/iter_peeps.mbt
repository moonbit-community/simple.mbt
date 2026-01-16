///|
priv struct JavaRandom {
  mut _seed : Int64
}

///|
let _random_multiplier : Int64 = 0x5DEECE66DL

///|
let _random_addend : Int64 = 0xBL

///|
let _random_mask : Int64 = (1L << 48) - 1L

///|
fn JavaRandom::new(seed : Int64) -> JavaRandom {
  let r : JavaRandom = { _seed: 0L }
  r.set_seed(seed)
  r
}

///|
fn JavaRandom::set_seed(self : JavaRandom, seed : Int64) -> Unit {
  self._seed = (seed ^ _random_multiplier) & _random_mask
}

///|
fn JavaRandom::next(self : JavaRandom, bits : Int) -> Int {
  self._seed = (self._seed * _random_multiplier + _random_addend) & _random_mask
  (self._seed >> (48 - bits)).to_int()
}

///|
fn JavaRandom::next_int(self : JavaRandom, bound : Int) -> Int {
  if bound <= 0 {
    panic()
  }
  if (bound & -bound) == bound {
    let r = self.next(31)
    let mut k = 0
    let mut b = bound
    while b > 1 {
      b = b >> 1
      k = k + 1
    }
    return r >> (31 - k)
  }
  while true {
    let bits = self.next(31)
    let val = bits % bound
    let bits64 = bits.to_int64()
    let val64 = val.to_int64()
    let bound64 = bound.to_int64()
    if bits64 - val64 + (bound64 - 1L) < 0x80000000L {
      return val
    }
  }
  0
}

///|
priv struct WorkList {
  mut _es : Array[Node]
  mut _on : Array[Bool]
  mut _rand : JavaRandom
  _seed : Int64
}

///|
fn WorkList::new(seed : Int64) -> WorkList {
  { _es: [], _on: [], _rand: JavaRandom::new(seed), _seed: seed }
}

///|
fn WorkList::_ensure_on_size(self : WorkList, nid : Int) -> Unit {
  while nid >= self._on.length() {
    self._on.push(false)
  }
}

///|
fn WorkList::push(self : WorkList, x : Node?) -> Node? {
  match x {
    None => None
    Some(n) => {
      self._ensure_on_size(n._nid + 1)
      if !self._on[n._nid] {
        self._on[n._nid] = true
        self._es.push(n)
      }
      Some(n)
    }
  }
}

///|
fn WorkList::add_all(self : WorkList, ary : Array[Node]) -> Unit {
  for n in ary {
    ignore(self.push(Some(n)))
  }
}

///|
fn WorkList::pop(self : WorkList) -> Node? {
  let len = self._es.length()
  if len == 0 {
    return None
  }
  let idx = self._rand.next_int(len)
  let x = self._es[idx]
  let last = self._es.remove(len - 1)
  if idx < self._es.length() {
    self._es[idx] = last
  }
  self._ensure_on_size(x._nid + 1)
  self._on[x._nid] = false
  Some(x)
}

///|
fn WorkList::on(self : WorkList, x : Node) -> Bool {
  self._ensure_on_size(x._nid + 1)
  self._on[x._nid]
}

///|
fn WorkList::clear(self : WorkList) -> Unit {
  self._es = []
  self._on = []
  self._rand.set_seed(self._seed)
}

///|
let work : WorkList = WorkList::new(123L)

///|
let mid_assert_flag : Ref[Bool] = Ref::{ val: false }

///|
pub struct IterPeeps {}

///|
pub fn IterPeeps::mid_assert() -> Bool {
  mid_assert_flag.val
}

///|
pub fn IterPeeps::reset() -> Unit {
  work.clear()
}

///|
pub fn IterPeeps::add(n : Node) -> Node {
  ignore(work.push(Some(n)))
  n
}

///|
pub fn IterPeeps::add_all(ary : Array[Node?]) -> Unit {
  for n in ary {
    ignore(work.push(n))
  }
}

///|
pub fn IterPeeps::add_all_nodes(ary : Array[Node]) -> Unit {
  work.add_all(ary)
}

///|
pub fn IterPeeps::iterate(stop : Node) -> Node {
  let visited : Array[Bool] = []
  fn seed(visited : Array[Bool], node : Node) -> Unit {
    let nid = node._nid
    while visited.length() <= nid {
      visited.push(false)
    }
    if visited[nid] {
      return
    }
    visited[nid] = true
    ignore(work.push(Some(node)))
    for def in node._inputs {
      match def {
        Some(n) => seed(visited, n)
        None => ()
      }
    }
  }
  seed(visited, stop)

  let mut n = work.pop()
  while n is Some(node) {
    if !node.is_dead() {
      match node.peephole_opt() {
        None => ()
        Some(x) =>
          if !x.is_dead() {
            if x._type is None {
              ignore(x.set_type(x.compute()))
            }
            if x != node || x.kind != Constant {
              // All outputs of node (changing node), not x (prior existing node).
              for z in node._outputs {
                ignore(work.push(z))
              }
              // Everybody gets a free "go again" in case they didn't get made
              // in their final form.
              ignore(work.push(Some(x)))
              if x != node {
                for z in node._inputs {
                  ignore(work.push(z))
                }
                node.subsume(x)
              }
            }
            node.move_deps_to_worklist()
          }
      }
    }
    n = work.pop()
  }
  stop
}
