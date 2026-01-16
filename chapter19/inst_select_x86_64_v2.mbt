///|
fn _ensure_bool_instsel(visited : Array[Bool], nid : Int) -> Unit {
  while visited.length() <= nid {
    visited.push(false)
  }
}

///|
fn _const_int(n : Node) -> Int64? {
  if n.kind != Constant {
    return None
  }
  match n._con {
    Some(Int(i)) => if i.is_constant() { Some(i.value_exn()) } else { None }
    _ => None
  }
}

///|
fn _mach_const_int(n : Node) -> Int64? {
  if n.kind != Mach {
    return None
  }
  match n._con {
    Some(Int(i)) => if i.is_constant() { Some(i.value_exn()) } else { None }
    _ => None
  }
}

///|
fn _mach_lea_params(n : Node) -> (Int64, Int64)? {
  if n.kind != Mach || n._mach_op != "lea" {
    return None
  }
  match n._con {
    Some(Type::Tuple(Some(ts))) if ts.length() == 2 =>
      match (ts[0], ts[1]) {
        (Int(off), Int(scale)) if off.is_constant() && scale.is_constant() =>
          Some((off.value_exn(), scale.value_exn()))
        _ => None
      }
    _ => None
  }
}

///|
fn _mach(op : String, inputs : Array[Node?], con? : Type = bottom) -> Node {
  let m = Node::new_raw(Mach, inputs)
  m._mach_op = op
  // Reuse Node._con as a generic embedded constant slot for machine ops.
  if con != bottom {
    m._con = Some(con)
  }
  m
}

///|
fn _lea_con(off : Int64, scale : Int64) -> Type {
  // Store LEA (off,scale) as a small tuple constant; printing ignores it.
  Type::Tuple(Some([TypeInteger::constant(off), TypeInteger::constant(scale)]))
}

///|
fn _scale_index(n : Node) -> (Node, Int64) {
  // Match x86 addressing scales: 1,2,4,8 (shift 0..3).
  if n.kind == Mach && n._mach_op == "shli" {
    match _mach_const_int(n) {
      Some(shift) if 0L <= shift && shift <= 3L => {
        let idx = n.input_exn(1)
        (idx, 1L << shift.to_int())
      }
      _ => (n, 1L)
    }
  } else {
    (n, 1L)
  }
}

///|
fn _select_lea(n : Node, base : Node, idx0 : Node, off : Int64) -> Bool {
  let (idx1, scale) = _scale_index(idx0)
  if off == 0L && scale == 1L {
    return false
  }
  let mut base0 = base
  let mut idx = idx1
  // Prefer printing `arg` as the base for symmetric (scale==1) LEAs.
  if scale == 1L &&
    ((idx.kind == Proj && base0.kind != Proj) ||
      (idx.kind == Parm && base0.kind != Parm)) {
    let tmp = base0
    base0 = idx
    idx = tmp
  }
  let m = _mach(
    "lea",
    [n.input(0), Some(base0), Some(idx)],
    con=_lea_con(off, scale),
  )
  m._type = n._type
  n.subsume(m)
  true
}

///|
fn _select_add(n : Node) -> Unit {
  let lhs0 = n.input_exn(1)
  let rhs0 = n.input_exn(2)

  // ((base+idx) + off)
  match _const_int(rhs0) {
    Some(off) =>
      if lhs0.kind == Mach {
        if lhs0._mach_op == "add" {
          let base = lhs0.input_exn(1)
          let idx = lhs0.input_exn(2)
          if _select_lea(n, base, idx, off) {
            return
          }
        } else {
          // (lea base idx) + off
          match _mach_lea_params(lhs0) {
            Some((off0, scale0)) => {
              let base = lhs0.input_exn(1)
              let idx = lhs0.input_exn(2)
              let m = _mach(
                "lea",
                [n.input(0), Some(base), Some(idx)],
                con=_lea_con(off0 + off, scale0),
              )
              m._type = n._type
              n.subsume(m)
              return
            }
            None => ()
          }
        }
      }
    None => ()
  }

  // (base + (idx<<scale))
  if _const_int(rhs0) is None {
    if lhs0.kind == Mach && lhs0._mach_op == "shli" &&
      !(rhs0.kind == Mach && rhs0._mach_op == "shli") {
      if _select_lea(n, rhs0, lhs0, 0L) {
        return
      }
    } else if rhs0.kind == Mach && rhs0._mach_op == "shli" {
      if _select_lea(n, lhs0, rhs0, 0L) {
        return
      }
    }
  }

  let (lhs, rhs) = match (_const_int(lhs0), _const_int(rhs0)) {
    (Some(_), None) => (rhs0, lhs0)
    _ => (lhs0, rhs0)
  }
  match _const_int(rhs) {
    Some(imm) => {
      let op = if imm == 1L {
        "inc"
      } else if imm == -1L {
        "dec"
      } else {
        "addi"
      }
      let m = _mach(op, [n.input(0), Some(lhs)], con=TypeInteger::constant(imm))
      // Preserve computed type for later phases.
      m._type = n._type
      n.subsume(m)
    }
    None => {
      let m = _mach("add", [n.input(0), Some(lhs), Some(rhs)])
      m._type = n._type
      n.subsume(m)
    }
  }
}

///|
fn _select_sub(n : Node) -> Unit {
  let lhs = n.input_exn(1)
  let rhs = n.input_exn(2)
  match _const_int(rhs) {
    Some(imm0) => {
      let imm = -imm0
      let op = if imm == 1L {
        "inc"
      } else if imm == -1L {
        "dec"
      } else {
        "addi"
      }
      let m = _mach(op, [n.input(0), Some(lhs)], con=TypeInteger::constant(imm))
      m._type = n._type
      n.subsume(m)
    }
    None => {
      let m = _mach("sub", [n.input(0), Some(lhs), Some(rhs)])
      m._type = n._type
      n.subsume(m)
    }
  }
}

///|
fn _select_mul(n : Node) -> Unit {
  let lhs0 = n.input_exn(1)
  let rhs0 = n.input_exn(2)
  let (lhs, rhs) = match (_const_int(lhs0), _const_int(rhs0)) {
    (Some(_), None) => (rhs0, lhs0)
    _ => (lhs0, rhs0)
  }
  match _const_int(rhs) {
    Some(imm) => {
      // Prefer shifts for power-of-two constants (matches refs/simple x86 matcher output).
      let mut x = imm
      let mut shift = 0L
      while x > 1L && (x & 1L) == 0L {
        x = x >> 1
        shift = shift + 1L
      }
      let m = if x == 1L && imm > 0L {
        _mach("shli", [n.input(0), Some(lhs)], con=TypeInteger::constant(shift))
      } else {
        _mach("muli", [n.input(0), Some(lhs)], con=TypeInteger::constant(imm))
      }
      m._type = n._type
      n.subsume(m)
    }
    None => {
      let m = _mach("mul", [n.input(0), Some(lhs), Some(rhs)])
      m._type = n._type
      n.subsume(m)
    }
  }
}

///|
fn _select_div(n : Node) -> Unit {
  let lhs = n.input_exn(1)
  let rhs = n.input_exn(2)
  // No x86 immediate div; keep the constant input (prints as in refs/simple).
  let m = _mach("div", [n.input(0), Some(lhs), Some(rhs)])
  m._type = n._type
  n.subsume(m)
}

///|
fn _select_and(n : Node) -> Unit {
  let lhs0 = n.input_exn(1)
  let rhs0 = n.input_exn(2)
  let (lhs, rhs) = match (_const_int(lhs0), _const_int(rhs0)) {
    (Some(_), None) => (rhs0, lhs0)
    _ => (lhs0, rhs0)
  }
  match _const_int(rhs) {
    Some(imm) => {
      let m = _mach(
        "andi",
        [n.input(0), Some(lhs)],
        con=TypeInteger::constant(imm),
      )
      m._type = n._type
      n.subsume(m)
    }
    None => {
      let m = _mach("and", [n.input(0), Some(lhs), Some(rhs)])
      m._type = n._type
      n.subsume(m)
    }
  }
}

///|
fn _select_or(n : Node) -> Unit {
  let lhs0 = n.input_exn(1)
  let rhs0 = n.input_exn(2)
  let (lhs, rhs) = match (_const_int(lhs0), _const_int(rhs0)) {
    (Some(_), None) => (rhs0, lhs0)
    _ => (lhs0, rhs0)
  }
  match _const_int(rhs) {
    Some(imm) => {
      let m = _mach(
        "ori",
        [n.input(0), Some(lhs)],
        con=TypeInteger::constant(imm),
      )
      m._type = n._type
      n.subsume(m)
    }
    None => {
      let m = _mach("or", [n.input(0), Some(lhs), Some(rhs)])
      m._type = n._type
      n.subsume(m)
    }
  }
}

///|
fn _select_xor(n : Node) -> Unit {
  let lhs0 = n.input_exn(1)
  let rhs0 = n.input_exn(2)
  let (lhs, rhs) = match (_const_int(lhs0), _const_int(rhs0)) {
    (Some(_), None) => (rhs0, lhs0)
    _ => (lhs0, rhs0)
  }
  match _const_int(rhs) {
    Some(imm) => {
      let m = _mach(
        "xori",
        [n.input(0), Some(lhs)],
        con=TypeInteger::constant(imm),
      )
      m._type = n._type
      n.subsume(m)
    }
    None => {
      let m = _mach("xor", [n.input(0), Some(lhs), Some(rhs)])
      m._type = n._type
      n.subsume(m)
    }
  }
}

///|
fn _select_shl(n : Node) -> Unit {
  let lhs = n.input_exn(1)
  let rhs = n.input_exn(2)
  match _const_int(rhs) {
    Some(imm) => {
      let m = _mach(
        "shli",
        [n.input(0), Some(lhs)],
        con=TypeInteger::constant(imm),
      )
      m._type = n._type
      n.subsume(m)
    }
    None => {
      let m = _mach("shl", [n.input(0), Some(lhs), Some(rhs)])
      m._type = n._type
      n.subsume(m)
    }
  }
}

///|
fn _select_sar(n : Node) -> Unit {
  let lhs = n.input_exn(1)
  let rhs = n.input_exn(2)
  match _const_int(rhs) {
    Some(imm) => {
      let m = _mach(
        "sari",
        [n.input(0), Some(lhs)],
        con=TypeInteger::constant(imm),
      )
      m._type = n._type
      n.subsume(m)
    }
    None => {
      let m = _mach("sar", [n.input(0), Some(lhs), Some(rhs)])
      m._type = n._type
      n.subsume(m)
    }
  }
}

///|
fn _select_shr(n : Node) -> Unit {
  let lhs = n.input_exn(1)
  let rhs = n.input_exn(2)
  match _const_int(rhs) {
    Some(imm) => {
      let m = _mach(
        "shri",
        [n.input(0), Some(lhs)],
        con=TypeInteger::constant(imm),
      )
      m._type = n._type
      n.subsume(m)
    }
    None => {
      let m = _mach("shr", [n.input(0), Some(lhs), Some(rhs)])
      m._type = n._type
      n.subsume(m)
    }
  }
}

///|
fn _select_bool(n : Node, bop : String) -> Unit {
  let lhs0 = n.input_exn(1)
  let rhs0 = n.input_exn(2)
  let (lhs, rhs) = match (_const_int(lhs0), _const_int(rhs0)) {
    (Some(_), None) => (rhs0, lhs0)
    _ => (lhs0, rhs0)
  }
  let cmp = match _const_int(rhs) {
    Some(imm) => {
      let op = if imm == 0L { "test" } else { "cmp" }
      let c = _mach(op, [n.input(0), Some(lhs)], con=TypeInteger::constant(imm))
      // Treat flags as an opaque value for now.
      c._type = Some(type_integer_bot)
      c
    }
    None => {
      let c = _mach("cmp", [n.input(0), Some(lhs), Some(rhs)])
      c._type = Some(type_integer_bot)
      c
    }
  }
  let set = _mach("set" + bop, [n.input(0), Some(cmp)])
  set._type = n._type
  n.subsume(set)
}

///|
fn _select_to_float(n : Node) -> Unit {
  let inp = n.input_exn(1)
  let m = _mach("i2f8", [n.input(0), Some(inp)])
  m._type = n._type
  n.subsume(m)
}

///|
fn _select_addf(n : Node) -> Unit {
  let lhs = n.input_exn(1)
  let rhs = n.input_exn(2)
  let m = _mach("addf", [n.input(0), Some(lhs), Some(rhs)])
  m._type = n._type
  n.subsume(m)
}

///|
fn _select_subf(n : Node) -> Unit {
  let lhs = n.input_exn(1)
  let rhs = n.input_exn(2)
  let m = _mach("subf", [n.input(0), Some(lhs), Some(rhs)])
  m._type = n._type
  n.subsume(m)
}

///|
fn _select_mulf(n : Node) -> Unit {
  let lhs = n.input_exn(1)
  let rhs = n.input_exn(2)
  let m = _mach("mulf", [n.input(0), Some(lhs), Some(rhs)])
  m._type = n._type
  n.subsume(m)
}

///|
fn _select_divf(n : Node) -> Unit {
  let lhs = n.input_exn(1)
  let rhs = n.input_exn(2)
  let m = _mach("divf", [n.input(0), Some(lhs), Some(rhs)])
  m._type = n._type
  n.subsume(m)
}

///|
pub fn inst_select_x86_64_v2(stop : Node) -> Unit {
  let visited : Array[Bool] = []
  fn walk(visited : Array[Bool], n : Node) -> Unit {
    _ensure_bool_instsel(visited, n._nid)
    if visited[n._nid] {
      return
    }
    visited[n._nid] = true

    // Post-order: rewrite children first, then this node.
    for def in n._inputs {
      match def {
        Some(d) => walk(visited, d)
        None => ()
      }
    }
    match n.kind {
      Add => _select_add(n)
      AddF => _select_addf(n)
      Sub => _select_sub(n)
      SubF => _select_subf(n)
      Mul => _select_mul(n)
      MulF => _select_mulf(n)
      Div => _select_div(n)
      DivF => _select_divf(n)
      And => _select_and(n)
      Or => _select_or(n)
      Xor => _select_xor(n)
      Shl => _select_shl(n)
      Sar => _select_sar(n)
      Shr => _select_shr(n)
      ToFloat => _select_to_float(n)
      BoolEq => _select_bool(n, "==")
      BoolLt => _select_bool(n, "<")
      BoolLe => _select_bool(n, "<=")
      _ => ()
    }
  }

  walk(visited, stop)
}
