///|
fn is_simple_type(t : Type) -> Bool {
  match t {
    Bot | Top | Ctrl | XCtrl | Nil | XNil => true
    _ => false
  }
}

///|
fn check_commute(t0 : Type, t1 : Type) -> Unit raise {
  if t0 == t1 {
    return
  }
  // By design in meet, args may be flipped to a canonical order.
  if is_simple_type(t0) && !is_simple_type(t1) {
    return
  }
  let mta = t0.meet(t1)
  let mtb = t1.meet(t0)
  assert_eq(mta, mtb)
}

///|
fn check_symmetric(t0 : Type, t1 : Type) -> Unit raise {
  if t0 == t1 {
    return
  }
  let mt = t0.meet(t1)
  let ta = mt.dual().meet(t1.dual())
  let tb = mt.dual().meet(t0.dual())
  assert_eq(ta, t1.dual())
  assert_eq(tb, t0.dual())
}

///|
fn assoc(t0 : Type, t1 : Type, t2 : Type) -> Unit raise {
  let t01 = t0.meet(t1)
  let t12 = t1.meet(t2)
  let t01_2 = t01.meet(t2)
  let t0_12 = t0.meet(t12)
  assert_eq(t01_2, t0_12)
}

///|
test "chapter18: type adhoc" {
  assert_eq(bottom, type_integer_true.meet(type_nil))
  assert_eq(bottom, type_integer_top.meet(type_nil))

  let s1 = TypeStruct::make("s1", [
    Field::make("a", type_integer_bot, -1, false),
    Field::make("b", type_integer_bot, -2, false),
  ])
  let s2 = TypeStruct::make("s2", [
    Field::make("a", type_integer_bot, -3, false),
    Field::make("b", type_integer_bot, -4, false),
  ])

  assert_eq(s1.make_ro(), s1.glb())
  assert_true(s1 != s1.dual())
  assert_eq(s1.make_ro(), s1.dual().glb())

  let m1 = Type::mem(1, t=type_nil)
  let m2 = Type::mem(2, t=type_integer_u16)
  let m3 = Type::mem(3, t=type_float_bot)
  let m4 = Type::mem(4, t=type_integer_bot)

  assert_true(m1 != m2)
  assert_true(m2 != m3)
  assert_true(m3 != m4)

  assert_eq(type_struct_bot, s1.meet(s2))
  assert_eq(type_mem_bot, m1.meet(m2))
  assert_eq(type_mem_bot, m1.meet(m3))
  assert_eq(type_mem_bot, m3.meet(m4))

  assert_eq(Type::mem(1, t=bottom), m1.glb())
  assert_eq(Type::mem(1, t=type_xnil), m1.dual())
  assert_eq(m4.dual(), m4.glb().dual())

  let ptr1 = Type::mem_ptr(s1)
  match ptr1 {
    MemPtr(obj, nil) => {
      assert_eq(obj, s1)
      assert_eq(nil, 2)
    }
    _ => fail("expected MemPtr")
  }
  let ptr2 = Type::mem_ptr(s2)
  match ptr2 {
    MemPtr(obj, nil) => {
      assert_eq(obj, s2)
      assert_eq(nil, 2)
    }
    _ => fail("expected MemPtr")
  }

  let ptr1nil = Type::mem_ptr(s1, nullable=true)
  match ptr1nil {
    MemPtr(obj, nil) => {
      assert_eq(obj, s1)
      assert_eq(nil, 3)
    }
    _ => fail("expected MemPtr")
  }
  let ptr2nil = Type::mem_ptr(s2, nullable=true)
  match ptr2nil {
    MemPtr(obj, nil) => {
      assert_eq(obj, s2)
      assert_eq(nil, 3)
    }
    _ => fail("expected MemPtr")
  }

  assert_true(ptr1 != ptr2)
  assert_true(ptr1 != ptr1.glb())
  assert_eq(ptr1nil.make_ro(), ptr1.glb())

  assert_eq(ptr1, ptr1.dual().dual())
  assert_eq(ptr1.glb().make_ro(), ptr1.dual().glb())

  assert_eq(type_mem_ptr_bot, ptr1.meet(ptr2nil))
  assert_eq(ptr1.glb(), ptr1.meet(type_nil).make_ro())

  // NULL / ptr meet & join
  let top_ptr = type_mem_ptr_top
  let bot_ptr = type_mem_ptr_bot
  let ptr = type_mem_ptr_voidptr
  let null_ = type_nil

  assert_eq(bot_ptr, null_.meet(ptr))
  assert_eq(ptr, ptr1.meet(ptr2))

  let null_join_ptr1 = null_.join(ptr1)
  assert_eq(type_ptr_xnptr, null_join_ptr1)

  let null_join_ptr = ptr.join(null_)
  assert_eq(type_ptr_xnptr, null_join_ptr)

  ignore(top_ptr)
  ignore(ptr1.dual())
  ignore(ptr1nil.dual())
}

///|
test "chapter18: lattice theory" {
  let ts = Type::gather()
  for t0 in ts {
    for t1 in ts {
      check_commute(t0, t1)
      check_symmetric(t0, t1)
    }
  }
  for t0 in ts {
    for t1 in ts {
      for t2 in ts {
        assoc(t0, t1, t2)
      }
    }
  }
  for t0 in ts {
    for t1 in ts {
      if t0.isa(t1) {
        for t2 in ts {
          let t02 = t0.join(t2)
          let t12 = t1.join(t2)
          let mt = t02.meet(t12)
          assert_eq(mt, t12)
        }
      }
    }
  }
}

///|
test "chapter18: cyclic0" {
  let d0 = type_struct_s1.dual()
  let d1 = d0.dual()
  assert_eq(type_struct_s1, d1)
}
