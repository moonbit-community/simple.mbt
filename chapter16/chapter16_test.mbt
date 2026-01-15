///|
test "chapter16: jig" {
  let parser = Parser::new("return 3.14;\n")
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return 3.14;")
  assert_true(
    eval_float(stop, 0L).is_close(
      3.14,
      relative_tolerance=1.0e-12,
      absolute_tolerance=1.0e-12,
    ),
  )
}

///|
test "chapter16: multi0" {
  let parser = Parser::new("int x, y;\n" + "return x+y;\n")
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return 0;")
  assert_eq(eval_int(stop, 0L), 0L)
}

///|
test "chapter16: multi1" {
  let parser = Parser::new("int x=2, y=x+1;\n" + "return x+y;\n")
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return 5;")
  assert_eq(eval_int(stop, 0L), 5L)
}

///|
test "chapter16: final0" {
  expect_iterate_error("int !x=2;\n" + "x=3;\n" + "return x;\n", "Cannot reassign final 'x'")
}

///|
test "chapter16: final1" {
  let parser = Parser::new(
    "int !x=2, y=3;\n" +
    "if( arg ) { int x = y; x = x*x; y=x; }\n" +
    "return y;\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return Phi(Region21,9,3);")
  assert_eq(eval_int(stop, 0L), 3L)
  assert_eq(eval_int(stop, 1L), 9L)
}

///|
test "chapter16: construct0" {
  let parser = Parser::new(
    "struct X { int x=3; };\n" + "X z = new X;\n" + "return z.x;\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return 3;")
  assert_eq(eval_int(stop, 0L), 3L)
}

///|
test "chapter16: construct1" {
  let parser = Parser::new(
    "struct X { int !x; };\n" + "X z = new X { x=3; };\n" + "return z.x;\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return 3;")
  assert_eq(eval_int(stop, 0L), 3L)
}

///|
test "chapter16: construct2" {
  let parser = Parser::new(
    "struct X { int x=3; };\n" + "X z = new X { x = 4; };\n" + "return z.x;\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return 4;")
  assert_eq(eval_int(stop, 0L), 4L)
}

///|
test "chapter16: struct final" {
  let parser = Parser::new(
    "struct Point { int !x, !y; };\n" +
    "Point p = new Point { x=3; y=4; };\n" +
    "return p;\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return Point;")
  assert_obj_int_fields(Evaluator::evaluate(stop, parameter=0L), "Point", [3L, 4L])
}

///|
test "chapter16: linked list 1" {
  let parser = Parser::new(
    "struct LLI { LLI? next; int i; };\n" +
    "LLI? head = null;\n" +
    "while( arg ) {\n" +
    "    head = new LLI { next=head; i=arg; };\n" +
    "    arg = arg-1;\n" +
    "}\n" +
    "if( !head ) return 0;\n" +
    "LLI? next = head.next;\n" +
    "if( !next ) return 1;\n" +
    "return next.i;\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "Stop[ return 0; return 1; return .i; ]")
  assert_eq(eval_int(stop, 0L), 0L)
  assert_eq(eval_int(stop, 1L), 1L)
  assert_eq(eval_int(stop, 3L), 2L)
}

///|
test "chapter16: linked list 2" {
  let parser = Parser::new(
    "struct LLI { LLI? next; int i; };\n" +
    "LLI? head = null;\n" +
    "while( arg ) {\n" +
    "    head = new LLI {\n" +
    "        next=head;\n" +
    "        int tmp=arg;\n" +
    "        while( arg > 10 ) {\n" +
    "            tmp = tmp + arg;\n" +
    "            arg = arg - 1;\n" +
    "        }\n" +
    "        i=tmp;\n" +
    "    };\n" +
    "    arg = arg-1;\n" +
    "}\n" +
    "if( !head ) return 0;\n" +
    "LLI? next = head.next;\n" +
    "if( !next ) return 1;\n" +
    "return next.i;\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "Stop[ return 0; return 1; return .i; ]")
  assert_eq(eval_int(stop, 0L), 0L)
  assert_eq(eval_int(stop, 1L), 1L)
  assert_eq(eval_int(stop, 11L), 2L)
}

///|
test "chapter16: square" {
  let parser = Parser::new(
    "struct Square {\n" +
    "    flt !side = arg;\n" +
    "    flt diag = arg*arg/2;\n" +
    "    while( 1 ) {\n" +
    "        flt next = (side/diag + diag)/2;\n" +
    "        if( next == diag ) break;\n" +
    "        diag = next;\n" +
    "    }\n" +
    "};\n" +
    "return new Square;\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return Square;")
  match Evaluator::evaluate(stop, parameter=3L) {
    EvalValue::Obj(obj) => {
      assert_eq(obj.struct_._name, "Square")
      assert_eq(obj.fields.length(), 2)
      match obj.fields[0] {
        EvalValue::Float(v) =>
          assert_true(v.is_close(3.0, relative_tolerance=1.0e-12, absolute_tolerance=1.0e-12))
        _ => fail("expected float field")
      }
      match obj.fields[1] {
        EvalValue::Float(v) =>
          assert_true(
            v.is_close(
              1.7320508075688772,
              relative_tolerance=1.0e-12,
              absolute_tolerance=1.0e-12,
            ),
          )
        _ => fail("expected float field")
      }
    }
    _ => fail("expected object")
  }
  match Evaluator::evaluate(stop, parameter=4L) {
    EvalValue::Obj(obj) => {
      match obj.fields[0] {
        EvalValue::Float(v) =>
          assert_true(v.is_close(4.0, relative_tolerance=1.0e-12, absolute_tolerance=1.0e-12))
        _ => fail("expected float field")
      }
      match obj.fields[1] {
        EvalValue::Float(v) =>
          assert_true(v.is_close(2.0, relative_tolerance=1.0e-12, absolute_tolerance=1.0e-12))
        _ => fail("expected float field")
      }
    }
    _ => fail("expected object")
  }
}

