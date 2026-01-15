///|
test "chapter13: jig" {
  let parser = Parser::new("return 3.14;\n")
  let stop = parser.parse(show=false).iterate(show=false)
  assert_eq(stop.print(), "return 3.14;")
  match Evaluator::evaluate(stop, parameter=0L) {
    EvalValue::Float(v) =>
      assert_true(
        v.is_close(3.14, relative_tolerance=1.0e-12, absolute_tolerance=1.0e-12),
      )
    _ => fail("expected float")
  }
}

///|
test "chapter13: linked list 0" {
  expect_iterate_error(
    "struct LLI { LLI? next; int i; };\n" +
    "LLI? !head = null;\n" +
    "while( arg ) {\n" +
    "    LLI !x = new LLI;\n" +
    "    x.next = head;\n" +
    "    x.i = arg;\n" +
    "    head = x;\n" +
    "    arg = arg-1;\n" +
    "}\n" +
    "return head.next.i;\n",
    "Might be null accessing 'i'",
  )
}

///|
test "chapter13: linked list 1" {
  let parser = Parser::new(
    "struct LLI { LLI? next; int i; };\n" +
    "LLI? !head = null;\n" +
    "while( arg ) {\n" +
    "    LLI !x = new LLI;\n" +
    "    x.next = head;\n" +
    "    x.i = arg;\n" +
    "    head = x;\n" +
    "    arg = arg-1;\n" +
    "}\n" +
    "if( !head ) return 0;\n" +
    "LLI? next = head.next;\n" +
    "if( next==null ) return 1;\n" +
    "return next.i;\n",
  )
  let stop = parser.parse(show=false).iterate(show=false)
  assert_eq(stop.print(), "Stop[ return 0; return 1; return .i; ]")
  match Evaluator::evaluate(stop, parameter=3L) {
    EvalValue::Int(v) => assert_eq(v, 2L)
    _ => fail("expected int")
  }
}

///|
test "chapter13: co-recur" {
  let parser = Parser::new(
    "struct int0 { int i; flt0? f; };\n" +
    "struct flt0 { flt f; int0? i; };\n" +
    "int0 !i0 = new int0;\n" +
    "i0.i = 17;\n" +
    "flt0 !f0 = new flt0;\n" +
    "f0.f = 3.14;\n" +
    "i0.f = f0;\n" +
    "f0.i = i0;\n" +
    "return f0.i.f.i.i;\n",
  )
  let stop = parser.parse(show=false).iterate(show=false)
  assert_eq(stop.print(), "return 17;")
}

///|
test "chapter13: null ref 0" {
  let parser = Parser::new(
    "struct N { N? next; int i; };\n" + "N n = new N;\n" + "return n.next;\n",
  )
  let stop = parser.parse(show=false).iterate(show=false)
  assert_eq(stop.print(), "return null;")
}

///|
test "chapter13: null ref 1" {
  let parser = Parser::new(
    "struct M { int m; };\n" +
    "struct N { M next; int i; };\n" +
    "N n = new N { next = new M; };\n" +
    "return n.next;\n",
  )
  let stop = parser.parse(show=false).iterate(show=false)
  assert_eq(stop.print(), "return (const)M;")
}

///|
test "chapter13: null ref 2" {
  expect_iterate_error(
    "struct M { int m; };\n" +
    "struct N { M next; int i; };\n" +
    "N n = new N { next = null; }\n" +
    "return n.next;\n",
    "Type null is not of declared type *M",
  )
}

///|
test "chapter13: null ref 3" {
  expect_iterate_error(
    "struct N { N? next; int i; };\n" +
    "N !n = new N;\n" +
    "n.i = 3.14;\n" +
    "return n.i;\n",
    "Type 3.14 is not of declared type int",
  )
}

///|
test "chapter13: null ref 4" {
  expect_iterate_error("-null-5/null-5;", "Cannot 'Add' null")
}

///|
test "chapter13: null ref 5" {
  expect_iterate_error("return null+42;", "Cannot 'Add' null")
}

///|
test "chapter13: empty" {
  let parser = Parser::new("struct S{};\n")
  let stop = parser.parse(show=false).iterate(show=false)
  assert_eq(stop.print(), "return 0;")
  match Evaluator::evaluate(stop, parameter=0L) {
    EvalValue::Int(v) => assert_eq(v, 0L)
    _ => fail("expected int")
  }
}

///|
test "chapter13: forward ref 0" {
  expect_iterate_error(
    "struct S1 { S2 s; };\n" + "return new S2;\n",
    "Unknown struct type 'S2'",
  )
}

///|
test "chapter13: forward ref 1" {
  let parser = Parser::new(
    "struct S1 { S2? s; };\n" +
    "struct S2 { int x; };\n" +
    "return new S1.s=new S2;\n",
  )
  let stop = parser.parse(show=false).iterate(show=false)
  assert_eq(stop.print(), "return S2;")
}

///|
test "chapter13: check null" {
  expect_iterate_error(
    "struct I {int i;};\n" +
    "struct P { I? pi; };\n" +
    "P !p1 = new P;\n" +
    "P p2 = new P;\n" +
    "p2.pi = new I;\n" +
    "p2.pi.i = 2;\n" +
    "if (arg) p1 = new P;\n" +
    "return p1.pi.i + 1;\n",
    "Might be null accessing 'i'",
  )
}
