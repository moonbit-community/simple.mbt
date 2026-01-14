///|
fn eval_int12(stop : Node, parameter : Int64) -> Int64 raise {
  match Evaluator::evaluate(stop, parameter=parameter) {
    EvalValue::Int(v) => v
    _ => fail("expected int")
  }
}

///|
fn eval_float(stop : Node, parameter : Int64) -> Double raise {
  match Evaluator::evaluate(stop, parameter=parameter) {
    EvalValue::Float(v) => v
    _ => fail("expected float")
  }
}

///|
test "chapter12: jig" {
  let parser = Parser::new("return 3.14;\n")
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return 3.14;")
  assert_true(eval_float(stop, 0L).is_close(3.14, relative_tolerance=1.0e-12, absolute_tolerance=1.0e-12))
}

///|
test "chapter12: square root" {
  let parser = Parser::new(
    "flt guess = arg;\n" +
    "while( 1 ) {\n" +
    "    flt next = (arg/guess + guess)/2;\n" +
    "    if( next == guess ) break;\n" +
    "    guess = next;\n" +
    "}\n" +
    "return guess;\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(
    stop.print(),
    "return Phi(Loop10,(flt)arg,(((ToFloat/Phi_guess)+Phi_guess)/2.0));",
  )
  assert_true(eval_float(stop, 9L).is_close(3.0, relative_tolerance=1.0e-12, absolute_tolerance=1.0e-12))
  assert_true(
    eval_float(stop, 2L).is_close(
      1.414213562373095,
      relative_tolerance=1.0e-12,
      absolute_tolerance=1.0e-12,
    ),
  )
}

///|
test "chapter12: fp ops" {
  let parser = Parser::new(
    "flt x = arg;\n" +
    "return x+1==x;\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return ((flt)arg==(ToFloat+1.0));")
  assert_eq(eval_int12(stop, 1L), 0L)
}
