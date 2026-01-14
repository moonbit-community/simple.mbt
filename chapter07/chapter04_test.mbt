///|
test "chapter04: peephole" {
  let ret = Parser::new("return 1+arg+2;").parse()
  assert_eq(ret.print(), "return (arg+3);")
}

///|
test "chapter04: peephole2" {
  let ret = Parser::new("return (1+arg)+2;").parse()
  assert_eq(ret.print(), "return (arg+3);")
}

///|
test "chapter04: add0" {
  let ret = Parser::new("return 0+arg;").parse()
  assert_eq(ret.print(), "return arg;")
}

///|
test "chapter04: add add mul" {
  let ret = Parser::new("return arg+0+arg;").parse()
  assert_eq(ret.print(), "return (arg*2);")
}

///|
test "chapter04: peephole3" {
  let ret = Parser::new("return 1+arg+2+arg+3;").parse()
  assert_eq(ret.print(), "return ((arg*2)+6);")
}

///|
test "chapter04: mul1" {
  let ret = Parser::new("return 1*arg;").parse()
  assert_eq(ret.print(), "return arg;")
}

///|
test "chapter04: var arg" {
  let parser = Parser::new("return arg;")
  let stop = parser.parse()
  let ret = stop.input_exn(0)
  assert_true(ret.input_exn(0).kind is Proj)
  assert_true(ret.input_exn(1).kind is Proj)
}

///|
test "chapter04: constant arg" {
  let parser = Parser::new_with_arg("return arg;", TypeInteger::constant(2L))
  let ret = parser.parse()
  assert_eq(ret.print(), "return 2;")
}

///|
test "chapter04: comp eq" {
  let ret = Parser::new("return 3==3;").parse()
  assert_eq(ret.print(), "return 1;")
}

///|
test "chapter04: comp eq2" {
  let ret = Parser::new("return 3==4;").parse()
  assert_eq(ret.print(), "return 0;")
}

///|
test "chapter04: comp neq" {
  let ret = Parser::new("return 3!=3;").parse()
  assert_eq(ret.print(), "return 0;")
}

///|
test "chapter04: comp neq2" {
  let ret = Parser::new("return 3!=4;").parse()
  assert_eq(ret.print(), "return 1;")
}

///|
test "chapter04: bug1" {
  let ret = Parser::new("int a=arg+1; int b=a; b=1; return a+2;").parse()
  assert_eq(ret.print(), "return (arg+3);")
}

///|
test "chapter04: bug2" {
  let ret = Parser::new("int a=arg+1; a=a; return a;").parse()
  assert_eq(ret.print(), "return (arg+1);")
}

///|
test "chapter04: bug3" {
  expect_parse_error("inta=1; return a;", "Undefined name 'inta'")
}

///|
test "chapter04: bug4" {
  let ret = Parser::new("return -arg;").parse()
  assert_eq(ret.print(), "return (-arg);")
}

///|
test "chapter04: bug5" {
  let ret = Parser::new("return arg--2;").parse()
  assert_eq(ret.print(), "return (arg--2);")
}
