///|
test "chapter03: var decl" {
  let ret = Parser::new("int a=1; return a;").parse()
  assert_eq(ret.print(), "return 1;")
}

///|
test "chapter03: var add" {
  let ret = Parser::new("int a=1; int b=2; return a+b;").parse()
  assert_eq(ret.print(), "return 3;")
}

///|
test "chapter03: var scope" {
  let ret = Parser::new(
    "int a=1; int b=2; int c=0; { int b=3; c=a+b; } return c;",
  ).parse()
  assert_eq(ret.print(), "return 4;")
}

///|
test "chapter03: var scope no peephole" {
  let parser = Parser::new(
    "int a=1; int b=2; int c=0; { int b=3; c=a+b; } return c;",
  )
  disable_peephole.val = true
  let ret = parser.parse()
  disable_peephole.val = false
  assert_eq(ret.print(), "return (1+3);")
}

///|
test "chapter03: var dist" {
  let ret = Parser::new(
    "int x0=1; int y0=2; int x1=3; int y1=4; return (x0-x1)*(x0-x1) + (y0-y1)*(y0-y1);",
  ).parse()
  assert_eq(ret.print(), "return 8;")
}

///|
test "chapter03: self assign" {
  expect_parse_error("int a=a; return a;", "Undefined name 'a'")
}

///|
test "chapter03: redeclare var" {
  expect_parse_error(
    "int a=1; int b=2; int c=0; int b=3; c=a+b;", "Redefining name 'b'",
  )
}

///|
test "chapter03: bad missing close brace" {
  expect_parse_error(
    "int a=1; int b=2; int c=0; { int b=3; c=a+b;", "Syntax error, expected }: ",
  )
}
