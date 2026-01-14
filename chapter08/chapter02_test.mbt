///|
test "chapter02: parse grammar" {
  let parser = Parser::new("return 1+2*3+-5;")
  disable_peephole.val = true
  let ret = parser.parse()
  assert_eq(ret.print(), "return (1+((2*3)+(-5)));")
  disable_peephole.val = false
}

///|
test "chapter02: add peephole" {
  let ret = Parser::new("return 1+2;").parse()
  assert_eq(ret.print(), "return 3;")
}

///|
test "chapter02: sub peephole" {
  let ret = Parser::new("return 1-2;").parse()
  assert_eq(ret.print(), "return -1;")
}

///|
test "chapter02: mul peephole" {
  let ret = Parser::new("return 2*3;").parse()
  assert_eq(ret.print(), "return 6;")
}

///|
test "chapter02: div peephole" {
  let ret = Parser::new("return 6/3;").parse()
  assert_eq(ret.print(), "return 2;")
}

///|
test "chapter02: minus peephole" {
  let ret = Parser::new("return 6/-3;").parse()
  assert_eq(ret.print(), "return -2;")
}

///|
test "chapter02: example" {
  let ret = Parser::new("return 1+2*3+-5;").parse()
  assert_eq(ret.print(), "return 2;")
}
