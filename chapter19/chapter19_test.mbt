///|
test "chapter19: jig" {
  let code = CodeGen::new("return 0;")
  ignore(code.parse().opto().type_check())
  assert_eq(code.print(), "return 0;")
  assert_eq(Eval2::eval(code, 2L), "0")
}
