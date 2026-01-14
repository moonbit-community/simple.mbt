///|
fn expect_parse_error(source : String, expected : String) -> Unit raise {
  let result : Result[Node, ParseError] = try? Parser::new(source).parse()
  match result {
    Err(ParseError::Msg(msg)) => assert_eq(msg, expected)
    Ok(_) => fail("expected ParseError")
  }
}

///|
test "chapter01: simple program" {
  let parser = Parser::new("return 1;")
  let ret = parser.parse()
  let start_node = start.val
  assert_true(start_node == ret.ctrl())
  let expr = ret.expr()
  match expr.kind {
    Constant => {
      assert_true(expr.input_exn(0) == start_node)
      assert_eq(expr._value, 1L)
    }
    _ => fail("expected Constant node")
  }
}

///|
test "chapter01: zero" {
  let parser = Parser::new("return 0;")
  ignore(parser.parse())
  let start_node = start.val
  for user_node in start_node._outputs {
    if user_node.kind is Constant {
      assert_eq(user_node._value, 0L)
    }
  }
}

///|
test "chapter01: bad1" {
  expect_parse_error("ret", "Syntax error, expected a statement: ret")
}

///|
test "chapter01: bad2" {
  expect_parse_error(
    "return 0123;", "Syntax error: integer values cannot start with '0'",
  )
}

///|
test "chapter01: bad3" {
  expect_parse_error("return --12;", "Syntax error, expected integer literal")
}

///|
test "chapter01: bad4" {
  expect_parse_error("return 100", "Syntax error, expected ;: ")
}

///|
test "chapter01: bad5" {
  expect_parse_error("return -100;", "Syntax error, expected integer literal")
}

///|
test "chapter01: bad6" {
  expect_parse_error(
    "return100", "Syntax error, expected a statement: return100",
  )
}

///|
test "chapter01: bad7" {
  expect_parse_error("return 1;}", "Syntax error, unexpected }")
}
