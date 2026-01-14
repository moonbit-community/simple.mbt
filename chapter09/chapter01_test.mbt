///|
fn expect_parse_error(source : String, expected : String) -> Unit raise {
  let result : Result[Node, ParseError] = try? Parser::new(source).parse()
  match result {
    Err(ParseError::Msg(msg)) => assert_eq(msg, expected)
    Ok(_) => fail("expected ParseError")
  }
}

///|
fn expect_type(node : Node, expected : Type) -> Unit raise {
  match node._type {
    Some(t) => assert_eq(t, expected)
    None => fail("expected node type")
  }
}

///|
test "chapter02: chapter01 simple program" {
  let parser = Parser::new("return 1;")
  let stop = parser.parse()
  let ret = stop.input_exn(0)
  let start_node = start.val
  assert_true(ret.ctrl().kind is Proj)
  let expr = ret.expr()
  if expr.kind is Constant {
    assert_true(expr.input_exn(0) == start_node)
    expect_type(expr, TypeInteger::constant(1L))
  } else {
    fail("expected Constant node")
  }
}

///|
test "chapter02: chapter01 zero" {
  let parser = Parser::new("return 0;")
  ignore(parser.parse())
  let start_node = start.val
  for user_node in start_node._outputs {
    match user_node {
      Some(n) if n.kind is Constant => expect_type(n, TypeInteger::constant(0L))
      _ => ()
    }
  }
}

///|
test "chapter02: chapter01 bad1" {
  expect_parse_error("ret", "Syntax error, expected =: ")
}

///|
test "chapter02: chapter01 bad2" {
  expect_parse_error(
    "return 0123;", "Syntax error: integer values cannot start with '0'",
  )
}

///|
test "chapter02: chapter01 not bad3" {
  assert_eq(Parser::new("return --12;").parse().print(), "return 12;")
}

///|
test "chapter02: chapter01 bad4" {
  expect_parse_error("return 100", "Syntax error, expected ;: ")
}

///|
test "chapter02: chapter01 not bad5" {
  assert_eq(Parser::new("return -100;").parse().print(), "return -100;")
}

///|
test "chapter02: chapter01 bad6" {
  expect_parse_error("return100", "Syntax error, expected =: ")
}

///|
test "chapter02: chapter01 bad7" {
  expect_parse_error("return 1;}", "Syntax error, unexpected }")
}
