///|
test "chapter05: if stmt" {
  let parser = Parser::new(
    "int a = 1;\n" +
    "if (arg == 1)\n" +
    "    a = arg+2;\n" +
    "else {\n" +
    "    a = arg-3;\n" +
    "    #showGraph;\n" +
    "}\n" +
    "#showGraph;\n" +
    "return a;",
  )
  let stop = parser.parse(show=true)
  assert_eq(stop.print(), "return Phi(Region17,(arg+2),(arg-3));")
}

///|
test "chapter05: merge unused vars" {
  let parser = Parser::new_with_arg(
    "int c = 3;\n" +
    "int b = 2;\n" +
    "if (arg == 1) {\n" +
    "    b = 3;\n" +
    "    c = 4;\n" +
    "}\n" +
    "return c;",
    type_integer_bot,
  )
  let stop = parser.parse(show=true)
  assert_eq(stop.print(), "return Phi(Region16,4,3);")
}

///|
test "chapter05: multi return stop" {
  let parser = Parser::new_with_arg(
    "if( arg==1 )\n" +
    "    return 3;\n" +
    "else\n" +
    "    return 4;\n" +
    "#showGraph;",
    type_integer_bot,
  )
  let stop = parser.parse()
  assert_eq(stop.print(), "Stop[ return 3; return 4; ]")
}

///|
test "chapter05: if merge b" {
  let parser = Parser::new(
    "int a=arg+1;\n" +
    "int b=0;\n" +
    "if( arg==1 )\n" +
    "    b=a;\n" +
    "else\n" +
    "    b=a+1;\n" +
    "return a+b;",
  )
  let stop = parser.parse(show=true)
  assert_eq(stop.print(), "return ((arg*2)+Phi(Region20,2,3));")
}

///|
test "chapter05: if merge 2" {
  let parser = Parser::new(
    "int a=arg+1;\n" +
    "int b=arg+2;\n" +
    "if( arg==1 )\n" +
    "    b=b+a;\n" +
    "else\n" +
    "    a=b+1;\n" +
    "return a+b;",
  )
  let stop = parser.parse(show=true)
  assert_eq(
    stop.print(),
    "return ((Phi(Region31,(arg*2),arg)+arg)+Phi(Region31,4,5));",
  )
}

///|
test "chapter05: merge 3" {
  let parser = Parser::new_with_arg(
    "int a=1;\n" +
    "if( arg==1 )\n" +
    "    if( arg==2 )\n" +
    "        a=2;\n" +
    "    else\n" +
    "        a=3;\n" +
    "else if( arg==3 )\n" +
    "    a=4;\n" +
    "else\n" +
    "    a=5;\n" +
    "return a;\n" +
    "#showGraph;",
    type_integer_bot,
  )
  let stop = parser.parse()
  assert_eq(
    stop.print(),
    "return Phi(Region33,Phi(Region21,2,3),Phi(Region31,4,5));",
  )
}

///|
test "chapter05: merge 4" {
  let parser = Parser::new_with_arg(
    "int a=0;\n" +
    "int b=0;\n" +
    "if( arg )\n" +
    "    a=1;\n" +
    "if( arg==0 )\n" +
    "    b=2;\n" +
    "return arg+a+b;\n" +
    "#showGraph;",
    type_integer_bot,
  )
  let stop = parser.parse()
  assert_eq(stop.print(), "return ((arg+Phi(Region13,1,0))+Phi(Region22,2,0));")
}

///|
test "chapter05: merge 5" {
  let parser = Parser::new(
    "int a=arg==2;\n" +
    "if( arg==1 )\n" +
    "{\n" +
    "    a=arg==3;\n" +
    "}\n" +
    "return a;",
  )
  let stop = parser.parse(show=true)
  assert_eq(stop.print(), "return (arg==Phi(Region16,3,2));")
}

///|
test "chapter05: true literal" {
  let stop = Parser::new("return true;").parse()
  assert_eq(stop.print(), "return 1;")
}

///|
test "chapter05: half def" {
  expect_parse_error(
    "if( arg==1 ) int b=2; return b;", "Cannot define a new name on one arm of an if",
  )
}

///|
test "chapter05: half def2" {
  expect_parse_error(
    "if( arg==1 ) { int b=2; } else { int b=3; } return b;", "Undefined name 'b'",
  )
}

///|
test "chapter05: regress1" {
  expect_parse_error(
    "if(arg==2) int a=1; else int b=2; return a;", "Cannot define a new name on one arm of an if",
  )
}

///|
test "chapter05: bad num" {
  expect_parse_error(
    "return 1-;", "Syntax error, expected an identifier or expression: ;",
  )
}

///|
test "chapter05: keyword1" {
  expect_parse_error(
    "int true=0; return true;", "Expected an identifier, found 'true'",
  )
}

///|
test "chapter05: keyword2" {
  expect_parse_error(
    "int else=arg; if(else) else=2; else else=1; return else;", "Expected an identifier, found 'else'",
  )
}

///|
test "chapter05: keyword3" {
  expect_parse_error(
    "int a=1; ififif(arg)inta=2;return a;", "Syntax error, expected =: (",
  )
}
