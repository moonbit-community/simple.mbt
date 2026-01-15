///|
test "chapter08: ex6" {
  let parser = Parser::new(
    "while(arg < 10) {\n" +
    "    arg = arg + 1;\n" +
    "    if (arg == 5)\n" +
    "        break;\n" +
    "    if (arg == 6)\n" +
    "        break;\n" +
    "}\n" +
    "return arg;\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(
    stop.print(),
    "return Phi(Region45,Phi(Region32,Phi(Loop10,arg,(Phi_arg+1)),Add),Add);",
  )
  let ret = stop.input_exn(0)
  assert_true(ret.ctrl().kind is Region)
  assert_eq(GraphEvaluator::evaluate(stop, parameter=1L), 5L)
  assert_eq(GraphEvaluator::evaluate(stop, parameter=6L), 10L)
}

///|
test "chapter08: ex5" {
  let parser = Parser::new(
    "int a = 1;\n" +
    "while(arg < 10) {\n" +
    "    arg = arg + 1;\n" +
    "    if (arg == 5)\n" +
    "        continue;\n" +
    "    if (arg == 7)\n" +
    "        continue;\n" +
    "    a = a + 1;\n" +
    "}\n" +
    "return a;\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return Phi(Loop11,1,Phi(Region52,Phi_a,(Phi_a+1)));")
  let ret = stop.input_exn(0)
  assert_true(ret.ctrl().kind is CProj)
}

///|
test "chapter08: ex4" {
  let parser = Parser::new(
    "while(arg < 10) {\n" +
    "    arg = arg + 1;\n" +
    "    if (arg == 5)\n" +
    "        continue;\n" +
    "    if (arg == 6)\n" +
    "        break;\n" +
    "}\n" +
    "return arg;\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(
    stop.print(),
    "return Phi(Region43,Phi(Loop10,arg,(Phi_arg+1)),Add);",
  )
  let ret = stop.input_exn(0)
  assert_true(ret.ctrl().kind is Region)
}

///|
test "chapter08: ex3" {
  let parser = Parser::new(
    "while(arg < 10) {\n" +
    "    arg = arg + 1;\n" +
    "    if (arg == 6)\n" +
    "        break;\n" +
    "}\n" +
    "return arg;\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(
    stop.print(),
    "return Phi(Region32,Phi(Loop10,arg,(Phi_arg+1)),Add);",
  )
  let ret = stop.input_exn(0)
  assert_true(ret.ctrl().kind is Region)
}

///|
test "chapter08: ex2" {
  let parser = Parser::new(
    "while(arg < 10) {\n" +
    "    arg = arg + 1;\n" +
    "    if (arg == 5)\n" +
    "        continue;\n" +
    "    if (arg == 6)\n" +
    "        continue;\n" +
    "}\n" +
    "return arg;\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return Phi(Loop10,arg,(Phi_arg+1));")
  let ret = stop.input_exn(0)
  assert_true(ret.ctrl().kind is CProj)
}

///|
test "chapter08: ex1" {
  let parser = Parser::new(
    "while(arg < 10) {\n" +
    "    arg = arg + 1;\n" +
    "    if (arg == 5)\n" +
    "        continue;\n" +
    "}\n" +
    "return arg;\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return Phi(Loop10,arg,(Phi_arg+1));")
  let ret = stop.input_exn(0)
  assert_true(ret.ctrl().kind is CProj)
}

///|
test "chapter08: regress1" {
  let parser = Parser::new(
    "while( arg < 10 ) {\n" +
    "    int a = arg+2;\n" +
    "    if( a > 4 )\n" +
    "        break;\n" +
    "}\n" +
    "return arg;\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return arg;")
}

///|
test "chapter08: regress2" {
  let parser = Parser::new(
    "if(1) return 0;  else while(arg>--arg) arg=arg+1; return 0;",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return 0;")
}

///|
test "chapter08: break outside loop" {
  expect_parse_error(
    "if(arg <= 10) {\n" +
    "    break;\n" +
    "    arg = arg + 1;\n" +
    "}\n" +
    "return arg;\n",
    "No active loop for a break or continue",
  )
}

///|
test "chapter08: regress3" {
  let parser = Parser::new(
    "while(arg < 10) {\n" + "    break;\n" + "}\n" + "return arg;\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return arg;")
}

///|
test "chapter08: regress4" {
  let parser = Parser::new(
    "int a = 1;\n" +
    "while(arg < 10) {\n" +
    "    a = a + 1;\n" +
    "    if (arg > 2) {\n" +
    "        int a = 17;\n" +
    "        break;\n" +
    "    }\n" +
    "}\n" +
    "return a;\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return Phi(Region35,Phi(Loop11,1,(Phi_a+1)),Add);")
  let ret = stop.input_exn(0)
  assert_true(ret.ctrl().kind is Region)
}

///|
test "chapter08: regress5" {
  let parser = Parser::new(
    "int a = 1;\n" +
    "while(1) {\n" +
    "    a = a + 1;\n" +
    "    if (a<10) continue;\n" +
    "    break;\n" +
    "}\n" +
    "return a;\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return (Phi(Loop11,1,Add)+1);")
  let ret = stop.input_exn(0)
  assert_true(ret.ctrl().kind is CProj)
  assert_eq(ret.ctrl()._proj_idx, 1)
}
