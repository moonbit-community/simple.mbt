///|
test "chapter06: peephole return" {
  let parser = Parser::new("if( true ) return 2;\nreturn 1;\n")
  let stop = parser.parse(show=false)
  assert_eq(stop.print(), "return 2;")
  let ret = stop.input_exn(0)
  assert_true(ret.ctrl().kind is Proj)
}

///|
test "chapter06: peephole rotate" {
  let parser = Parser::new(
    "int a = 1;\n" + "if (arg)\n" + "    a = 2;\n" + "return (arg < a) < 3;\n",
  )
  let stop = parser.parse(show=false)
  assert_eq(stop.print(), "return ((arg<Phi(Region12,2,1))<3);")
}

///|
test "chapter06: peephole cfg" {
  let parser = Parser::new(
    "int a=1;\n" +
    "if( true )\n" +
    "  a=2;\n" +
    "else\n" +
    "  a=3;\n" +
    "return a;\n",
  )
  let stop = parser.parse(show=false)
  assert_eq(stop.print(), "return 2;")
  let ret = stop.input_exn(0)
  assert_true(ret.ctrl().kind is Proj)
}

///|
test "chapter06: if if" {
  let parser = Parser::new_with_arg(
    "int a=1;\n" +
    "if( arg!=1 )\n" +
    "    a=2;\n" +
    "else\n" +
    "    a=3;\n" +
    "int b=4;\n" +
    "if( a==2 )\n" +
    "    b=42;\n" +
    "else\n" +
    "    b=5;\n" +
    "return b;",
    type_integer_bot,
  )
  let stop = parser.parse(show=false)
  assert_eq(stop.print(), "return Phi(Region32,42,5);")
}

///|
test "chapter06: if arg if" {
  let parser = Parser::new_with_arg(
    "int a=1;\n" +
    "if( 1==1 )\n" +
    "    a=2;\n" +
    "else\n" +
    "    a=3;\n" +
    "int b=4;\n" +
    "if( arg==2 )\n" +
    "    b=a;\n" +
    "else\n" +
    "    b=5;\n" +
    "return b;",
    type_integer_bot,
  )
  let stop = parser.parse(show=false)
  assert_eq(stop.print(), "return Phi(Region28,2,5);")
}

///|
test "chapter06: merge3 with arg2" {
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
    "return a;\n",
    TypeInteger::constant(2L),
  )
  let stop = parser.parse()
  assert_eq(stop.print(), "return 5;")
}

///|
test "chapter06: merge3 with arg1" {
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
    "return a;\n",
    TypeInteger::constant(1L),
  )
  let stop = parser.parse(show=false)
  assert_eq(stop.print(), "return 3;")
}

///|
test "chapter06: merge3 peephole" {
  let parser = Parser::new_with_arg(
    "int a=1;\n" +
    "if( arg==1 )\n" +
    "    if( 1==2 )\n" +
    "        a=2;\n" +
    "    else\n" +
    "        a=3;\n" +
    "else if( arg==3 )\n" +
    "    a=4;\n" +
    "else\n" +
    "    a=5;\n" +
    "return a;\n",
    type_integer_bot,
  )
  let stop = parser.parse(show=false)
  assert_eq(stop.print(), "return Phi(Region36,3,Phi(Region34,4,5));")
}

///|
test "chapter06: merge3 peephole arg1" {
  let parser = Parser::new_with_arg(
    "int a=1;\n" +
    "if( arg==1 )\n" +
    "    if( 1==2 )\n" +
    "        a=2;\n" +
    "    else\n" +
    "        a=3;\n" +
    "else if( arg==3 )\n" +
    "    a=4;\n" +
    "else\n" +
    "    a=5;\n" +
    "return a;\n",
    TypeInteger::constant(1L),
  )
  let stop = parser.parse(show=false)
  assert_eq(stop.print(), "return 3;")
}

///|
test "chapter06: merge3 peephole arg3" {
  let parser = Parser::new_with_arg(
    "int a=1;\n" +
    "if( arg==1 )\n" +
    "    if( 1==2 )\n" +
    "        a=2;\n" +
    "    else\n" +
    "        a=3;\n" +
    "else if( arg==3 )\n" +
    "    a=4;\n" +
    "else\n" +
    "    a=5;\n" +
    "return a;\n",
    TypeInteger::constant(3L),
  )
  let stop = parser.parse(show=false)
  assert_eq(stop.print(), "return 4;")
}

///|
test "chapter06: demo1 non const" {
  let parser = Parser::new(
    "int a = 0;\n" +
    "int b = 1;\n" +
    "if( arg ) {\n" +
    "    a = 2;\n" +
    "    if( arg ) { b = 2; }\n" +
    "    else b = 3;\n" +
    "}\n" +
    "return a+b;\n",
  )
  let stop = parser.parse(show=false)
  assert_eq(stop.print(), "return Phi(Region22,4,1);")
}

///|
test "chapter06: demo1 true" {
  let parser = Parser::new_with_arg(
    "int a = 0;\n" +
    "int b = 1;\n" +
    "if( arg ) {\n" +
    "    a = 2;\n" +
    "    if( arg ) { b = 2; }\n" +
    "    else b = 3;\n" +
    "}\n" +
    "return a+b;\n",
    TypeInteger::constant(1L),
  )
  let stop = parser.parse(show=false)
  assert_eq(stop.print(), "return 4;")
}

///|
test "chapter06: demo1 false" {
  let parser = Parser::new_with_arg(
    "int a = 0;\n" +
    "int b = 1;\n" +
    "if( arg ) {\n" +
    "    a = 2;\n" +
    "    if( arg ) { b = 2; }\n" +
    "    else b = 3;\n" +
    "}\n" +
    "return a+b;\n",
    TypeInteger::constant(0L),
  )
  let stop = parser.parse(show=false)
  assert_eq(stop.print(), "return 1;")
}

///|
test "chapter06: demo2 non const" {
  let parser = Parser::new(
    "int a = 0;\n" +
    "int b = 1;\n" +
    "int c = 0;\n" +
    "if( arg ) {\n" +
    "    a = 1;\n" +
    "    if( arg==2 ) { c=2; } else { c=3; }\n" +
    "    if( arg ) { b = 2; }\n" +
    "    else b = 3;\n" +
    "}\n" +
    "return a+b+c;\n",
  )
  let stop = parser.parse(show=false)
  assert_eq(
    stop.print(),
    "return (Phi(Region33,Phi(Region22,2,3),0)+Phi(Region,3,1));",
  )
}

///|
test "chapter06: demo2 true" {
  let parser = Parser::new_with_arg(
    "int a = 0;\n" +
    "int b = 1;\n" +
    "int c = 0;\n" +
    "if( arg ) {\n" +
    "    a = 1;\n" +
    "    if( arg==2 ) { c=2; } else { c=3; }\n" +
    "    if( arg ) { b = 2; }\n" +
    "    else b = 3;\n" +
    "}\n" +
    "return a+b+c;\n",
    TypeInteger::constant(1L),
  )
  let stop = parser.parse(show=false)
  assert_eq(stop.print(), "return 6;")
}

///|
test "chapter06: demo2 arg2" {
  let parser = Parser::new_with_arg(
    "int a = 0;\n" +
    "int b = 1;\n" +
    "int c = 0;\n" +
    "if( arg ) {\n" +
    "    a = 1;\n" +
    "    if( arg==2 ) { c=2; } else { c=3; }\n" +
    "    if( arg ) { b = 2; }\n" +
    "    else b = 3;\n" +
    "}\n" +
    "return a+b+c;\n",
    TypeInteger::constant(2L),
  )
  let stop = parser.parse(show=false)
  assert_eq(stop.print(), "return 5;")
}
