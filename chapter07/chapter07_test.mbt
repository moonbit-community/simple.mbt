///|
test "chapter07: example" {
  let parser = Parser::new(
    "while(arg < 10) {\n" + "    arg = arg + 1;\n" + "}\n" + "return arg;\n",
  )
  disable_peephole.val = true
  let stop = parser.parse(show=false)
  assert_eq(stop.print(), "return Phi(Loop6,arg,(Phi_arg+1));")
  let ret = stop.input_exn(0)
  assert_true(ret.ctrl().kind is Proj)
  disable_peephole.val = false
}

///|
test "chapter07: regression" {
  let parser = Parser::new(
    "int a = 1;\n" +
    "if(arg){}else{\n" +
    "    while(a < 10) {\n" +
    "        a = a + 1;\n" +
    "    }\n" +
    "}\n" +
    "return a;\n",
  )
  let stop = parser.parse(show=false)
  assert_eq(stop.print(), "return Phi(Region23,1,Phi(Loop11,1,(Phi_a+1)));")
}

///|
test "chapter07: while nested" {
  let parser = Parser::new(
    "int sum = 0;\n" +
    "int i = 0;\n" +
    "while(i < arg) {\n" +
    "    i = i + 1;\n" +
    "    int j = 0;\n" +
    "    while( j < arg ) {\n" +
    "        sum = sum + j;\n" +
    "        j = j + 1;\n" +
    "    }\n" +
    "}\n" +
    "return sum;\n",
  )
  let stop = parser.parse(show=false)
  assert_eq(
    stop.print(),
    "return Phi(Loop8,0,Phi(Loop21,Phi_sum,(Phi(Loop,0,(Phi_j+1))+Phi_sum)));",
  )
}

///|
test "chapter07: while scope" {
  let parser = Parser::new(
    "int a = 1;\n" +
    "int b = 2;\n" +
    "while(a < 10) {\n" +
    "    if (a == 2) a = 3;\n" +
    "    else b = 4;\n" +
    "}\n" +
    "return b;\n",
  )
  disable_peephole.val = true
  let stop = parser.parse(show=false)
  assert_eq(stop.print(), "return Phi(Loop8,2,Phi(Region27,Phi_b,4));")
  let ret = stop.input_exn(0)
  assert_true(ret.ctrl().kind is Proj)
  disable_peephole.val = false
}

///|
test "chapter07: while nested if and inc" {
  let parser = Parser::new(
    "int a = 1;\n" +
    "int b = 2;\n" +
    "while(a < 10) {\n" +
    "    if (a == 2) a = 3;\n" +
    "    else b = 4;\n" +
    "    b = b + 1;\n" +
    "    a = a + 1;\n" +
    "}\n" +
    "return b;\n",
  )
  let stop = parser.parse(show=false)
  assert_eq(stop.print(), "return Phi(Loop8,2,(Phi(Region27,Phi_b,4)+1));")
  let ret = stop.input_exn(0)
  assert_true(ret.ctrl().kind is Proj)
}

///|
test "chapter07: while" {
  let parser = Parser::new(
    "int a = 1;\n" +
    "while(a < 10) {\n" +
    "    a = a + 1;\n" +
    "    a = a + 2;\n" +
    "}\n" +
    "return a;\n",
  )
  disable_peephole.val = true
  let stop = parser.parse(show=false)
  assert_eq(stop.print(), "return Phi(Loop7,1,((Phi_a+1)+2));")
  let ret = stop.input_exn(0)
  assert_true(ret.ctrl().kind is Proj)
  disable_peephole.val = false
}

///|
test "chapter07: while peep" {
  let parser = Parser::new(
    "int a = 1;\n" +
    "while(a < 10) {\n" +
    "    a = a + 1;\n" +
    "    a = a + 2;\n" +
    "}\n" +
    "return a;\n",
  )
  let stop = parser.parse(show=false)
  assert_eq(stop.print(), "return Phi(Loop7,1,(Phi_a+3));")
  let ret = stop.input_exn(0)
  assert_true(ret.ctrl().kind is Proj)
}

///|
test "chapter07: while2" {
  let parser = Parser::new(
    "int a = 1;\n" + "while(arg) a = 2;\n" + "return a;\n",
  )
  disable_peephole.val = true
  let stop = parser.parse(show=false)
  assert_eq(stop.print(), "return Phi(Loop7,1,2);")
  let ret = stop.input_exn(0)
  assert_true(ret.ctrl().kind is Proj)
  disable_peephole.val = false
}

///|
test "chapter07: while2 peep" {
  let parser = Parser::new(
    "int a = 1;\n" + "while(arg) a = 2;\n" + "return a;\n",
  )
  let stop = parser.parse(show=false)
  assert_eq(stop.print(), "return Phi(Loop7,1,2);")
  let ret = stop.input_exn(0)
  assert_true(ret.ctrl().kind is Proj)
}

///|
test "chapter07: while3" {
  let parser = Parser::new(
    "int a = 1;\n" +
    "while(a < 10) {\n" +
    "    int b = a + 1;\n" +
    "    a = b + 2;\n" +
    "}\n" +
    "return a;\n",
  )
  disable_peephole.val = true
  let stop = parser.parse(show=false)
  assert_eq(stop.print(), "return Phi(Loop7,1,((Phi_a+1)+2));")
  let ret = stop.input_exn(0)
  assert_true(ret.ctrl().kind is Proj)
  disable_peephole.val = false
}

///|
test "chapter07: while3 peep" {
  let parser = Parser::new(
    "int a = 1;\n" +
    "while(a < 10) {\n" +
    "    int b = a + 1;\n" +
    "    a = b + 2;\n" +
    "}\n" +
    "return a;\n",
  )
  let stop = parser.parse(show=false)
  assert_eq(stop.print(), "return Phi(Loop7,1,(Phi_a+3));")
  let ret = stop.input_exn(0)
  assert_true(ret.ctrl().kind is Proj)
}

///|
test "chapter07: while4" {
  let parser = Parser::new(
    "int a = 1;\n" +
    "int b = 2;\n" +
    "while(a < 10) {\n" +
    "    int b = a + 1;\n" +
    "    a = b + 2;\n" +
    "}\n" +
    "return a;\n",
  )
  disable_peephole.val = true
  let stop = parser.parse(show=false)
  assert_eq(stop.print(), "return Phi(Loop8,1,((Phi_a+1)+2));")
  let ret = stop.input_exn(0)
  assert_true(ret.ctrl().kind is Proj)
  disable_peephole.val = false
}

///|
test "chapter07: while4 peep" {
  let parser = Parser::new(
    "int a = 1;\n" +
    "int b = 2;\n" +
    "while(a < 10) {\n" +
    "    int b = a + 1;\n" +
    "    a = b + 2;\n" +
    "}\n" +
    "return a;\n",
  )
  let stop = parser.parse(show=false)
  assert_eq(stop.print(), "return Phi(Loop8,1,(Phi_a+3));")
  let ret = stop.input_exn(0)
  assert_true(ret.ctrl().kind is Proj)
}
