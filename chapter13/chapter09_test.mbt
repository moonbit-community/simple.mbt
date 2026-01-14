///|
test "chapter09: gvn1" {
  let parser = Parser::new(
    "int x = arg + arg;\n" +
    "if(arg < 10) {\n" +
    "    return arg + arg;\n" +
    "}\n" +
    "else {\n" +
    "    x = x + 1;\n" +
    "}\n" +
    "return x;\n",
  )
  let stop = parser.parse(show=false)
  assert_eq(stop.print(), "Stop[ return (arg*2); return (Mul+1); ]")
  assert_eq(GraphEvaluator::evaluate(stop, parameter=1L), 2L)
  assert_eq(GraphEvaluator::evaluate(stop, parameter=11L), 23L)
}

///|
test "chapter09: gvn2" {
  let parser = Parser::new("return arg*arg-arg*arg;\n")
  let stop = parser.parse(show=false)
  assert_eq(stop.print(), "return 0;")
  assert_eq(GraphEvaluator::evaluate(stop, parameter=1L), 0L)
}

///|
test "chapter09: worklist1" {
  let parser = Parser::new(
    "int step = 1;\n" +
    "while (arg < 10) {\n" +
    "    arg = arg + step + 1;\n" +
    "}\n" +
    "return arg;\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return Phi(Loop10,arg,(Phi_arg+2));")
  assert_eq(GraphEvaluator::evaluate(stop, parameter=1L), 11L)
}

///|
test "chapter09: worklist2" {
  let parser = Parser::new(
    "int cond = 0;\n" +
    "int one = 1;\n" +
    "while (arg < 10) {\n" +
    "    if (cond) one = 2;\n" +
    "    arg = arg + one*3 + 1;\n" +
    "}\n" +
    "return arg;\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return Phi(Loop11,arg,(Phi_arg+4));")
  assert_eq(GraphEvaluator::evaluate(stop, parameter=1L), 13L)
}

///|
test "chapter09: worklist3" {
  let parser = Parser::new(
    "int v1 = 0;\n" +
    "int v2 = 0;\n" +
    "int v3 = 0;\n" +
    "int v4 = 0;\n" +
    "int v5 = 0;\n" +
    "int v6 = 0;\n" +
    "int v7 = 0;\n" +
    "int v8 = 0;\n" +
    "while (arg) {\n" +
    "    if (v1) v2 = 1;\n" +
    "    if (v2) v3 = 1;\n" +
    "    if (v3) v4 = 1;\n" +
    "    if (v4) v5 = 1;\n" +
    "    if (v5) v6 = 1;\n" +
    "    if (v6) v7 = 1;\n" +
    "    if (v7) v8 = 1;\n" +
    "    arg = arg + v8 + 1;\n" +
    "}\n" +
    "return arg;\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return Phi(Loop17,arg,(Phi_arg+1));")
}

///|
test "chapter09: region peep bug" {
  let parser = Parser::new(
    "int v0=0;\n" +
    "int v1=0;\n" +
    "while(v1+arg) {\n" +
    "    arg=0;\n" +
    "    int v2=v0;\n" +
    "    while(arg+1) {}\n" +
    "    v0=1;\n" +
    "    v1=v2;\n" +
    "}\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "Stop[ return 0; return 0; ]")
}

///|
test "chapter09: sccp" {
  let parser = Parser::new(
    "int x = 1;\n" +
    "int cnt = 5;\n" +
    "while (cnt) {\n" +
    "  cnt = cnt - 1;\n" +
    "  if (x == 0) {\n" +
    "    x = x + 1;\n" +
    "  }\n" +
    "}\n" +
    "return x;\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return Phi(Loop11,1,Phi(Region36,1,Phi_x));")
}

///|
test "chapter09: while0" {
  let parser = Parser::new("while(0) continue; if(0) arg=0;")
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return 0;")
}

///|
test "chapter09: while1" {
  let parser = Parser::new(
    "if(0) while(0) {\n" +
    "    int arg=arg;\n" +
    "    while(0) {}\n" +
    "}\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return 0;")
}

///|
test "chapter09: precedence" {
  let parser = Parser::new("return 3-1+2;")
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return 4;")
}

///|
test "chapter09: swap2" {
  let parser = Parser::new("return 1+(1+1);")
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return 3;")
}

///|
test "chapter09: fuzz0" {
  let parser = Parser::new(
    "int one = 1;\n" +
    "int a = 0;\n" +
    "int zero = 0;\n" +
    "while(arg) {\n" +
    "    a = -(one + a + 2);\n" +
    "    arg = arg + 1;\n" +
    "    one = one + zero;\n" +
    "}\n" +
    "return a;\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return Phi(Loop12,0,(-(Phi_a+3)));")
}

///|
test "chapter09: fuzz1" {
  let parser = Parser::new(
    "while(1) {}\n" +
    "while(arg) break;\n" +
    "while(arg) arg=0;\n" +
    "arg=0;\n" +
    "int v0=0!=0<-0;\n" +
    "return -0+0+0;\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return 0;")
}

///|
test "chapter09: fuzz2" {
  let parser = Parser::new("return 0+-0;")
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return 0;")
}

///|
test "chapter09: fuzz3" {
  let parser = Parser::new("int v0=0; while(0==69) while(v0) return 0;")
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return 0;")
}

///|
test "chapter09: fuzz4" {
  let parser = Parser::new(
    "while(1) {\n" +
    "    arg=0<=0;\n" +
    "    if(1<0) while(arg==-0) arg=arg-arg;\n" +
    "}\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return 0;")
}

///|
test "chapter09: fuzz5" {
  let parser = Parser::new(
    "{\n" +
    "    int v0=0;\n" +
    "    while(1)\n" +
    "            int v1=0--0;\n" +
    "    while(v0)\n" +
    "        break;\n" +
    "    while(-v0) {\n" +
    "        while(0+0+v0) continue;\n" +
    "        break;\n" +
    "    }\n" +
    "    if(-0!=-0+0+v0) while(0+0+0+0)\n" +
    "                break;\n" +
    "}\n" +
    "return 0!=0;\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return 0;")
}

///|
test "chapter09: fuzz6" {
  let parser = Parser::new(
    "int v0=0;\n" +
    "while(0==1) while(v0)\n" +
    "        v0=1+v0;\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return 0;")
}

///|
test "chapter09: fuzz7" {
  let parser = Parser::new(
    "while(1) {}\n" +
    "int v0=0;\n" +
    "while(v0)\n" +
    "    {}\n" +
    "int v1=0;\n" +
    "while(1)\n" +
    "        v1=1;\n" +
    "return v1+v0;\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return 0;")
}

///|
test "chapter09: fuzz8" {
  let parser = Parser::new("while(arg) arg = arg - 1;  return arg;")
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return Phi(Loop9,arg,(Phi_arg-1));")
}

///|
test "chapter09: meet" {
  let t1 = top
  let t2 = type_integer_top
  assert_eq(t1.meet(t2), type_integer_top)
  assert_eq(t2.meet(t1), type_integer_top)
  let t3 = bottom
  let t4 = type_integer_bot
  assert_eq(t3.meet(t4), bottom)
  assert_eq(t4.meet(t3), bottom)
}
