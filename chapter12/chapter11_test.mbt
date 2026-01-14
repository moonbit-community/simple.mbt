///|
fn eval_int(stop : Node, parameter : Int64) -> Int64 raise {
  match Evaluator::evaluate(stop, parameter=parameter) {
    EvalValue::Int(v) => v
    _ => fail("expected int")
  }
}

///|
test "chapter11: primes" {
  let parser = Parser::new(
    "if( arg < 2 ) return 0;\n" +
    "int primeCount = 1;\n" +
    "int prime = 3;\n" +
    "while( prime <= arg ) {\n" +
    "    int isPrime = 1;\n" +
    "    // Check for even case, so the next loop need only check odds\n" +
    "    if( (prime/2)*2 == prime )\n" +
    "        continue;\n" +
    "    // Check odds up to sqrt of prime\n" +
    "    int j = 3;\n" +
    "    while( j*j <= prime ) {\n" +
    "        if( (prime/j)*j == prime ) {\n" +
    "            isPrime = 0;\n" +
    "            break;\n" +
    "        }\n" +
    "        j = j + 2;\n" +
    "    }\n" +
    "    if( isPrime )\n" +
    "        primeCount = primeCount + 1;\n" +
    "    prime = prime + 2;\n" +
    "}\n" +
    "return primeCount;\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(
    stop.print(),
    "Stop[ return 0; return Phi(Loop20,1,Phi(Region82,Phi_primeCount,Phi(Region77,(Phi_primeCount+1),Phi_primeCount))); ]",
  )
  assert_eq(eval_int(stop, 1), 0L)
  assert_eq(eval_int(stop, 2), 1L)
  assert_eq(eval_int(stop, 3), 2L)
  assert_eq(eval_int(stop, 4), 2L)
  assert_eq(eval_int(stop, 5), 3L)
  assert_eq(eval_int(stop, 10), 4L)
}

///|
test "chapter11: anti deps 1" {
  let parser = Parser::new(
    "struct S { int f; }\n" +
    "S v=new S;\n" +
    "v.f = 2;\n" +
    "int i=new S.f;\n" +
    "i=v.f;\n" +
    "if (arg) v.f=1;\n" +
    "return i;\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return .f;")
}

///|
test "chapter11: anti deps 2" {
  let parser = Parser::new(
    "struct S { int f; }\n" +
    "S v = new S;\n" +
    "S t = new S;\n" +
    "int i = 0;\n" +
    "if (arg) {\n" +
    "    if (arg+1) v = t;\n" +
    "    i = v.f;\n" +
    "} else {\n" +
    "    v.f = 2;\n" +
    "}\n" +
    "return i;\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return Phi(Region34,.f,0);")
}

///|
test "chapter11: anti deps 3" {
  let parser = Parser::new(
    "struct S { int f; }\n" +
    "S v0 = new S;\n" +
    "S? v1;\n" +
    "if (arg) v1 = new S;\n" +
    "if (v1) {\n" +
    "    v0.f = v1.f;\n" +
    "} else {\n" +
    "    v0.f = 2;\n" +
    "}\n" +
    "return v0;\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return new S;")
}

///|
test "chapter11: anti deps 4" {
  let parser = Parser::new(
    "struct S { int f; }\n" +
    "S v = new S;\n" +
    "S t = new S;\n" +
    "int i = v.f;\n" +
    "if (arg+1) arg= 0;\n" +
    "while (arg) v.f = 2;\n" +
    "return i;\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return .f;")
}

///|
test "chapter11: anti deps 5" {
  let parser = Parser::new(
    "struct S { int f; }\n" +
    "S v = new S;\n" +
    "while(1) {\n" +
    "    while(arg+1) { arg=arg-1; }\n" +
    "    if (arg) break;\n" +
    "    v.f = 2;\n" +
    "}\n" +
    "return v;\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return new S;")
}

///|
test "chapter11: anti deps 6" {
  let parser = Parser::new(
    "struct s { int v; }\n" +
    "s ptr=new s;\n" +
    "while( -arg )\n" +
    "  ptr = new s;\n" +
    "while(1)\n" +
    "  arg = arg+ptr.v;\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return 0;")
}

///|
test "chapter11: anti deps 7" {
  let parser = Parser::new(
    "struct S { int f; }\n" +
    "S v = new S;\n" +
    "S t = new S;\n" +
    "int i = v.f;\n" +
    "while (arg) {\n" +
    "    v.f = arg;\n" +
    "    arg = arg-1;\n" +
    "}\n" +
    "return i;\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return .f;")
}

///|
test "chapter11: anti deps 8" {
  let parser = Parser::new(
    "struct S { int f; }\n" +
    "S v = new S;\n" +
    "S t = new S;\n" +
    "while(arg) {\n" +
    "    arg=arg-1;\n" +
    "    int f = v.f;\n" +
    "    v.f = 2;\n" +
    "    if (arg) arg = f;\n" +
    "    else v.f = 3;\n" +
    "}\n" +
    "return arg;\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return Phi(Loop16,arg,Phi(Region38,.f,0));")
}

///|
test "chapter11: anti deps 9" {
  let parser = Parser::new(
    "struct S { int f; }\n" +
    "S v = new S;\n" +
    "S t = new S;\n" +
    "if (arg) {\n" +
    "    v.f=2;\n" +
    "    int i=t.f;\n" +
    "    v.f=i;\n" +
    "}\n" +
    "return v;\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return new S;")
}

///|
test "chapter11: split" {
  let parser = Parser::new(
    "struct S { int f; }\n" +
    "S s = new S;\n" +
    "if( arg==0 ) s.f = 1;\n" +
    "else if (arg == 1) s.f = 1;\n" +
    "return s.f;\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return Phi(Region37,1,Phi(Region35,1,0));")
  assert_eq(eval_int(stop, 0), 1L)
  assert_eq(eval_int(stop, 1), 1L)
  assert_eq(eval_int(stop, 2), 0L)
}

///|
test "chapter11: schedule use" {
  let parser = Parser::new(
    "int v0=0;\n" +
    "while(0>=0) {\n" +
    "    int v1=0;\n" +
    "    v1=v0;\n" +
    "    if(v1*0)\n" +
    "        v0=-v1;\n" +
    "}\n" +
    "return 0;\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return 0;")
}

///|
test "chapter11: loop carried dep" {
  let parser = Parser::new(
    "int v0=0;\n" +
    "{\n" +
    "    int v1=0;\n" +
    "    while(v1) {\n" +
    "        v1=1+(v0!=0);\n" +
    "        v0=v1/0;\n" +
    "    }\n" +
    "}\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return 0;")
}
