///|
fn expect_codegen_error(source : String, expected : String) -> Unit raise {
  let result : Result[CodeGen, ParseError] = try? CodeGen::new(source).parse().opto()
  match result {
    Err(ParseError::Msg(msg)) => assert_eq(msg, expected)
    Ok(_) => fail("expected ParseError")
  }
}

///|
fn expect_type_error(source : String, expected : String) -> Unit raise {
  let result : Result[CodeGen, ParseError] =
    try? CodeGen::new(source).parse().opto().type_check()
  match result {
    Err(ParseError::Msg(msg)) => assert_eq(msg, expected)
    Ok(_) => fail("expected ParseError")
  }
}

///|
test "chapter19: jig" {
  let code = CodeGen::new("return 0;")
  ignore(code.parse().opto().type_check())
  assert_eq(code.print(), "return 0;")
  assert_eq(Eval2::eval(code, 2L), "0")
}

///|
test "chapter19: inst_select basic0" {
  let code = CodeGen::new("return 0;")
  ignore(
    code
    .parse()
    .opto()
    .type_check()
    .inst_select("x86_64_v2", "SystemV")
    .gcm()
    .local_sched(),
  )
  assert_eq(code.print(), "return 0;")
}

///|
test "chapter19: inst_select basic1" {
  let code = CodeGen::new("return arg+1;")
  ignore(
    code
    .parse()
    .opto()
    .type_check()
    .inst_select("x86_64_v2", "SystemV")
    .gcm()
    .local_sched(),
  )
  assert_eq(code.print(), "return (inc,arg);")
}

///|
test "chapter19: inst_select basic2" {
  let code = CodeGen::new("return -17;")
  ignore(
    code
    .parse()
    .opto()
    .type_check()
    .inst_select("x86_64_v2", "SystemV")
    .gcm()
    .local_sched(),
  )
  assert_eq(code.print(), "return -17;")
}

///|
test "chapter19: inst_select basic3" {
  let code = CodeGen::new("return arg==1;")
  ignore(
    code
    .parse()
    .opto()
    .type_check()
    .inst_select("x86_64_v2", "SystemV")
    .gcm()
    .local_sched(),
  )
  assert_eq(code.print(), "return (set==,(cmp,arg));")
}

///|
test "chapter19: inst_select basic4" {
  let code = CodeGen::new("return arg<<1;")
  ignore(
    code
    .parse()
    .opto()
    .type_check()
    .inst_select("x86_64_v2", "SystemV")
    .gcm()
    .local_sched(),
  )
  assert_eq(code.print(), "return (shli,arg);")
}

///|
test "chapter19: inst_select basic5" {
  let code = CodeGen::new("return arg >> 1;")
  ignore(
    code
    .parse()
    .opto()
    .type_check()
    .inst_select("x86_64_v2", "SystemV")
    .gcm()
    .local_sched(),
  )
  assert_eq(code.print(), "return (sari,arg);")
}

///|
test "chapter19: inst_select basic6" {
  let code = CodeGen::new("return arg >>> 1;")
  ignore(
    code
    .parse()
    .opto()
    .type_check()
    .inst_select("x86_64_v2", "SystemV")
    .gcm()
    .local_sched(),
  )
  assert_eq(code.print(), "return (shri,arg);")
}

///|
test "chapter19: inst_select basic7" {
  let code = CodeGen::new("return arg / 2;")
  ignore(
    code
    .parse()
    .opto()
    .type_check()
    .inst_select("x86_64_v2", "SystemV")
    .gcm()
    .local_sched(),
  )
  assert_eq(code.print(), "return (div,arg,2);")
}

///|
test "chapter19: inst_select basic8" {
  let code = CodeGen::new("return arg * 6;")
  ignore(
    code
    .parse()
    .opto()
    .type_check()
    .inst_select("x86_64_v2", "SystemV")
    .gcm()
    .local_sched(),
  )
  assert_eq(code.print(), "return (muli,arg);")
}

///|
test "chapter19: inst_select basic9" {
  let code = CodeGen::new("return arg & 2;")
  ignore(
    code
    .parse()
    .opto()
    .type_check()
    .inst_select("x86_64_v2", "SystemV")
    .gcm()
    .local_sched(),
  )
  assert_eq(code.print(), "return (andi,arg);")
}

///|
test "chapter19: inst_select basic10" {
  let code = CodeGen::new("return arg | 2;")
  ignore(
    code
    .parse()
    .opto()
    .type_check()
    .inst_select("x86_64_v2", "SystemV")
    .gcm()
    .local_sched(),
  )
  assert_eq(code.print(), "return (ori,arg);")
}

///|
test "chapter19: inst_select basic11" {
  let code = CodeGen::new("return arg ^ 2;")
  ignore(
    code
    .parse()
    .opto()
    .type_check()
    .inst_select("x86_64_v2", "SystemV")
    .gcm()
    .local_sched(),
  )
  assert_eq(code.print(), "return (xori,arg);")
}

///|
test "chapter19: inst_select basic12" {
  let code = CodeGen::new("return arg + 2.0;")
  ignore(
    code
    .parse()
    .opto()
    .type_check()
    .inst_select("x86_64_v2", "SystemV")
    .gcm()
    .local_sched(),
  )
  assert_eq(code.print(), "return (addf,(i2f8,arg),2.0f);")
}

///|
test "chapter19: inst_select basic13" {
  let code = CodeGen::new("return arg - 2.0;")
  ignore(
    code
    .parse()
    .opto()
    .type_check()
    .inst_select("x86_64_v2", "SystemV")
    .gcm()
    .local_sched(),
  )
  assert_eq(code.print(), "return (subf,(i2f8,arg),2.0f);")
}

///|
test "chapter19: inst_select basic14" {
  let code = CodeGen::new("return arg * 2.0;")
  ignore(
    code
    .parse()
    .opto()
    .type_check()
    .inst_select("x86_64_v2", "SystemV")
    .gcm()
    .local_sched(),
  )
  assert_eq(code.print(), "return (mulf,(i2f8,arg),2.0f);")
}

///|
test "chapter19: inst_select basic15" {
  let code = CodeGen::new("return arg / 2.0;")
  ignore(
    code
    .parse()
    .opto()
    .type_check()
    .inst_select("x86_64_v2", "SystemV")
    .gcm()
    .local_sched(),
  )
  assert_eq(code.print(), "return (divf,(i2f8,arg),2.0f);")
}

///|
test "chapter19: inst_select basic16" {
  let code = CodeGen::new(
    "int arg1 =  arg + 1;\n" +
    "return arg1 / arg;",
  )
  ignore(
    code
    .parse()
    .opto()
    .type_check()
    .inst_select("x86_64_v2", "SystemV")
    .gcm()
    .local_sched(),
  )
  assert_eq(code.print(), "return (div,(inc,arg),arg);")
}

///|
test "chapter19: inst_select basic17" {
  let code = CodeGen::new(
    "int arg1 =  arg + 1;\n" +
    "return arg1 * arg;\n",
  )
  ignore(
    code
    .parse()
    .opto()
    .type_check()
    .inst_select("x86_64_v2", "SystemV")
    .gcm()
    .local_sched(),
  )
  assert_eq(code.print(), "return (mul,(inc,arg),arg);")
}

///|
test "chapter19: inst_select basic18" {
  let code = CodeGen::new(
    "int arg1 =  arg + 1;\n" +
    "return arg1 << arg;\n",
  )
  ignore(
    code
    .parse()
    .opto()
    .type_check()
    .inst_select("x86_64_v2", "SystemV")
    .gcm()
    .local_sched(),
  )
  assert_eq(code.print(), "return (shl,(inc,arg),arg);")
}

///|
test "chapter19: inst_select basic19" {
  let code = CodeGen::new(
    "int arg1 =  arg + 1;\n" +
    "return arg1 >> arg;\n",
  )
  ignore(
    code
    .parse()
    .opto()
    .type_check()
    .inst_select("x86_64_v2", "SystemV")
    .gcm()
    .local_sched(),
  )
  assert_eq(code.print(), "return (sar,(inc,arg),arg);")
}

///|
test "chapter19: inst_select basic20" {
  let code = CodeGen::new(
    "int arg1 =  arg + 1;\n" +
    "return arg1 >>> arg;\n",
  )
  ignore(
    code
    .parse()
    .opto()
    .type_check()
    .inst_select("x86_64_v2", "SystemV")
    .gcm()
    .local_sched(),
  )
  assert_eq(code.print(), "return (shr,(inc,arg),arg);")
}

///|
test "chapter19: inst_select if stmt" {
  let code = CodeGen::new(
    "int a = 1;\n" +
    "if (arg == 1)\n" +
    "    a = arg+2;\n" +
    "else {\n" +
    "    a = arg-3;\n" +
    "}\n" +
    "return a;",
  )
  ignore(
    code
    .parse()
    .opto()
    .type_check()
    .inst_select("x86_64_v2", "SystemV")
    .gcm()
    .local_sched(),
  )
  assert_eq(code.print(), "return Phi(Region,(addi,arg),(addi,arg));")
}

///|
test "chapter19: inst_select lea1" {
  let code = CodeGen::new("int x = arg/3; return arg+x+7;")
  ignore(
    code
    .parse()
    .opto()
    .type_check()
    .inst_select("x86_64_v2", "SystemV")
    .gcm()
    .local_sched(),
  )
  assert_eq(code.print(), "return (lea,arg,(div,arg,3));")
}

///|
test "chapter19: inst_select lea2" {
  let code = CodeGen::new("int x = arg/3; return arg+x*4+7;")
  ignore(
    code
    .parse()
    .opto()
    .type_check()
    .inst_select("x86_64_v2", "SystemV")
    .gcm()
    .local_sched(),
  )
  assert_eq(code.print(), "return (lea,arg,(div,arg,3));")
}

///|
test "chapter19: inst_select lea3" {
  let code = CodeGen::new("int x = arg/3; return x*4+arg;")
  ignore(
    code
    .parse()
    .opto()
    .type_check()
    .inst_select("x86_64_v2", "SystemV")
    .gcm()
    .local_sched(),
  )
  assert_eq(code.print(), "return (lea,arg,(div,arg,3));")
}

///|
test "chapter19: phi parallel assign" {
  let code = CodeGen::new(
    "int a = 1;\n" +
    "int b = 2;\n" +
    "while(arg--) {\n" +
    "  int t = a;\n" +
    "  a = b;\n" +
    "  b = t;\n" +
    "}\n" +
    "return a;\n",
  )
  ignore(code.parse().opto().type_check().gcm())
  assert_eq(code.print(), "return Phi(Loop,1,Phi(Loop,2,Phi_a));")
  assert_eq(Eval2::eval(code, 0L), "1")
  assert_eq(Eval2::eval(code, 1L), "2")
  assert_eq(Eval2::eval(code, 2L), "1")
  assert_eq(Eval2::eval(code, 3L), "2")
}

///|
test "chapter19: type0" {
  let code = CodeGen::new(
    "{int -> int}? x2 = null; // null function ptr\n" +
    "return x2;\n",
  )
  ignore(code.parse().opto())
  assert_eq(code.print(), "return null;")
  assert_eq(Eval2::eval(code, 0L), "null")
}

///|
test "chapter19: fcn0" {
  let code = CodeGen::new(
    "{int -> int}? sq = { int x ->\n" +
    "    x*x;\n" +
    "};\n" +
    "return sq;\n",
  )
  ignore(code.parse().opto())
  assert_eq(code.print(), "Stop[ return { sq}; return (Parm_x(sq,int)*x); ]")
  assert_eq(Eval2::eval(code, 3L), "{ int -> int #1}")
}

///|
test "chapter19: fcn1" {
  let code = CodeGen::new(
    "var sq = { int x ->\n" +
    "    x*x;\n" +
    "};\n" +
    "return sq(arg)+sq(3);\n",
  )
  ignore(code.parse().opto().type_check().gcm().local_sched())
  assert_eq(
    code.print(),
    "Stop[ return (sq( 3)+sq( arg)); return (Parm_x(sq,int,3,arg)*x); ]",
  )
  assert_eq(Eval2::eval(code, 2L), "13")
}

///|
test "chapter19: fcn2" {
  expect_codegen_error(
    "int cnt=1;\n" + "return { -> cnt; };\n",
    "Variable 'cnt' is out of function scope and must be a final constant",
  )
}

///|
test "chapter19: fcn3" {
  let code = CodeGen::new("val cnt=2;\nreturn { -> cnt; }();\n")
  ignore(code.parse().opto())
  assert_eq(code.print(), "return 2;")
  assert_eq(Eval2::eval(code, 0L), "2")
}

///|
test "chapter19: fcn4" {
  let code = CodeGen::new(
    "var fcn = arg ? { int x -> x*x; } : { int x -> x+x; };\n" +
    "return fcn(3);\n",
  )
  ignore(code.parse().opto())
  assert_eq(
    code.print(),
    "Stop[ return Phi(Region,{ int -> int #1},{ int -> int #2})( 3); return (Parm_x($fun,int,3)*x); return (Parm_x($fun,int,3)<<1); ]",
  )
  assert_eq(Eval2::eval(code, 0L), "6")
  assert_eq(Eval2::eval(code, 1L), "9")
}

///|
test "chapter19: fcn5" {
  let code = CodeGen::new(
    "val fact = { int x -> x <= 1 ? 1 : x*fact(x-1); };\n" +
    "return fact(arg);\n",
  )
  ignore(code.parse().opto().type_check())
  assert_eq(
    code.print(),
    "Stop[ return fact( arg); return Phi(Region,1,(Parm_x(fact,int,arg,(x-1))*fact( Sub))); ]",
  )
  assert_eq(Eval2::eval(code, 0L), "1")
  assert_eq(Eval2::eval(code, 1L), "1")
  assert_eq(Eval2::eval(code, 2L), "2")
  assert_eq(Eval2::eval(code, 3L), "6")
  assert_eq(Eval2::eval(code, 4L), "24")
}

///|
test "chapter19: fcn6" {
  let code = CodeGen::new(
    "struct S { int i; };\n" +
    "val newS = { int x -> return new S { i=x; }; };\n" +
    "return newS(1).i;\n",
  )
  ignore(code.parse().opto().type_check().gcm())
  assert_eq(code.print(), "return 1;")
  assert_eq(Eval2::eval(code, 0L), "1")
}

///|
test "chapter19: fcn7" {
  let code = CodeGen::new(
    "if( arg ? f : g ) return 1;\n" +
    "val f = {->1;};\n" +
    "val g = {->2;};\n" +
    "return 2;\n",
  )
  ignore(code.parse().opto().type_check().gcm())
  assert_eq(code.print(), "Stop[ return 1; return 1; return 2; ]")
  assert_eq(Eval2::eval(code, 0L), "1")
}

///|
test "chapter19: fcn8" {
  let code = CodeGen::new(
    "{int -> int}? i2i = null;\n" +
    "var id = {{int->int} f-> return f;};\n" +
    "for(;;) {\n" +
    "    if (i2i) return i2i(arg);\n" +
    "    var x = {int i-> return i;};\n" +
    "    arg = x(3);\n" +
    "    i2i = id(x);\n" +
    "}\n",
  )
  ignore(code.parse().opto().type_check().gcm().local_sched())
  assert_eq(
    code.print(),
    "Stop[ return x( Phi(Loop,arg,x( 3))); return Parm_i(x,int,3,Phi_arg); ]",
  )
  assert_eq(Eval2::eval(code, 0L), "3")
}

///|
test "chapter19: fcn9" {
  let code = CodeGen::new(
    "{int -> int}? i2i = null;\n" +
    "for(;;) {\n" +
    "    if (i2i) return i2i(arg);\n" +
    "    var x = {int i-> return i;};\n" +
    "    arg = x(3);\n" +
    "}\n",
  )
  ignore(code.parse().opto().type_check().gcm().local_sched())
  assert_eq(code.print(), "return Top;")
  assert_eq(Eval2::eval(code, 0L), "null")
}

///|
test "chapter19: fcn10" {
  let code = CodeGen::new(
    "struct Person {\n" +
    "  int age;\n" +
    "};\n" +
    "\n" +
    "val fcn = { Person?[] ps, int x ->\n" +
    "  val tmp = ps[x];\n" +
    "  if( ps[x] )\n" +
    "    ps[x].age++;\n" +
    "};\n" +
    "\n" +
    "var ps = new Person?[2];\n" +
    "ps[0] = new Person;\n" +
    "ps[1] = new Person;\n" +
    "fcn(ps,1);\n",
  )
  ignore(code.parse().opto().type_check().gcm().local_sched())
  assert_eq(code.print(), "return 0;")
  assert_eq(Eval2::eval(code, 0L), "0")
}

///|
test "chapter19: err1" {
  expect_codegen_error(
    "for(;;) {\n" +
    "    val f = { ->\n" +
    "        break;\n" +
    "    };\n" +
    "    f();\n" +
    "    return 2;\n" +
    "}\n" +
    "return 1;\n",
    "No active loop for a break or continue",
  )
}

///|
test "chapter19: err2" {
  expect_type_error(
    "{int -> int}? !i2i = { int i -> return i; };\n" +
    "for(;;) {\n" +
    "    if (i2i(2) == arg) break;\n" +
    "    i2i = null;\n" +
    "}\n",
    "Might be null calling { int -> int #1}?",
  )
}

///|
test "chapter19: err3" {
  expect_type_error(
    "val f = { int i, int j -> return i+j; };\n" +
    "return f();\n",
    "Expecting 2 arguments, but found 0",
  )
}

///|
test "chapter19: err4" {
  expect_type_error(
    "struct S {\n" +
    "    {int} f = { -> x(); return 0; }; // Do not let fref x be a field\n" +
    "};\n" +
    "val x = { -> return 1; };\n" +
    "S? s = null;\n" +
    "for(;;) {\n" +
    "    if (s) return s.x;\n" +
    "}\n",
    "Accessing unknown field 'x' from '*S'",
  )
}

///|
test "chapter19: err5" {
  expect_type_error(
    "val g = { ->\n" +
    "    g();\n" +
    "};\n" +
    "return 0;\n",
    "No defined return type",
  )
}

///|
test "chapter19: inline" {
  let code = CodeGen::new(
    "{int->int}?! i2i = {int i->return i;};\n" +
    "{{int->int}->{int->int}}! f2f = {{int->int} f->return f;};\n" +
    "val o = i2i;\n" +
    "if (arg) i2i = null;\n" +
    "if (i2i) return i2i(arg);\n" +
    "return f2f(o)(1);\n",
  )
  ignore(code.parse().opto().type_check().gcm().local_sched())
  assert_eq(
    code.print(),
    "Stop[ return Phi(Region,o( arg),o( 1)); return Parm_i(o,int,arg,1); ]",
  )
  assert_eq(Eval2::eval(code, 2L), "1")
}

///|
test "chapter19: oper field" {
  let code = CodeGen::new(
    "struct Person {\n" +
    "    int coffee_count;\n" +
    "};\n" +
    "Person !p = new Person;\n" +
    "p.coffee_count += 1;\n" +
    "return p.coffee_count;\n",
  )
  ignore(code.parse().opto().type_check().gcm().local_sched())
  assert_eq(code.print(), "return 1;")
  assert_eq(Eval2::eval(code, 2L), "1")
}
