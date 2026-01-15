///|
test "chapter21: jig" {
  let code = CodeGen::new("return 0;")
  ignore(code.parse().opto().type_check())
  assert_eq(code.print(), "return 0;")
  assert_eq(Eval2::eval(code, 2L), "0")
}

///|
test "chapter21: inst_select basic0" {
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
test "chapter21: inst_select basic1" {
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
test "chapter21: inst_select basic2" {
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
test "chapter21: inst_select basic3" {
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
test "chapter21: inst_select basic4" {
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
test "chapter21: inst_select basic5" {
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
test "chapter21: inst_select basic6" {
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
test "chapter21: inst_select basic7" {
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
test "chapter21: inst_select basic8" {
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
test "chapter21: inst_select basic9" {
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
test "chapter21: inst_select basic10" {
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
test "chapter21: inst_select basic11" {
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
test "chapter21: inst_select basic12" {
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
test "chapter21: inst_select basic13" {
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
test "chapter21: inst_select basic14" {
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
test "chapter21: inst_select basic15" {
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
test "chapter21: inst_select basic16" {
  let code = CodeGen::new("int arg1 =  arg + 1;\n" + "return arg1 / arg;")
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
test "chapter21: inst_select basic17" {
  let code = CodeGen::new("int arg1 =  arg + 1;\n" + "return arg1 * arg;\n")
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
test "chapter21: inst_select basic18" {
  let code = CodeGen::new("int arg1 =  arg + 1;\n" + "return arg1 << arg;\n")
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
test "chapter21: inst_select basic19" {
  let code = CodeGen::new("int arg1 =  arg + 1;\n" + "return arg1 >> arg;\n")
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
test "chapter21: inst_select basic20" {
  let code = CodeGen::new("int arg1 =  arg + 1;\n" + "return arg1 >>> arg;\n")
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
test "chapter21: inst_select if stmt" {
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
test "chapter21: inst_select lea1" {
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
test "chapter21: inst_select lea2" {
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
test "chapter21: inst_select lea3" {
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
