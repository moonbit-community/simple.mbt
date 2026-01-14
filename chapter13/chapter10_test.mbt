///|
fn expect_iterate_error(source : String, expected : String) -> Unit raise {
  let result : Result[Node, ParseError] = try? Parser::new(source).parse().iterate()
  match result {
    Err(ParseError::Msg(msg)) => assert_eq(msg, expected)
    Ok(_) => fail("expected ParseError")
  }
}

///|
test "chapter10: fuzzer" {
  let parser = Parser::new(
    "int a = arg/3;\n" +
    "int b = arg*5;\n" +
    "int x = arg*7;\n" +
    "int y = arg/11;\n" +
    "int p; int g; int h;\n" +
    "if( (arg/13)==0 ) {\n" +
    "    p = x + y;\n" +
    "    g = x;\n" +
    "    h = y;\n" +
    "} else {\n" +
    "    p = a + b;\n" +
    "    g = a;\n" +
    "    h = b;\n" +
    "}\n" +
    "int r = g+h;\n" +
    "return p-r;\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return 0;")
}

///|
test "chapter10: struct" {
  let parser = Parser::new(
    "struct Bar {\n" +
    "    int a;\n" +
    "    int b;\n" +
    "}\n" +
    "struct Foo {\n" +
    "    int x;\n" +
    "}\n" +
    "Foo? foo = null;\n" +
    "Bar bar = new Bar;\n" +
    "bar.a = 1;\n" +
    "bar.a = 2;\n" +
    "return bar.a;\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return 2;")
}

///|
test "chapter10: example" {
  let parser = Parser::new(
    "struct Vector2D { int x; int y; }\n" +
    "Vector2D v = new Vector2D;\n" +
    "v.x = 1;\n" +
    "if (arg)\n" +
    "    v.y = 2;\n" +
    "else\n" +
    "    v.y = 3;\n" +
    "return v;\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return new Vector2D;")
}

///|
test "chapter10: bug unknown field from null" {
  expect_parse_error(
    "struct s0 {\n" +
    "    int v0;\n" +
    "}\n" +
    "s0? v1=null;\n" +
    "int v3=v1.zAicm;\n",
    "Accessing unknown field 'zAicm' from 'null'",
  )
}

///|
test "chapter10: bug expected identifier" {
  expect_parse_error(
    "struct s0 { int v0; }\n" +
    "arg=0+new s0.0;\n",
    "Expected an identifier, found 'null'",
  )
}

///|
test "chapter10: loop" {
  let parser = Parser::new(
    "struct Bar { int a; }\n" +
    "Bar bar = new Bar;\n" +
    "while (arg) {\n" +
    "    bar.a = bar.a + 2;\n" +
    "    arg = arg + 1;\n" +
    "}\n" +
    "return bar.a;\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return Phi(Loop13,0,(Phi_a+2));")
}

///|
test "chapter10: if type mismatch" {
  expect_iterate_error(
    "struct Bar { int a; }\n" +
    "Bar bar = new Bar;\n" +
    "if (arg) bar = null;\n" +
    "bar.a = 1;\n" +
    "return bar.a;\n",
    "Type null is not of declared type *Bar",
  )
}

///|
test "chapter10: if might be null" {
  expect_iterate_error(
    "struct Bar { int a; }\n" +
    "Bar? bar = null;\n" +
    "if (arg) bar = new Bar;\n" +
    "bar.a = 1;\n" +
    "return bar.a;\n",
    "Might be null accessing 'a'",
  )
}

///|
test "chapter10: if type mismatch (decl)" {
  expect_parse_error(
    "struct Bar { int a; }\n" +
    "Bar bar = null;\n" +
    "if (arg) bar = null;\n" +
    "bar.a = 1;\n" +
    "return bar.a;\n",
    "Type null is not of declared type *Bar",
  )
}

///|
test "chapter10: if or null" {
  let parser = Parser::new(
    "struct Bar { int a; }\n" +
    "Bar? bar = new Bar;\n" +
    "if (arg) bar = null;\n" +
    "if( bar ) bar.a = 1;\n" +
    "return bar;\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return Phi(Region32,(*void)Phi(Region20,null,new Bar),null);")
}

///|
test "chapter10: if or null 2" {
  let parser = Parser::new(
    "struct Bar { int a; }\n" +
    "Bar? bar = new Bar;\n" +
    "if (arg) bar = null;\n" +
    "int rez = 3;\n" +
    "if( !bar ) rez=4;\n" +
    "else bar.a = 1;\n" +
    "return rez;\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return Phi(Region38,4,3);")
}

///|
test "chapter10: while with null inside" {
  expect_iterate_error(
    "struct s0 {int v0;}\n" +
    "s0? v0 = new s0;\n" +
    "int ret = 0;\n" +
    "while(arg) {\n" +
    "    ret = v0.v0;\n" +
    "    v0 = null;\n" +
    "    arg = arg - 1;\n" +
    "}\n" +
    "return ret;\n",
    "Might be null accessing 'v0'",
  )
}

///|
test "chapter10: redeclare struct" {
  expect_parse_error(
    "struct s0 {\n" +
    "    int v0;\n" +
    "}\n" +
    "s0? v1=new s0;\n" +
    "s0? v1;\n" +
    "v1=new s0;\n",
    "Redefining name 'v1'",
  )
}

///|
test "chapter10: iter" {
  let parser = Parser::new(
    "struct Iter {\n" +
    "    int x;\n" +
    "    int len;\n" +
    "}\n" +
    "Iter i = new Iter;\n" +
    "i.len = arg;\n" +
    "int sum=0;\n" +
    "while( i.x < i.len ) {\n" +
    "    sum = sum + i.x;\n" +
    "    i.x = i.x + 1;\n" +
    "}\n" +
    "return sum;\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return Phi(Loop18,0,(Phi(Loop,0,(Phi_x+1))+Phi_sum));")
}

///|
test "chapter10: test1" {
  let parser = Parser::new(
    "struct s0 {int v0;}\n" +
    "s0 ret = new s0;\n" +
    "while(arg) {\n" +
    "    s0 v0 = new s0;\n" +
    "    v0.v0 = arg;\n" +
    "    arg = arg-1;\n" +
    "    if (arg==5) ret=v0;\n" +
    "}\n" +
    "return ret;\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return Phi(Loop13,new s0,Phi(Region35,new s0,Phi_ret));")
}

///|
test "chapter10: test2" {
  let parser = Parser::new(
    "struct s0 {int v0;}\n" +
    "s0 ret = new s0;\n" +
    "s0 v0 = new s0;\n" +
    "while(arg) {\n" +
    "    v0.v0 = arg;\n" +
    "    arg = arg-1;\n" +
    "    if (arg==5) ret=v0;\n" +
    "}\n" +
    "return ret;\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return Phi(Loop16,new s0,Phi(Region36,new s0,Phi_ret));")
}

///|
test "chapter10: test3" {
  let parser = Parser::new(
    "struct s0 {int v0;}\n" +
    "s0 ret = new s0;\n" +
    "while(arg < 10) {\n" +
    "    s0 v0 = new s0;\n" +
    "    if (arg == 5) ret=v0;\n" +
    "    arg = arg + 1;\n" +
    "}\n" +
    "return ret;\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return Phi(Loop13,new s0,Phi(Region34,new s0,Phi_ret));")
}

///|
test "chapter10: bug3 dead code still parses" {
  expect_parse_error(
    "struct s0 {\n" +
    "    int f0;\n" +
    "}\n" +
    "if(0>=0) return new s0;\n" +
    "return new s0;\n" +
    "int v0=null.f0;\n",
    "Accessing unknown field 'f0' from 'null'",
  )
}

///|
test "chapter10: bug4" {
  let parser = Parser::new(
    "if(0) {\n" +
    "    while(0) if(arg) continue;\n" +
    "    int v0=0;\n" +
    "    while(1) {\n" +
    "        int arg=-arg;\n" +
    "        v0=arg;\n" +
    "    }\n" +
    "}\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return 0;")
}

///|
test "chapter10: bug5" {
  let parser = Parser::new(
    "struct s0 {\n" +
    "    int f0;\n" +
    "}\n" +
    "if(0) return 0;\n" +
    "else return new s0;\n" +
    "if(new s0.f0) return 0;\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return new s0;")
}

///|
test "chapter10: bug6 missed worklist" {
  let parser = Parser::new(
    "while(0) {}\n" +
    "int v4=0;\n" +
    "while(0<arg) {\n" +
    "    v4=v4+1;\n" +
    "    while(1) v4=-v4;\n" +
    "    while(0) arg=-1;\n" +
    "}\n" +
    "return 0;\n",
  )
  ignore(parser.parse(show=false).iterate())
}

///|
test "chapter10: bug7" {
  let parser = Parser::new(
    "struct s0 {  int f0; }\n" +
    "s0 v0 = new s0;\n" +
    "while(v0.f0) {}\n" +
    "s0 v1 = v0;\n" +
    "return v1;\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return new s0;")
}

///|
test "chapter10: bug8" {
  let parser = Parser::new(
    "int v2=0;\n" +
    "while(0)\n" +
    "while(0) {}\n" +
    "{\n" +
    "    {\n" +
    "        {\n" +
    "            int v36=0;\n" +
    "            {\n" +
    "                while(0) {\n" +
    "                    {\n" +
    "                        while(-v2) {\n" +
    "                            {\n" +
    "                                while(v36) {\n" +
    "                                                while(v2) return 0;\n" +
    "                                                break;\n" +
    "                                }\n" +
    "                            }\n" +
    "                            if(-v2) break;\n" +
    "                        }\n" +
    "                    }\n" +
    "                }\n" +
    "            }\n" +
    "        }\n" +
    "    }\n" +
    "}\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return 0;")
}

///|
test "chapter10: bug9" {
  let parser = Parser::new(
    "int v0=arg==0;\n" +
    "while(v0) continue;\n" +
    "return 0;\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_eq(stop.print(), "return 0;")
}
