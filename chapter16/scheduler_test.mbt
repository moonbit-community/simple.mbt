///|
fn assert_obj_int_fields(
  value : EvalValue,
  name : String,
  fields : Array[Int64],
) -> Unit raise {
  match value {
    EvalValue::Obj(obj) => {
      assert_eq(obj.struct_._name, name)
      assert_eq(obj.fields.length(), fields.length())
      for i = 0; i < fields.length(); i = i + 1 {
        match obj.fields[i] {
          EvalValue::Int(v) => assert_eq(v, fields[i])
          _ => fail("expected int field")
        }
      }
    }
    _ => fail("expected object")
  }
}

///|
test "scheduler: store in if" {
  let parser = Parser::new(
    "struct S {\n" +
    "    int f;\n" +
    "};\n" +
    "S v0=new S;\n" +
    "if(arg) v0.f=1;\n" +
    "return v0;\n",
  )
  let stop = parser.parse(show=false).iterate()
  assert_obj_int_fields(Evaluator::evaluate(stop, parameter=0), "S", [0L])
  assert_obj_int_fields(Evaluator::evaluate(stop, parameter=1), "S", [1L])
}

///|
test "scheduler: store in if 2" {
  let parser = Parser::new(
    "struct S {\n" +
    "    int f;\n" +
    "};\n" +
    "S v=new S;\n" +
    "v.f = 2;\n" +
    "int i=new S.f;\n" +
    "i=v.f;\n" +
    "if (arg) v.f=1;\n" +
    "return i;\n",
  )
  let stop = parser.parse(show=false).iterate()
  match Evaluator::evaluate(stop, parameter=0) {
    EvalValue::Int(v) => assert_eq(v, 2L)
    _ => fail("expected int")
  }
  match Evaluator::evaluate(stop, parameter=1) {
    EvalValue::Int(v) => assert_eq(v, 2L)
    _ => fail("expected int")
  }
}
