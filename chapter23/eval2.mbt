///|
pub struct Eval2 {}

///|
pub fn Eval2::eval(code : CodeGen, arg : Int64, loops? : Int = 1000) -> String {
  // Force scheduling before running the interpreter (matches refs/simple intent).
  ignore(code.gcm().local_sched())

  // NOTE: This is a placeholder implementation. refs/simple/chapter19 Eval2
  // supports function calls and closures; chapter19 MoonBit port will extend
  // this to match.
  let v = Evaluator::evaluate(code._stop, parameter=arg, loops~)
  match v {
    EvalValue::Int(i) => "\{i}"
    EvalValue::Float(f) => "\{f}"
    EvalValue::Null => "null"
    EvalValue::Obj(_) | EvalValue::Mem(_) | EvalValue::Tuple(_) => "\{v}"
  }
}
