///|
pub enum Type {
  Bot
  Top
  Ctrl
  IntTop
  IntBot
  Int(Int64)
  Tuple(Array[Type])
} derive(Eq)

///|
pub struct TypeInteger {}

///|
pub let bottom : Type = Bot

///|
pub let top : Type = Top

///|
pub let control : Type = Ctrl

///|
pub let type_integer : TypeInteger = TypeInteger::{  }

///|
pub let type_integer_top : Type = IntTop

///|
pub let type_integer_bot : Type = IntBot

///|
pub let type_integer_zero : Type = TypeInteger::constant(0L)

///|
pub let type_tuple_if : Type = Tuple([control, control])

///|
pub fn Type::is_constant(self : Type) -> Bool {
  match self {
    Top | Int(_) => true
    _ => false
  }
}

///|
pub fn Type::value_exn(self : Type) -> Int64 {
  match self {
    Int(v) => v
    _ => panic()
  }
}

///|
pub fn Type::meet(self : Type, other : Type) -> Type {
  if self == other {
    return self
  }
  match (self, other) {
    (IntBot, _) | (_, IntBot) => IntBot
    (IntTop, x) => x
    (x, IntTop) => x
    (Int(v0), Int(v1)) => if v0 == v1 { Int(v0) } else { IntBot }
    _ => bottom
  }
}

///|
pub fn Type::print_to(self : Type, sb : StringBuilder) -> Unit {
  match self {
    Bot => sb.write_string("Bot")
    Top => sb.write_string("Top")
    Ctrl => sb.write_string("Ctrl")
    IntTop => sb.write_string("IntTop")
    IntBot => sb.write_string("IntBot")
    Int(v) => sb.write_string(v.to_string())
    Tuple(types) => {
      sb.write_string("[")
      let mut first = true
      for t in types {
        if !first {
          sb.write_string(",")
        }
        first = false
        t.print_to(sb)
      }
      sb.write_string("]")
    }
  }
}

///|
pub impl Show for Type with output(self, logger) {
  let sb = StringBuilder::new()
  self.print_to(sb)
  logger.write_string(sb.to_string())
}

///|
pub fn TypeInteger::constant(con : Int64) -> Type {
  Int(con)
}
