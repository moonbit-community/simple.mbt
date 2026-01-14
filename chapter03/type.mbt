///|
pub enum Type {
  Bot
  Top
  Int(Int64)
} derive(Eq)

///|
pub struct TypeInteger {}

///|
pub let bottom : Type = Bot

///|
pub let top : Type = Top

///|
pub let type_integer : TypeInteger = TypeInteger::{  }

///|
pub fn Type::is_constant(self : Type) -> Bool {
  match self {
    Int(_) => true
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
pub fn Type::print_to(self : Type, sb : StringBuilder) -> Unit {
  match self {
    Bot => sb.write_string("Bot")
    Top => sb.write_string("Top")
    Int(v) => sb.write_string(v.to_string())
  }
}

///|
pub impl Show for Type with output(self, logger) {
  match self {
    Bot => logger.write_string("Bot")
    Top => logger.write_string("Top")
    Int(v) => logger.write_string(v.to_string())
  }
}

///|
pub fn TypeInteger::constant(con : Int64) -> Type {
  Int(con)
}

///|
pub let type_integer_zero : Type = TypeInteger::constant(0L)
