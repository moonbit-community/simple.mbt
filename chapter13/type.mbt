///|
pub enum Type {
  Bot
  Top
  Ctrl
  XCtrl
  IntTop
  IntBot
  Int(Int64)
  FltTop
  FltBot
  Flt(Double)
  Mem(Int)
  MemPtr(TypeStruct, Bool)
  Tuple(Array[Type])
} derive(Eq)

///|
pub struct TypeInteger {}

///|
pub struct TypeFloat {}

///|
pub struct Field {
  _fname : String
  _type : Type
} derive(Eq)

///|
pub struct TypeStruct {
  _name : String
  _fields : Array[Field]?
} derive(Eq)

///|
pub impl Show for TypeStruct with output(self, logger) {
  logger.write_string(self.str())
}

///|
pub let bottom : Type = Bot

///|
pub let top : Type = Top

///|
pub let control : Type = Ctrl

///|
pub let xcontrol : Type = XCtrl

///|
pub let type_integer : TypeInteger = TypeInteger::{  }

///|
pub let type_float : TypeFloat = TypeFloat::{  }

///|
pub let type_integer_top : Type = IntTop

///|
pub let type_integer_bot : Type = IntBot

///|
pub let type_integer_zero : Type = TypeInteger::constant(0L)

///|
pub let type_float_top : Type = FltTop

///|
pub let type_float_bot : Type = FltBot

///|
pub let type_float_zero : Type = TypeFloat::constant(0.0)

///|
pub let type_mem_top : Type = Mem(0)

///|
pub let type_mem_bot : Type = Mem(-1)

///|
pub let type_struct_top : TypeStruct = { _name: "$TOP", _fields: Some([]) }

///|
pub let type_struct_bot : TypeStruct = { _name: "$BOT", _fields: Some([]) }

///|
pub let type_field_test : Field = Field::make("test", type_integer_zero)

///|
pub let type_struct_test : TypeStruct = TypeStruct::make("test", [type_field_test])

///|
pub let type_struct_s1_forward : TypeStruct = TypeStruct::make_forward("S1")

///|
pub let type_struct_s2_forward : TypeStruct = TypeStruct::make_forward("S2")

///|
pub let type_struct_s1 : TypeStruct =
  TypeStruct::make(
    "S1",
    [
      Field::make("a", type_integer_bot),
      Field::make("s2", MemPtr(type_struct_s2_forward, false)),
    ],
  )

///|
pub let type_struct_s2 : TypeStruct =
  TypeStruct::make(
    "S2",
    [
      Field::make("b", type_float_bot),
      Field::make("s1", MemPtr(type_struct_s1_forward, false)),
    ],
  )

///|
pub let type_mem_ptr_bot : Type = MemPtr(type_struct_bot, true)

///|
pub let type_mem_ptr_top : Type = type_mem_ptr_bot.dual()

///|
pub let type_mem_ptr_nullptr : Type = MemPtr(type_struct_top, true)

///|
pub let type_mem_ptr_voidptr : Type = type_mem_ptr_nullptr.dual()

///|
pub let type_mem_ptr_test : Type = MemPtr(type_struct_test, false)

///|
pub let type_tuple_if_both : Type = Tuple([control, control])

///|
pub let type_tuple_if_neither : Type = Tuple([xcontrol, xcontrol])

///|
pub let type_tuple_if_true : Type = Tuple([control, xcontrol])

///|
pub let type_tuple_if_false : Type = Tuple([xcontrol, control])

///|
pub fn Type::gather() -> Array[Type] {
  let ts : Array[Type] = []
  ts.push(bottom)
  ts.push(control)
  ts.push(type_integer_zero)
  ts.push(type_integer_bot)
  ts.push(type_float_zero)
  ts.push(type_float_bot)
  ts.push(Mem(1))
  ts.push(type_mem_bot)
  ts.push(type_mem_ptr_nullptr)
  ts.push(type_mem_ptr_bot)
  ts.push(type_mem_ptr_test)
  ts.push(MemPtr(type_struct_s1, false))
  ts.push(MemPtr(type_struct_s2, false))
  ts.push(Tuple([type_integer_bot, type_mem_ptr_test]))
  ts.push(type_tuple_if_both)
  let sz = ts.length()
  for i in 0..<sz {
    ts.push(ts[i].dual())
  }
  ts
}

///|
pub fn Type::mem(mem_alias : Int) -> Type {
  Mem(mem_alias)
}

///|
pub fn Type::mem_ptr(obj : TypeStruct, nil? : Bool = false) -> Type {
  MemPtr(obj, nil)
}

///|
pub fn Type::is_constant(self : Type) -> Bool {
  match self {
    Int(_) => true
    Flt(_) => true
    _ => false
  }
}

///|
pub fn Type::is_high_or_const(self : Type) -> Bool {
  match self {
    Top | XCtrl | IntTop | Int(_) | FltTop | Flt(_) => true
    _ => false
  }
}

///|
pub fn Type::dual(self : Type) -> Type {
  match self {
    Bot => Top
    Top => Bot
    Ctrl => XCtrl
    XCtrl => Ctrl
    IntTop => IntBot
    IntBot => IntTop
    Int(v) => Int(v)
    FltTop => FltBot
    FltBot => FltTop
    Flt(v) => Flt(v)
    Mem(mem_alias) =>
      if mem_alias == 0 {
        type_mem_bot
      } else if mem_alias == -1 {
        type_mem_top
      } else {
        Mem(mem_alias)
      }
    MemPtr(obj, nil) => MemPtr(obj.dual(), !nil)
    Tuple(types) => Tuple(types.map(fn(t) { t.dual() }))
  }
}

///|
pub fn Type::join(self : Type, other : Type) -> Type {
  if self == other {
    return self
  }
  self.dual().meet(other.dual()).dual()
}

///|
pub fn Type::isa(self : Type, other : Type) -> Bool {
  self.meet(other) == other
}

///|
pub fn Type::glb(self : Type) -> Type {
  match self {
    Ctrl => xcontrol
    Bot | Top | XCtrl => bottom
    IntTop | IntBot | Int(_) => type_integer_bot
    FltTop | FltBot | Flt(_) => type_float_bot
    Mem(_) => type_mem_bot
    MemPtr(obj, _nil) => MemPtr(obj.glb(), true)
    Tuple(types) => Tuple(types.map(fn(t) { t.glb() }))
  }
}

///|
pub fn Type::make_init(self : Type) -> Type {
  match self {
    IntTop | IntBot | Int(_) => type_integer_zero
    FltTop | FltBot | Flt(_) => type_float_zero
    MemPtr(_, _) => type_mem_ptr_nullptr
    _ => bottom
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
    (Bot, _) | (_, Bot) => Bot
    (Top, x) => x
    (x, Top) => x
    (Ctrl, XCtrl) | (XCtrl, Ctrl) => Ctrl
    (Int(v0), Int(v1)) => if v0 == v1 { Int(v0) } else { IntBot }
    (IntTop, IntBot) | (IntBot, IntTop) => IntBot
    (IntTop, x) =>
      match x {
        IntTop | IntBot | Int(_) => x
        _ => bottom
      }
    (x, IntTop) =>
      match x {
        IntTop | IntBot | Int(_) => x
        _ => bottom
      }
    (IntBot, IntBot) => IntBot
    (IntBot, Int(_)) | (Int(_), IntBot) => IntBot
    (Flt(v0), Flt(v1)) => if v0 == v1 { Flt(v0) } else { FltBot }
    (FltTop, FltBot) | (FltBot, FltTop) => FltBot
    (FltTop, x) =>
      match x {
        FltTop | FltBot | Flt(_) => x
        _ => bottom
      }
    (x, FltTop) =>
      match x {
        FltTop | FltBot | Flt(_) => x
        _ => bottom
      }
    (FltBot, FltBot) => FltBot
    (FltBot, Flt(_)) | (Flt(_), FltBot) => FltBot
    (Tuple(ts0), Tuple(ts1)) =>
      if ts0.length() != ts1.length() {
        bottom
      } else {
        Tuple(ts0.mapi(fn(i, t0) { t0.meet(ts1[i]) }))
      }
    (Mem(a0), Mem(a1)) =>
      if a0 == 0 {
        Mem(a1)
      } else if a1 == 0 {
        Mem(a0)
      } else {
        type_mem_bot
      }
    (MemPtr(obj0, nil0), MemPtr(obj1, nil1)) =>
      MemPtr(obj0.meet(obj1), nil0 || nil1)
    _ => bottom
  }
}

///|
pub fn Type::hash_code(self : Type) -> Int {
  let mix = fn(v : Int) -> Int { v ^ (v << 17) ^ (v >> 13) }
  match self {
    Bot => 0x01
    Top => 0x02
    Ctrl => 0x03
    XCtrl => 0x04
    IntTop => 0x05
    IntBot => 0x06
    Int(v) => mix(0x10 ^ v.to_int())
    FltTop => 0x07
    FltBot => 0x08
    Flt(v) => mix(0x18 ^ v.hash())
    Mem(mem_alias) => mix(0x30 ^ mem_alias)
    MemPtr(obj, nil) =>
      mix(
        (0x40 ^ obj.hash_code()) ^
        (if nil { 0x1000 } else { 0 }),
      )
    Tuple(types) => {
      let mut sum = 0x20
      for t in types {
        sum = mix(sum ^ t.hash_code())
      }
      sum
    }
  }
}

///|
pub fn Type::print_to(self : Type, sb : StringBuilder) -> Unit {
  match self {
    Bot => sb.write_string("Bot")
    Top => sb.write_string("Top")
    Ctrl => sb.write_string("Ctrl")
    XCtrl => sb.write_string("~Ctrl")
    IntTop => sb.write_string("IntTop")
    IntBot => sb.write_string("IntBot")
    Int(v) => sb.write_string(v.to_string())
    FltTop => sb.write_string("FltTop")
    FltBot => sb.write_string("FltBot")
    Flt(v) => sb.write_string(TypeFloat::to_java_string(v))
    Mem(mem_alias) =>
      if mem_alias == 0 {
        sb.write_string("MEM#TOP")
      } else if mem_alias == -1 {
        sb.write_string("MEM#BOT")
      } else {
        sb.write_string("MEM#")
        sb.write_string(mem_alias.to_string())
      }
    MemPtr(_, _) => sb.write_string(self.str())
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
pub fn Type::str(self : Type) -> String {
  match self {
    IntTop => "~int"
    IntBot => "int"
    Int(v) => v.to_string()
    FltTop => "~flt"
    FltBot => "flt"
    Flt(v) => TypeFloat::to_java_string(v)
    MemPtr(_, _) =>
      if self == type_mem_ptr_nullptr {
        "null"
      } else if self == type_mem_ptr_voidptr {
        "*void"
      } else {
        match self {
          MemPtr(obj, nil) =>
            if nil { "*\{obj.str()}?" } else { "*\{obj.str()}" }
          _ => "?"
        }
      }
    Mem(mem_alias) =>
      if mem_alias == 0 {
        "MEM#TOP"
      } else if mem_alias == -1 {
        "MEM#BOT"
      } else {
        "MEM#\{mem_alias}"
      }
    Bot => "Bot"
    Top => "Top"
    Ctrl => "Ctrl"
    XCtrl => "~Ctrl"
    Tuple(_) => {
      let sb = StringBuilder::new()
      self.print_to(sb)
      sb.to_string()
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

///|
pub fn TypeFloat::constant(con : Double) -> Type {
  Flt(con)
}

///|
pub fn TypeFloat::to_java_string(v : Double) -> String {
  let s = v.to_string()
  if s.contains(".") || s.contains("e") || s.contains("E") {
    s
  } else {
    s + ".0"
  }
}

///|
pub fn Field::make(fname : String, typ : Type) -> Field {
  { _fname: fname, _type: typ }
}

///|
pub fn TypeStruct::make(name : String, fields : Array[Field]) -> TypeStruct {
  { _name: name, _fields: Some(fields) }
}

///|
pub fn TypeStruct::find(self : TypeStruct, fname : String) -> Int {
  match self._fields {
    None => ()
    Some(fields) =>
      for i, field in fields {
        if field._fname == fname {
          return i
        }
      }
  }
  -1
}

///|
pub fn TypeStruct::meet(self : TypeStruct, other : TypeStruct) -> TypeStruct {
  if self == other {
    return self
  }
  if self == type_struct_top {
    return other
  }
  if other == type_struct_top {
    return self
  }
  if self == type_struct_bot || other == type_struct_bot {
    return type_struct_bot
  }
  if self._name != other._name {
    return type_struct_bot
  }
  match (self._fields, other._fields) {
    (None, _) => return self
    (_, None) => return other
    (Some(f0s), Some(f1s)) =>
      if f0s.length() != f1s.length() {
        return type_struct_bot
      } else {
        let fields : Array[Field] = []
        for i, f0 in f0s {
          let f1 = f1s[i]
          if f0._fname != f1._fname {
            return type_struct_bot
          }
          fields.push(Field::make(f0._fname, f0._type.meet(f1._type)))
        }
        return TypeStruct::make(self._name, fields)
      }
  }
  type_struct_bot
}

///|
pub fn TypeStruct::dual(self : TypeStruct) -> TypeStruct {
  if self == type_struct_top {
    return type_struct_bot
  }
  if self == type_struct_bot {
    return type_struct_top
  }
  if self._fields is None {
    return self
  }
  let fields : Array[Field] = []
  match self._fields {
    None => ()
    Some(fs) =>
      for f in fs {
        fields.push(Field::make(f._fname, f._type.dual()))
      }
  }
  TypeStruct::make(self._name, fields)
}

///|
pub fn TypeStruct::glb(self : TypeStruct) -> TypeStruct {
  if self == type_struct_top || self == type_struct_bot {
    return self
  }
  if self._fields is None {
    return self
  }
  let fields : Array[Field] = []
  match self._fields {
    None => ()
    Some(fs) =>
      for f in fs {
        fields.push(Field::make(f._fname, f._type.glb()))
      }
  }
  TypeStruct::make(self._name, fields)
}

///|
pub fn TypeStruct::hash_code(self : TypeStruct) -> Int {
  let mix = fn(v : Int) -> Int { v ^ (v << 17) ^ (v >> 13) }
  let mut sum = self._name.hash()
  match self._fields {
    None => ()
    Some(fs) =>
      for f in fs {
        sum = mix(sum ^ f._fname.hash() ^ f._type.hash_code())
      }
  }
  sum
}

///|
pub fn TypeStruct::str(self : TypeStruct) -> String {
  self._name
}

///|
pub fn TypeStruct::make_forward(name : String) -> TypeStruct {
  { _name: name, _fields: None }
}
