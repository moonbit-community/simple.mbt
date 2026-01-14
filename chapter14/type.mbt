///|
pub enum Type {
  Bot
  Top
  Ctrl
  XCtrl
  Int(TypeInteger)
  Flt(TypeFloat)
  Mem(Int)
  MemPtr(TypeStruct, Bool)
  Tuple(Array[Type])
} derive(Eq)

///|
pub struct TypeInteger {
  _min : Int64
  _max : Int64
} derive(Eq)

///|
pub struct TypeFloat {
  /// +/-64 for double; +/-32 for float, or 0 for constants
  _sz : Int
  /// The constant value or 0.0
  _con : Double
} derive(Eq)

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
let long_max_value : Int64 = 9223372036854775807L

///|
let long_min_value : Int64 = -9223372036854775807L - 1L

///|
pub let type_integer_top : Type =
  Int({ _min: long_max_value, _max: long_min_value })

///|
pub let type_integer_bot : Type =
  Int({ _min: long_min_value, _max: long_max_value })

///|
pub let type_integer_zero : Type = TypeInteger::constant(0L)

///|
pub let type_integer_u1 : Type = TypeInteger::make(0L, 1L)

///|
pub let type_integer_bool : Type = type_integer_u1

///|
pub let type_integer_false : Type = type_integer_zero

///|
pub let type_integer_true : Type = TypeInteger::constant(1L)

///|
pub let type_integer_i8 : Type = TypeInteger::make(-128L, 127L)

///|
pub let type_integer_i16 : Type = TypeInteger::make(-32768L, 32767L)

///|
pub let type_integer_i32 : Type =
  TypeInteger::make(-(1L << 31), (1L << 31) - 1L)

///|
pub let type_integer_u8 : Type = TypeInteger::make(0L, 255L)

///|
pub let type_integer_u16 : Type = TypeInteger::make(0L, 65535L)

///|
pub let type_integer_u32 : Type = TypeInteger::make(0L, (1L << 32) - 1L)

///|
pub let type_float_top : Type = Flt({ _sz: -64, _con: 0.0 })

///|
pub let type_float_t32 : Type = Flt({ _sz: -32, _con: 0.0 })

///|
pub let type_float_zero : Type = TypeFloat::constant(0.0)

///|
pub let type_float_b32 : Type = Flt({ _sz: 32, _con: 0.0 })

///|
pub let type_float_bot : Type = Flt({ _sz: 64, _con: 0.0 })

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
  ts.push(type_integer_bool)
  ts.push(type_integer_u8)
  ts.push(type_float_zero)
  ts.push(type_float_bot)
  ts.push(type_float_b32)
  ts.push(TypeFloat::constant(3.141592653589793))
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
    Int(i) => i.is_constant()
    Flt(f) => f.is_constant()
    _ => false
  }
}

///|
pub fn Type::is_high(self : Type) -> Bool {
  match self {
    Top | XCtrl => true
    Int(i) => i.is_high()
    Flt(f) => f.is_high()
    _ => false
  }
}

///|
pub fn Type::is_high_or_const(self : Type) -> Bool {
  match self {
    Top | XCtrl => true
    Int(i) => i.is_high_or_const()
    Flt(f) => f.is_high_or_const()
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
    Int(i) => Int({ _min: i._max, _max: i._min })
    Flt(f) =>
      if f._sz == 0 {
        self
      } else {
        Flt({ _sz: -f._sz, _con: 0.0 })
      }
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
    Int(_) => type_integer_bot
    Flt(_) => type_float_bot
    Mem(_) => type_mem_bot
    MemPtr(obj, _nil) => MemPtr(obj.glb(), true)
    Tuple(types) => Tuple(types.map(fn(t) { t.glb() }))
  }
}

///|
pub fn Type::make_init(self : Type) -> Type {
  match self {
    Int(_) => type_integer_zero
    Flt(_) => type_float_zero
    MemPtr(_, _) => type_mem_ptr_nullptr
    _ => bottom
  }
}

///|
pub fn Type::value_exn(self : Type) -> Int64 {
  match self {
    Int(i) => i.value_exn()
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
    (Int(i0), Int(i1)) =>
      Int({
        _min: if i0._min < i1._min { i0._min } else { i1._min },
        _max: if i0._max > i1._max { i0._max } else { i1._max },
      })
    (Flt(f0), Flt(f1)) => TypeFloat::xmeet(f0, f1)
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
    (Ctrl | XCtrl, Ctrl | XCtrl) => Ctrl
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
    Int(i) => mix(0x10 ^ i._min.hash() ^ i._max.hash())
    Flt(f) => mix(0x18 ^ f._con.hash() ^ f._sz)
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
    Int(i) => sb.write_string(i.str())
    Flt(f) => f.print_to(sb)
    MemPtr(_, _) => sb.write_string(self.str())
    Mem(mem_alias) =>
      if mem_alias == 0 {
        sb.write_string("MEM#TOP")
      } else if mem_alias == -1 {
        sb.write_string("MEM#BOT")
      } else {
        sb.write_string("MEM#")
        sb.write_string(mem_alias.to_string())
      }
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
    Int(i) => i.str()
    Flt(f) => f.str()
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
pub fn TypeInteger::make(lo : Int64, hi : Int64) -> Type {
  Int({ _min: lo, _max: hi })
}

///|
pub fn TypeInteger::make_con(is_con : Bool, con : Int64) -> Type {
  let lo = if is_con {
    con
  } else if con == 0L {
    long_max_value
  } else {
    long_min_value
  }
  let hi = if is_con {
    con
  } else if con == 0L {
    long_min_value
  } else {
    long_max_value
  }
  TypeInteger::make(lo, hi)
}

///|
pub fn TypeInteger::constant(con : Int64) -> Type {
  TypeInteger::make_con(true, con)
}

///|
pub fn TypeInteger::is_high(self : TypeInteger) -> Bool {
  self._min > self._max
}

///|
pub fn TypeInteger::is_high_or_const(self : TypeInteger) -> Bool {
  self._min >= self._max
}

///|
pub fn TypeInteger::is_constant(self : TypeInteger) -> Bool {
  self._min == self._max
}

///|
pub fn TypeInteger::value_exn(self : TypeInteger) -> Int64 {
  if !self.is_constant() {
    panic()
  }
  self._min
}

///|
pub fn TypeInteger::mask(self : TypeInteger) -> Int64 {
  if self.is_high() {
    return 0L
  }
  if self.is_constant() {
    return self._min
  }
  let x = self._min.lxor(self._max)
  let ff1 = 1L << (63 - x.clz())
  self._min.lor((ff1 - 1L).lor(ff1))
}

///|
pub fn TypeInteger::str(self : TypeInteger) -> String {
  if self._min == long_max_value && self._max == long_min_value {
    return "~int"
  }
  if self._min == long_min_value && self._max == long_max_value {
    return "int"
  }
  if self._min == 0L && self._max == 1L {
    return "bool"
  }
  if self._min == -128L && self._max == 127L {
    return "i8"
  }
  if self._min == -32768L && self._max == 32767L {
    return "i16"
  }
  if self._min == -(1L << 31) && self._max == (1L << 31) - 1L {
    return "i32"
  }
  if self._min == 0L && self._max == 255L {
    return "u8"
  }
  if self._min == 0L && self._max == 65535L {
    return "u16"
  }
  if self._min == 0L && self._max == (1L << 32) - 1L {
    return "u32"
  }
  if self.is_constant() {
    return self._min.to_string()
  }
  "[\{self._min}-\{self._max}]"
}

///|
pub fn TypeFloat::constant(con : Double) -> Type {
  Flt({ _sz: 0, _con: con })
}

///|
pub fn TypeFloat::is_f32(self : TypeFloat) -> Bool {
  Float::from_double(self._con).to_double() == self._con
}

///|
pub fn TypeFloat::is_high(self : TypeFloat) -> Bool {
  self._sz < 0
}

///|
pub fn TypeFloat::is_high_or_const(self : TypeFloat) -> Bool {
  self._sz <= 0
}

///|
pub fn TypeFloat::is_constant(self : TypeFloat) -> Bool {
  self._sz == 0
}

///|
pub fn TypeFloat::value_exn(self : TypeFloat) -> Double {
  if !self.is_constant() {
    panic()
  }
  self._con
}

///|
pub fn TypeFloat::xmeet(self : TypeFloat, other : TypeFloat) -> Type {
  let i0 = if self._sz < other._sz { self } else { other }
  let i1 = if self._sz < other._sz { other } else { self }

  if i1._sz == 64 {
    return type_float_bot
  }
  if i0._sz == -64 {
    return Flt(i1)
  }
  if i1._sz == 32 {
    return if i0._sz == 0 && !i0.is_f32() { type_float_bot } else { type_float_b32 }
  }
  if i1._sz != 0 {
    return Flt(i1)
  }
  // i1 is a constant
  if i0._sz == -32 {
    return if i1.is_f32() { Flt(i1) } else { type_float_bot }
  }
  // Both are constants, and never equal
  if i0.is_f32() && i1.is_f32() {
    type_float_b32
  } else {
    type_float_bot
  }
}

///|
pub fn TypeFloat::print_to(self : TypeFloat, sb : StringBuilder) -> Unit {
  if self._sz == -64 {
    sb.write_string("FltTop")
  } else if self._sz == -32 {
    sb.write_string("F32Top")
  } else if self._sz == 32 {
    sb.write_string("F32Bot")
  } else if self._sz == 64 {
    sb.write_string("FltBot")
  } else {
    sb.write_string(TypeFloat::to_java_string(self._con))
  }
}

///|
pub fn TypeFloat::str(self : TypeFloat) -> String {
  if self._sz == -64 {
    return "~flt"
  }
  if self._sz == -32 {
    return "~f32"
  }
  if self._sz == 32 {
    return "f32"
  }
  if self._sz == 64 {
    return "flt"
  }
  let base = TypeFloat::to_java_string(self._con)
  if self.is_f32() { base + "f" } else { base }
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
