///|
pub enum Type {
  Bot
  Top
  Ctrl
  XCtrl
  Nil
  XNil
  Int(TypeInteger)
  Flt(TypeFloat)
  Mem(TypeMem)
  Ptr(Int)
  MemPtr(TypeStruct, Int)
  FunPtr(TypeFunPtr)
  RPC(TypeRPC)
  Tuple(Array[Type]?)
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
pub struct TypeMem {
  _alias : Int
  _t : Type
} derive(Eq)

///|
pub struct Field {
  _fname : String
  _type : Type
  _alias : Int
  _final : Bool
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
pub struct TypeFunPtr {
  _nil : Int
  _sig : Array[Type]?
  _ret : Type
  _fidxs : Int64
  _name : String?
}

///|
pub impl Eq for TypeFunPtr with equal(self, other) {
  self._nil == other._nil &&
  self._sig == other._sig &&
  self._ret == other._ret &&
  self._fidxs == other._fidxs
}

///|
pub struct TypeRPC {
  _any : Bool
  _rpcs : Array[Int]
} derive(Eq)

///|
pub let bottom : Type = Bot

///|
pub let top : Type = Top

///|
pub let control : Type = Ctrl

///|
pub let xcontrol : Type = XCtrl

///|
pub let type_nil : Type = Nil

///|
pub let type_xnil : Type = XNil

///|
pub let type_ptr_xptr : Type = Ptr(0)

///|
pub let type_ptr_xnptr : Type = Ptr(1)

///|
pub let type_ptr_nptr : Type = Ptr(2)

///|
pub let type_ptr_ptr : Type = Ptr(3)

///|
let long_max_value : Int64 = 9223372036854775807L

///|
let long_min_value : Int64 = -9223372036854775807L - 1L

///|
pub let type_integer_top : Type = Int({
  _min: long_max_value,
  _max: long_min_value,
})

///|
pub let type_integer_bot : Type = Int({
  _min: long_min_value,
  _max: long_max_value,
})

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
pub let type_integer_i32 : Type = TypeInteger::make(
  -(1L << 31),
  (1L << 31) - 1L,
)

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
pub let type_mem_top : Type = Mem({ _alias: 0, _t: top })

///|
pub let type_mem_bot : Type = Mem({ _alias: 0, _t: bottom })

///|
pub let type_struct_top : TypeStruct = { _name: "$TOP", _fields: Some([]) }

///|
pub let type_struct_bot : TypeStruct = { _name: "$BOT", _fields: Some([]) }

///|
pub let type_field_test : Field = Field::make(
  "test", type_integer_zero, -2, false,
)

///|
pub let type_struct_test : TypeStruct = TypeStruct::make("test", [
  type_field_test,
])

///|
pub let type_struct_s1_forward : TypeStruct = TypeStruct::make_forward("S1")

///|
pub let type_struct_s2_forward : TypeStruct = TypeStruct::make_forward("S2")

///|
pub let type_struct_s1 : TypeStruct = TypeStruct::make("S1", [
  Field::make("a", type_integer_bot, -1, false),
  Field::make("s2", MemPtr(type_struct_s2_forward, 2), -2, false),
])

///|
pub let type_struct_s2 : TypeStruct = TypeStruct::make("S2", [
  Field::make("b", type_float_bot, -3, false),
  Field::make("s1", MemPtr(type_struct_s1_forward, 2), -4, false),
])

///|
pub let type_mem_ptr_voidptr : Type = MemPtr(type_struct_bot, 2)

///|
pub let type_mem_ptr_bot : Type = MemPtr(type_struct_bot, 3)

///|
pub let type_mem_ptr_top : Type = type_mem_ptr_bot.dual()

///|
pub let type_mem_ptr_test : Type = MemPtr(type_struct_test, 2)

///|
pub let type_tuple_if_both : Type = Tuple(Some([control, control]))

///|
pub let type_tuple_if_neither : Type = Tuple(Some([xcontrol, xcontrol]))

///|
pub let type_tuple_if_true : Type = Tuple(Some([control, xcontrol]))

///|
pub let type_tuple_if_false : Type = Tuple(Some([xcontrol, control]))

///|
/// Match refs/simple `TypeTuple.RET`: [Ctrl, MemBot, Bottom]
pub let type_tuple_ret : Type = Tuple(Some([control, type_mem_bot, bottom]))

///|
/// Match refs/simple `TypeRPC.BOT` ($[ALL])
pub let type_rpc_bot : Type = RPC({ _any: true, _rpcs: [] })

///|
/// Match refs/simple `TypeFunPtr.BOT`
pub let type_funptr_bot : Type = FunPtr({ _nil: 3, _sig: Some([]), _ret: bottom, _fidxs: -1L, _name: None })

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
  ts.push(Type::mem(1, t=type_integer_zero))
  ts.push(type_mem_bot)
  ts.push(type_nil)
  ts.push(type_mem_ptr_bot)
  ts.push(type_mem_ptr_test)
  ts.push(MemPtr(type_struct_s1, 2))
  ts.push(MemPtr(type_struct_s2, 2))
  ts.push(Tuple(Some([type_integer_bot, type_mem_ptr_test])))
  ts.push(type_tuple_if_both)
  let sz = ts.length()
  for i in 0..<sz {
    ts.push(ts[i].dual())
  }
  ts
}

///|
fn nil_xmeet0(a : Int, b : Int) -> Int {
  if a > b {
    a
  } else {
    b
  }
}

///|
fn nil_dual0(nil : Int) -> Int {
  3 - nil
}

///|
fn nil_is_high(nil : Int) -> Bool {
  nil <= 1
}

///|
fn nil_q(nil : Int) -> String {
  if nil == 1 || nil == 2 {
    ""
  } else {
    "?"
  }
}

///|
fn nil_x(nil : Int) -> String {
  if nil_is_high(nil) {
    "~"
  } else {
    ""
  }
}

///|
pub fn Type::mem(mem_alias : Int, t? : Type = top) -> Type {
  if mem_alias == 0 {
    if t == top {
      type_mem_top
    } else if t == bottom {
      type_mem_bot
    } else {
      panic()
    }
  } else {
    Mem({ _alias: mem_alias, _t: t })
  }
}

///|
pub fn Type::mem_ptr(obj : TypeStruct, nullable? : Bool = false) -> Type {
  MemPtr(obj, if nullable { 3 } else { 2 })
}

///|
pub fn Type::is_constant(self : Type) -> Bool {
  match self {
    Nil => true
    Int(i) => i.is_constant()
    Flt(f) => f.is_constant()
    FunPtr(fp) => fp.is_constant()
    RPC(rpc) => rpc.is_constant()
    _ => false
  }
}

///|
pub fn Type::is_high(self : Type) -> Bool {
  match self {
    Top | XCtrl | XNil => true
    Int(i) => i.is_high()
    Flt(f) => f.is_high()
    Mem(mem) => mem._t.is_high()
    Ptr(nil) => nil_is_high(nil)
    MemPtr(_, nil) => nil_is_high(nil)
    FunPtr(fp) => fp.is_high()
    _ => false
  }
}

///|
pub fn Type::is_high_or_const(self : Type) -> Bool {
  self.is_high() || self.is_constant()
}

///|
pub fn Type::dual(self : Type) -> Type {
  match self {
    Bot => Top
    Top => Bot
    Ctrl => XCtrl
    XCtrl => Ctrl
    Nil => XNil
    XNil => Nil
    Int(i) => Int({ _min: i._max, _max: i._min })
    Flt(f) => if f._sz == 0 { self } else { Flt({ _sz: -f._sz, _con: 0.0 }) }
    Mem(mem) => Mem({ _alias: mem._alias, _t: mem._t.dual() })
    Ptr(nil) => Ptr(nil_dual0(nil))
    MemPtr(obj, nil) => MemPtr(obj.dual(), nil_dual0(nil))
    FunPtr(fp) => FunPtr(fp.dual())
    RPC(rpc) => RPC(rpc.dual())
    Tuple(types) =>
      match types {
        None => Tuple(Some([]))
        Some(ts) =>
          if ts.length() == 0 {
            Tuple(None)
          } else {
            Tuple(Some(ts.map(fn(t) { t.dual() })))
          }
      }
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
    Int(_) => type_integer_bot
    Flt(_) => type_float_bot
    Mem(mem) => Mem({ _alias: mem._alias, _t: mem._t.glb() })
    Ptr(_) => type_ptr_ptr
    MemPtr(obj, _) => MemPtr(obj.glb(), 3)
    FunPtr(fp) => FunPtr(fp.glb())
    Tuple(types) =>
      Tuple(
        match types {
          None => Some([])
          Some(ts) => Some(ts.map(fn(t) { t.glb() }))
        },
      )
    _ => bottom
  }
}

///|
pub fn Type::make_zero(self : Type) -> Type {
  match self {
    Int(_) => type_integer_zero
    Flt(_) => type_float_zero
    _ => type_nil
  }
}

///|
// Kept for compatibility with earlier chapters; chapter18 reference uses makeZero.
pub fn Type::make_init(self : Type) -> Type {
  self.make_zero()
}

///|
pub fn Type::non_zero(self : Type) -> Type {
  match self {
    Int(i) => i.non_zero()
    _ => type_ptr_nptr
  }
}

///|
pub fn Type::is_final(self : Type) -> Bool {
  match self {
    MemPtr(obj, _) => obj.is_final()
    _ => true
  }
}

///|
pub fn Type::make_ro(self : Type) -> Type {
  match self {
    MemPtr(obj, nil) => MemPtr(obj.make_ro(), nil)
    _ => self
  }
}

///|
pub fn Type::log_size(self : Type) -> Int {
  match self {
    Int(i) => i.log_size()
    Flt(f) => f.log_size()
    Ptr(_) | MemPtr(_, _) | FunPtr(_) => 2
    _ => panic()
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
fn type_nil_code_exn(t : Type) -> Int {
  match t {
    Ptr(nil) => nil
    MemPtr(_, nil) => nil
    FunPtr(fp) => fp._nil
    _ => panic()
  }
}

///|
fn type_make_from_nil(t : Type, nil : Int) -> Type {
  match t {
    Ptr(_) => Ptr(nil)
    MemPtr(obj, _) => MemPtr(obj, nil)
    FunPtr(fp) => FunPtr(fp.make_from_nil(nil))
    _ => panic()
  }
}

///|
fn type_meet0_nilable(t : Type) -> Type {
  match t {
    Ptr(nil) => if nil_is_high(nil) { type_nil } else { type_ptr_ptr }
    MemPtr(obj, _) => MemPtr(obj, 3)
    FunPtr(fp) => FunPtr(fp.meet0())
    _ => panic()
  }
}

///|
fn type_meetx_nilable(t : Type) -> Type {
  let nil = type_nil_code_exn(t)
  if nil == 0 {
    type_xnil
  } else if nil <= 2 {
    type_ptr_nptr
  } else {
    type_ptr_ptr
  }
}

///|
fn type_nmeet(lhs : Type, rhs : Type) -> Type {
  // Both args are nil-able (Ptr/MemPtr/FunPtr) and are different variants.
  match (lhs, rhs) {
    (Ptr(n0), other) => {
      let n1 = type_nil_code_exn(other)
      if n0 == 0 {
        other
      } else if n0 == 1 {
        type_make_from_nil(other, nil_xmeet0(n0, n1))
      } else if n0 == 2 {
        if n1 == 3 {
          type_ptr_ptr
        } else {
          type_ptr_nptr
        }
      } else {
        type_ptr_ptr
      }
    }
    (other, Ptr(n1)) => type_nmeet(Ptr(n1), other)
    _ => {
      let n0 = type_nil_code_exn(lhs)
      let n1 = type_nil_code_exn(rhs)
      if n0 == 0 && n1 == 0 {
        type_xnil
      } else if n0 <= 2 && n1 <= 2 {
        type_ptr_nptr
      } else {
        type_ptr_ptr
      }
    }
  }
}

///|

///|
let _meet_depth : Ref[Int] = Ref::{ val: 0 }

///|
fn _dbg_tag(t : Type) -> String {
  match t {
    Bot => "Bot"
    Top => "Top"
    Ctrl => "Ctrl"
    XCtrl => "XCtrl"
    Nil => "Nil"
    XNil => "XNil"
    Int(_) => "Int"
    Flt(_) => "Flt"
    Mem(mem) => "Mem(" + mem._alias.to_string() + ")"
    Ptr(nil) => "Ptr(" + nil.to_string() + ")"
    MemPtr(obj, nil) => "MemPtr(" + obj._name + "," + nil.to_string() + ")"
    FunPtr(fp) => "FunPtr(" + fp._nil.to_string() + ")"
    RPC(_) => "RPC"
    Tuple(_) => "Tuple"
  }
}

///|
pub fn Type::meet(self : Type, other : Type) -> Type {
  _meet_depth.val = _meet_depth.val + 1
  if _meet_depth.val > 2000 {
    println(
      "Type.meet recursion: " + _dbg_tag(self) + " meet " + _dbg_tag(other),
    )
    panic()
  }
  let res = if self == other {
    self
  } else {
    match (self, other) {
      (Bot, _) | (_, Bot) => Bot
      (Top, x) => x
      (x, Top) => x

      // Nil/XNil interactions
      (Nil, XNil) | (XNil, Nil) => type_ptr_ptr
      (Nil, Ptr(_) | MemPtr(_, _) | FunPtr(_)) => type_meet0_nilable(other)
      (Ptr(_) | MemPtr(_, _) | FunPtr(_), Nil) => type_meet0_nilable(self)
      (XNil, Ptr(_) | MemPtr(_, _) | FunPtr(_)) => type_meetx_nilable(other)
      (Ptr(_) | MemPtr(_, _) | FunPtr(_), XNil) => type_meetx_nilable(self)
      (Nil | XNil, _) | (_, Nil | XNil) => bottom

      // Same-type meets
      (Ctrl, XCtrl) | (XCtrl, Ctrl) => Ctrl
      (Ctrl | XCtrl, Ctrl | XCtrl) => Ctrl
      (Int(i0), Int(i1)) =>
        Int({
          _min: if i0._min < i1._min {
            i0._min
          } else {
            i1._min
          },
          _max: if i0._max > i1._max {
            i0._max
          } else {
            i1._max
          },
        })
      (Flt(f0), Flt(f1)) => TypeFloat::xmeet(f0, f1)
      (Mem(m0), Mem(m1)) =>
        if self == type_mem_top {
          Mem(m1)
        } else if other == type_mem_top {
          Mem(m0)
        } else if self == type_mem_bot || other == type_mem_bot {
          type_mem_bot
        } else {
          let alias_id = if m0._alias == m1._alias { m0._alias } else { 0 }
          Mem({ _alias: alias_id, _t: m0._t.meet(m1._t) })
        }
      (Ptr(n0), Ptr(n1)) => Ptr(nil_xmeet0(n0, n1))
      (MemPtr(obj0, n0), MemPtr(obj1, n1)) =>
        MemPtr(obj0.meet(obj1), nil_xmeet0(n0, n1))
      (FunPtr(fp0), FunPtr(fp1)) => FunPtr(fp0.xmeet(fp1))
      (Tuple(ts0), Tuple(ts1)) =>
        match (ts0, ts1) {
          (None, _) => other
          (_, None) => self
          (Some(a0), Some(a1)) =>
            if a0.length() != a1.length() {
              Tuple(Some([]))
            } else {
              Tuple(Some(a0.mapi(fn(i, t0) { t0.meet(a1[i]) })))
            }
        }

      // Mismatched nil-able meets
      (Ptr(_) | MemPtr(_, _) | FunPtr(_), Ptr(_) | MemPtr(_, _) | FunPtr(_)) =>
        type_nmeet(self, other)
      (RPC(r0), RPC(r1)) => RPC(r0.xmeet(r1))
      _ => bottom
    }
  }
  _meet_depth.val = _meet_depth.val - 1
  res
}

///|
pub fn Type::hash_code(self : Type) -> Int {
  let mix = fn(v : Int) -> Int { v ^ (v << 17) ^ (v >> 13) }
  match self {
    Bot => 0x01
    Top => 0x02
    Ctrl => 0x03
    XCtrl => 0x04
    Nil => 0x05
    XNil => 0x06
    Int(i) => mix(0x10 ^ i._min.hash() ^ i._max.hash())
    Flt(f) => mix(0x18 ^ f._con.hash() ^ f._sz)
    Mem(mem) => mix(0x30 ^ mem._alias ^ mem._t.hash_code())
    Ptr(nil) => mix(0x38 ^ nil)
    MemPtr(obj, nil) => mix(0x40 ^ obj.hash_code() ^ (nil << 12))
    FunPtr(fp) => mix(0x48 ^ fp.hash_code())
    RPC(rpc) => mix(0x50 ^ rpc.hash_code())
    Tuple(types) =>
      match types {
        None => mix(0x20 ^ 0x12345)
        Some(ts) => {
          let mut sum = 0x20
          for t in ts {
            sum = mix(sum ^ t.hash_code())
          }
          sum
        }
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
    Nil => sb.write_string("null")
    XNil => sb.write_string("~nil")
    Int(i) => sb.write_string(i.str())
    Flt(f) => f.print_to(sb)
    Ptr(nil) => {
      let strs = ["~ptr", "~nptr", "nptr", "ptr"]
      sb.write_string(strs[nil])
    }
    MemPtr(_, _) | FunPtr(_) | RPC(_) => sb.write_string(self.str())
    Mem(mem) => {
      sb.write_string("#")
      if mem._alias == 0 {
        sb.write_string(if mem._t == top { "TOP" } else { "BOT" })
      } else {
        sb.write_string(mem._alias.to_string())
        sb.write_string(":")
        mem._t.print_to(sb)
      }
    }
    Tuple(types) =>
      match types {
        None => sb.write_string("[TOP]")
        Some(ts) =>
          if ts.length() == 0 {
            sb.write_string("[BOT]")
          } else {
            sb.write_string("[  ")
            let mut first = true
            for t in ts {
              if !first {
                sb.write_string(", ")
              }
              first = false
              t.print_to(sb)
            }
            sb.write_string("]")
          }
      }
  }
}

///|
pub fn Type::str(self : Type) -> String {
  match self {
    Bot => "Bot"
    Top => "Top"
    Ctrl => "Ctrl"
    XCtrl => "~Ctrl"
    Nil => "null"
    XNil => "~nil"
    Int(i) => i.str()
    Flt(f) => f.str()
    Mem(mem) => {
      let sb = StringBuilder::new()
      sb.write_string("#")
      if mem._alias == 0 {
        sb.write_string(if mem._t == top { "TOP" } else { "BOT" })
      } else {
        sb.write_string(mem._alias.to_string())
        sb.write_string(":")
        mem._t.print_to(sb)
      }
      sb.to_string()
    }
    Ptr(nil) => {
      let strs = ["~ptr", "~nptr", "nptr", "ptr"]
      strs[nil]
    }
    MemPtr(obj, nil) =>
      if self == type_mem_ptr_voidptr {
        "*void"
      } else if self == type_mem_ptr_bot {
        "*void?"
      } else {
        nil_x(nil) + "*" + obj.str() + nil_q(nil)
      }
    FunPtr(fp) => fp.str()
    RPC(rpc) => rpc.str()
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
  let x = self._min ^ self._max
  let ff1 = 1L << (63 - x.clz())
  self._min | ((ff1 - 1L) | ff1)
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
pub fn TypeInteger::log_size(self : TypeInteger) -> Int {
  // 0(byte), 1(i16/u16), 2(i32/f32), 3(i64/dbl)
  if self._min == 0L && self._max == 1L {
    return 0
  }
  if (self._min == -128L && self._max == 127L) ||
    (self._min == 0L && self._max == 255L) {
    return 0
  }
  if (self._min == -32768L && self._max == 32767L) ||
    (self._min == 0L && self._max == 65535L) {
    return 1
  }
  if (self._min == -(1L << 31) && self._max == (1L << 31) - 1L) ||
    (self._min == 0L && self._max == (1L << 32) - 1L) {
    return 2
  }
  if self._min == long_min_value && self._max == long_max_value {
    return 3
  }
  panic()
}

///|
pub fn TypeInteger::non_zero(self : TypeInteger) -> Type {
  if self.is_high() {
    return Int(self)
  }
  if self._min == 0L {
    return TypeInteger::make(1L, self._max)
  }
  if self._max == 0L {
    return TypeInteger::make(self._min, -1L)
  }
  Int(self)
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
pub fn TypeFloat::log_size(self : TypeFloat) -> Int {
  if self._sz == 32 {
    2
  } else {
    3
  }
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
    return if i0._sz == 0 && !i0.is_f32() {
      type_float_bot
    } else {
      type_float_b32
    }
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
    let base = TypeFloat::to_java_string(self._con)
    if self.is_f32() {
      sb.write_string(base)
      sb.write_string("f")
    } else {
      sb.write_string(base)
    }
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
  if self.is_f32() {
    base + "f"
  } else {
    base
  }
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
pub fn Field::make(
  fname : String,
  typ : Type,
  alias_ : Int,
  xfinal : Bool,
) -> Field {
  { _fname: fname, _type: typ, _alias: alias_, _final: xfinal }
}

///|
pub fn Field::make_from(self : Field, typ : Type) -> Field {
  { _fname: self._fname, _type: typ, _alias: self._alias, _final: self._final }
}

///|
pub fn Field::make_ro(self : Field) -> Field {
  if self._final {
    self
  } else {
    Field::make(self._fname, self._type.make_ro(), self._alias, true)
  }
}

///|
pub fn Field::is_final(self : Field) -> Bool {
  self._final && self._type.is_final()
}

///|
pub fn TypeStruct::make(name : String, fields : Array[Field]) -> TypeStruct {
  { _name: name, _fields: Some(fields) }
}

///|
pub fn TypeStruct::is_fref(self : TypeStruct) -> Bool {
  self._fields is None
}

///|
pub fn TypeStruct::is_final(self : TypeStruct) -> Bool {
  match self._fields {
    None => true
    Some(fields) => {
      for f in fields {
        if !f.is_final() {
          return false
        }
      }
      true
    }
  }
}

///|
pub fn TypeStruct::make_ro(self : TypeStruct) -> TypeStruct {
  if self.is_final() {
    return self
  }
  match self._fields {
    None => self
    Some(fields) =>
      TypeStruct::make(self._name, fields.map(fn(f) { f.make_ro() }))
  }
}

///|
pub fn TypeStruct::make_ary(
  len : Type,
  len_alias : Int,
  body : Type,
  body_alias : Int,
) -> TypeStruct {
  match body {
    // Arrays of reference types must always be nullable.
    MemPtr(_, nil) if nil == 1 || nil == 2 => panic()
    _ => ()
  }
  TypeStruct::make("[" + body.str() + "]", [
    Field::make("#", len, len_alias, true),
    Field::make("[]", body, body_alias, false),
  ])
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
pub fn TypeStruct::find_alias(self : TypeStruct, alias_id : Int) -> Int {
  match self._fields {
    None => ()
    Some(fields) =>
      for i, field in fields {
        if field._alias == alias_id {
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
    (None, _) => return other
    (_, None) => return self
    (Some(f0s), Some(f1s)) =>
      if f0s.length() != f1s.length() {
        return type_struct_bot
      } else {
        let fields : Array[Field] = []
        for i, f0 in f0s {
          let f1 = f1s[i]
          if f0._fname != f1._fname || f0._alias != f1._alias {
            return type_struct_bot
          }
          fields.push(
            Field::make(
              f0._fname,
              f0._type.meet(f1._type),
              f0._alias,
              f0._final || f1._final,
            ),
          )
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
        fields.push(Field::make(f._fname, f._type.dual(), f._alias, !f._final))
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
        fields.push(Field::make(f._fname, f._type.glb(), f._alias, true))
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
        sum = mix(
          sum ^
          f._fname.hash() ^
          f._alias ^
          f._type.hash_code() ^
          (if f._final { 1024 } else { 0 }),
        )
      }
  }
  sum
}

///|
pub fn TypeStruct::str(self : TypeStruct) -> String {
  self._name
}

///|
pub fn TypeStruct::is_ary(self : TypeStruct) -> Bool {
  match self._fields {
    Some(fields) => fields.length() == 2 && fields[1]._fname == "[]"
    None => false
  }
}

///|
pub fn TypeStruct::ary_base(self : TypeStruct) -> Int {
  if !self.is_ary() {
    panic()
  }
  self.offset(1)
}

///|
pub fn TypeStruct::ary_scale(self : TypeStruct) -> Int {
  if !self.is_ary() {
    panic()
  }
  match self._fields {
    Some(fields) => fields[1]._type.log_size()
    None => panic()
  }
}

///|
pub fn TypeStruct::offset(self : TypeStruct, idx : Int) -> Int {
  let offs = self.offsets()
  if idx < 0 || idx >= offs.length() {
    panic()
  }
  offs[idx]
}

///|
fn TypeStruct::offsets(self : TypeStruct) -> Array[Int] {
  let fields = match self._fields {
    Some(fields) => fields
    None => panic()
  }
  let cnts : Array[Int] = Array::make(4, 0)
  for f in fields {
    let log = f._type.log_size()
    if log < 0 || log >= 4 {
      panic()
    }
    cnts[log] = cnts[log] + 1
  }
  let mut off = 0
  let offs : Array[Int] = Array::make(4, 0)
  for i = 3; i >= 0; i = i - 1 {
    offs[i] = off
    off += cnts[i] << i
  }
  let out : Array[Int] = Array::make(fields.length() + 1, 0)
  let mut idx = 0
  for f in fields {
    let log = f._type.log_size()
    out[idx] = offs[log]
    idx = idx + 1
    offs[log] = offs[log] + (1 << log)
    cnts[log] = cnts[log] - 1
  }
  out[fields.length()] = (off + 7) & -8
  out
}

///|
pub fn TypeStruct::make_forward(name : String) -> TypeStruct {
  { _name: name, _fields: None }
}

///|
pub fn TypeRPC::is_constant(self : TypeRPC) -> Bool {
  !self._any && self._rpcs.length() == 1
}

///|
pub fn TypeRPC::dual(self : TypeRPC) -> TypeRPC {
  { _any: !self._any, _rpcs: self._rpcs }
}

///|
pub fn TypeRPC::hash_code(self : TypeRPC) -> Int {
  let mut h = if self._any { -1 } else { 0 }
  for rpc in self._rpcs {
    h = h ^ rpc
  }
  h
}

///|
pub fn TypeRPC::str(self : TypeRPC) -> String {
  if self._rpcs.is_empty() {
    return if self._any { "$[ALL]" } else { "$[]" }
  }
  if self._rpcs.length() == 1 {
    return if self._any {
      "$[-\{self._rpcs[0]}]"
    } else {
      "$[\{self._rpcs[0]}]"
    }
  }
  // Match refs/simple formatting roughly (set-like display).
  let rpcs = self._rpcs.copy()
  rpcs.sort()
  rpcs.dedup()
  let sb = StringBuilder::new()
  sb.write_string("$[")
  if self._any {
    sb.write_string("-")
  }
  sb.write_string("[")
  let mut first = true
  for rpc in rpcs {
    if !first {
      sb.write_string(", ")
    }
    first = false
    sb.write_string(rpc.to_string())
  }
  sb.write_string("]]")
  sb.to_string()
}

///|
pub fn TypeRPC::xmeet(self : TypeRPC, other : TypeRPC) -> TypeRPC {
  // Canonicalize for deterministic Eq/printing.
  let lhs = self._rpcs.copy()
  lhs.sort()
  lhs.dedup()
  let rhs = other._rpcs.copy()
  rhs.sort()
  rhs.dedup()
  if lhs == rhs {
    // Equal sets with opposite _any collapse to BOT ($[ALL]).
    return { _any: true, _rpcs: [] }
  }
  if self._any && other._any {
    // Union of complements => complement of intersection.
    let out : Array[Int] = []
    let mut i = 0
    let mut j = 0
    while i < lhs.length() && j < rhs.length() {
      if lhs[i] == rhs[j] {
        out.push(lhs[i])
        i = i + 1
        j = j + 1
      } else if lhs[i] < rhs[j] {
        i = i + 1
      } else {
        j = j + 1
      }
    }
    return { _any: true, _rpcs: out }
  }
  if !self._any && !other._any {
    // Union of finite sets.
    let out : Array[Int] = []
    let mut i = 0
    let mut j = 0
    while i < lhs.length() || j < rhs.length() {
      if j >= rhs.length() || (i < lhs.length() && lhs[i] < rhs[j]) {
        out.push(lhs[i])
        i = i + 1
      } else if i >= lhs.length() || rhs[j] < lhs[i] {
        out.push(rhs[j])
        j = j + 1
      } else {
        out.push(lhs[i])
        i = i + 1
        j = j + 1
      }
    }
    out.dedup()
    return { _any: false, _rpcs: out }
  }

  // Union of (Universe \\ inf) with finite => Universe \\ (inf \\ finite).
  let (inf, sub) = if self._any { (lhs, rhs) } else { (rhs, lhs) }
  let out : Array[Int] = []
  let mut i = 0
  let mut j = 0
  while i < inf.length() {
    if j >= sub.length() || inf[i] < sub[j] {
      out.push(inf[i])
      i = i + 1
    } else if sub[j] < inf[i] {
      j = j + 1
    } else {
      // Remove items present in sub.
      i = i + 1
      j = j + 1
    }
  }
  { _any: true, _rpcs: out }
}

///|
pub fn TypeFunPtr::is_high(self : TypeFunPtr) -> Bool {
  self._nil <= 1 || (self._nil == 2 && self._fidxs == 0L)
}

///|
pub fn TypeFunPtr::not_null(self : TypeFunPtr) -> Bool {
  // Match refs/simple: nullable when nil is 0/3.
  self._nil == 1 || self._nil == 2
}

///|
pub fn TypeFunPtr::arg(self : TypeFunPtr, i : Int) -> Type {
  match self._sig {
    Some(ts) => ts[i]
    None => panic()
  }
}

///|
pub fn TypeFunPtr::nargs(self : TypeFunPtr) -> Int {
  match self._sig {
    Some(ts) => ts.length()
    None => 0
  }
}

///|
pub fn TypeFunPtr::ret(self : TypeFunPtr) -> Type {
  self._ret
}

///|
pub fn TypeFunPtr::fidxs(self : TypeFunPtr) -> Int64 {
  self._fidxs
}

///|
pub fn TypeFunPtr::make_from_ret(self : TypeFunPtr, ret : Type) -> TypeFunPtr {
  if ret == self._ret {
    self
  } else {
    { ..self, _ret: ret, _name: None }
  }
}

///|
pub fn TypeFunPtr::make_from_fidx(self : TypeFunPtr, fidx : Int) -> TypeFunPtr {
  // Match refs/simple: makeFrom(fidx) always yields a not-null constant funptr.
  { ..self, _nil: 2, _fidxs: 1L << fidx, _name: None }
}

///|
pub fn TypeFunPtr::next_fidx(fidxs : Int64) -> Int64 {
  // Iterate low-bit sets: x & (x-1)
  fidxs.land(fidxs - 1L)
}

///|
pub fn TypeFunPtr::is_constant(self : TypeFunPtr) -> Bool {
  (self._nil == 2 && self._fidxs.popcnt() == 1) ||
  (self._nil == 3 && self._fidxs == 0L)
}

///|
pub fn TypeFunPtr::make_from_nil(self : TypeFunPtr, nil : Int) -> TypeFunPtr {
  if nil == self._nil {
    self
  } else {
    { ..self, _nil: nil }
  }
}

///|
pub fn TypeFunPtr::meet0(self : TypeFunPtr) -> TypeFunPtr {
  self.make_from_nil(3)
}

///|
pub fn TypeFunPtr::dual(self : TypeFunPtr) -> TypeFunPtr {
  let sig_dual = match Type::Tuple(self._sig).dual() {
    Type::Tuple(ts) => ts
    _ => panic()
  }
  {
    ..self,
    _nil: nil_dual0(self._nil),
    _sig: sig_dual,
    _ret: self._ret.dual(),
    _fidxs: self._fidxs ^ -1L,
  }
}

///|
pub fn TypeFunPtr::glb(self : TypeFunPtr) -> TypeFunPtr {
  { _nil: 3, _sig: self._sig, _ret: self._ret, _fidxs: -1L, _name: None }
}

///|
pub fn TypeFunPtr::hash_code(self : TypeFunPtr) -> Int {
  let mix = fn(v : Int) -> Int { v ^ (v << 17) ^ (v >> 13) }
  let mut h = mix(
    0x5000 ^ (self._nil << 3) ^ self._ret.hash_code() ^ self._fidxs.hash(),
  )
  match self._sig {
    None => h = mix(h ^ 0x12345)
    Some(ts) =>
      for t in ts {
        h = mix(h ^ t.hash_code())
      }
  }
  h
}

///|
pub fn TypeFunPtr::xmeet(self : TypeFunPtr, other : TypeFunPtr) -> TypeFunPtr {
  let sig = match Type::Tuple(self._sig).meet(Type::Tuple(other._sig)) {
    Type::Tuple(ts) => ts
    _ => panic()
  }
  {
    _nil: if self._nil > other._nil {
      self._nil
    } else {
      other._nil
    },
    _sig: sig,
    _ret: self._ret.meet(other._ret),
    _fidxs: self._fidxs | other._fidxs,
    _name: None,
  }
}

///|
pub fn TypeFunPtr::set_name(self : TypeFunPtr, name : String?) -> TypeFunPtr {
  match name {
    None => self
    Some(n) => {
      // Debug-only: names only make sense for exact single-function pointers.
      if self._fidxs <= 0L || self._fidxs.popcnt() != 1 {
        panic()
      }
      { ..self, _name: Some(n) }
    }
  }
}

///|
pub fn TypeFunPtr::str(self : TypeFunPtr) -> String {
  let sb = StringBuilder::new()
  sb.write_string(nil_x(self._nil))
  sb.write_string("{ ")
  // Match refs/simple: printing never uses a debug name; names live on Fun nodes.
  match self._sig {
    None => ()
    Some(ts) =>
      for t in ts {
        t.print_to(sb)
        sb.write_string(" ")
      }
  }
  sb.write_string("-> ")
  self._ret.print_to(sb)
  sb.write_string(" #")
  if self.is_high() {
    sb.write_string("~")
  }
  let fidxs = if self.is_high() { self._fidxs ^ -1L } else { self._fidxs }
  if fidxs == -1L {
    sb.write_string("ALL")
  } else if fidxs != 0L {
    if fidxs.popcnt() == 1 {
      sb.write_string(fidxs.ctz().to_string())
    } else {
      // Rare in tests; keep a compact form.
      sb.write_string("b")
      sb.write_string(fidxs.to_string(radix=2))
    }
  }
  sb.write_string("}")
  sb.write_string(nil_q(self._nil))
  sb.to_string()
}
