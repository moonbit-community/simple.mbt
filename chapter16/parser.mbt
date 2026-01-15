///|
pub(all) suberror ParseError {
  Msg(String)
} derive(Show, Eq)

///|
struct Parser {
  mut _lexer : Lexer
  mut _scope : Node
  mut _stop : Node
  mut _continue_scope : Node?
  mut _break_scope : Node?
}

///|
let types : Ref[Map[String, Type]] = Ref::{ val: Map::new() }

let next_alias : Ref[Int] = Ref::{ val: 2 }

let inits : Ref[Map[String, Node]] = Ref::{ val: Map::new() }

///|
pub let scheduled : Ref[Bool] = Ref::{ val: false }

///|
pub fn Parser::new(source : String) -> Parser {
  Parser::new_with_arg(source, type_integer_bot)
}

///|
pub fn Parser::new_with_arg(source : String, arg : Type) -> Parser {
  Node::reset()
  IterPeeps::reset()
  types.val = Map::new()
  types.val["bool"] = type_integer_u1
  types.val["byte"] = type_integer_u8
  types.val["f32"] = type_float_b32
  types.val["f64"] = type_float_bot
  types.val["flt"] = type_float_bot
  types.val["i16"] = type_integer_i16
  types.val["i32"] = type_integer_i32
  types.val["i64"] = type_integer_bot
  types.val["i8"] = type_integer_i8
  types.val["int"] = type_integer_bot
  types.val["u1"] = type_integer_u1
  types.val["u16"] = type_integer_u16
  types.val["u32"] = type_integer_u32
  types.val["u8"] = type_integer_u8
  scheduled.val = false
  next_alias.val = 2
  inits.val = Map::new()
  let lexer = Lexer::new(source)
  let scope = Node::new_scope()
  start.val = Node::new_start([control, type_mem_top, arg])
  let stop = Node::new_stop()
  zero.val = Node::new_constant(type_integer_zero).peephole().keep()
  xctrl.val = Node::new_xctrl().peephole().keep()
  {
    _lexer: lexer,
    _scope: scope,
    _stop: stop,
    _continue_scope: None,
    _break_scope: None,
  }
}

///|
pub fn Parser::src(self : Parser) -> String {
  self._lexer._input.to_string()
}

///|
pub fn Parser::parse(
  self : Parser,
  show? : Bool = false,
) -> Node raise ParseError {
  self._scope.push()
  let mem = Node::new_mem()
  ignore(mem.add_def(None))
  ignore(
    mem.add_def(Some(Node::new_proj(start.val, 1, scope_mem0).peephole())),
  )
  ignore(
    self._scope.define_(
      scope_ctrl,
      control,
      false,
      Node::new_cproj(start.val, 0, scope_ctrl).peephole(),
    ),
  )
  ignore(
    self._scope.define_(scope_mem0, type_mem_top, false, mem.peephole()),
  )
  ignore(
    self._scope.define_(
      scope_arg0,
      type_integer_bot,
      false,
      Node::new_proj(start.val, 2, scope_arg0).peephole(),
    ),
  )
  self.parse_block()
  if self._scope.input_exn(0).ty() == control {
    let ret = Node::new_return(
      Some(self._scope.input_exn(0)),
      Node::new_constant(type_integer_zero).peephole(),
      self._scope,
    ).peephole()
    ignore(self._stop.add_return(ret))
  }
  self._scope.pop()
  for _, init in inits.val {
    ignore(init.unkeep())
    init.kill()
  }
  inits.val = Map::new()
  if !self._lexer.is_eof() {
    raise ParseError::Msg(
      "Syntax error, unexpected \{self._lexer.get_any_next_token()}",
    )
  }
  ignore(self._stop.peephole())
  if show {
    ignore(self.show_graph())
  }
  self._stop
}

///|
fn Parser::parse_block(self : Parser) -> Unit raise ParseError {
  self._scope.push()
  while !self._lexer.peek_char('}') && !self._lexer.is_eof() {
    self.parse_statement()
  }
  self._scope.pop()
}

///|
fn Parser::parse_statement(self : Parser) -> Unit raise ParseError {
  if self._lexer.matchx_syntax("return") {
    ignore(self.parse_return())
  } else if self._lexer.match_syntax("{") {
    self.parse_block()
    self.require_syntax("}")
  } else if self._lexer.matchx_syntax("if") {
    ignore(self.parse_if())
  } else if self._lexer.matchx_syntax("while") {
    ignore(self.parse_while())
  } else if self._lexer.matchx_syntax("break") {
    ignore(self.parse_break())
  } else if self._lexer.matchx_syntax("continue") {
    ignore(self.parse_continue())
  } else if self._lexer.matchx_syntax("struct") {
    self.parse_struct()
  } else if self._lexer.matchx_syntax("#showGraph") {
    ignore(self.show_graph())
    self.require_syntax(";")
  } else if self._lexer.matchx_syntax(";") {
    ()
  } else {
    ignore(self.parse_expression_statement())
  }
}

///|
///|
fn Parser::parse_struct(self : Parser) -> Unit raise ParseError {
  if self._scope._lex_size.length() > 2 {
    raise ParseError::Msg(
      self.error_syntax("struct declarations can only appear in top level scope"),
    )
  }
  let type_name = self.require_id()
  match types.val.get(type_name) {
    Some(t) =>
      match t {
        MemPtr(obj, _) =>
          match obj._fields {
            None => ()
            Some(_) =>
              raise ParseError::Msg(
                self.error_syntax("struct '\{type_name}' cannot be redefined"),
              )
          }
        _ =>
          raise ParseError::Msg(
            self.error_syntax("struct '\{type_name}' cannot be redefined"),
          )
      }
    None => ()
  }

  // Parse the struct body as a block, and inspect the scope afterward for fields.
  self._scope.push()
  self.require_syntax("{")
  while !self._lexer.peek_char('}') && !self._lexer.is_eof() {
    self.parse_statement()
  }

  let lexlen =
    match self._scope._lex_size.last() {
      Some(n) => n
      None => panic()
    }
  let varlen = self._scope._vars.length()
  let s = Node::new_struct()
  let fields : Array[Field] = []
  for i = lexlen; i < varlen; i = i + 1 {
    ignore(s.add_def(self._scope.input(i)))
    let v = self._scope._vars[i]
    let alias_id = next_alias.val
    next_alias.val = next_alias.val + 1
    fields.push(Field::make(v._name, v._type, alias_id, v._final))
  }
  let ts = TypeStruct::make(type_name, fields)
  s._struct_ts = Some(ts)
  types.val[type_name] = MemPtr(ts, false)
  inits.val[type_name] = s.peephole().keep()
  self.require_syntax("}")
  self.require_syntax(";")
  self._scope.pop()
}

///|
fn Parser::parse_if(self : Parser) -> Node raise ParseError {
  self.require_syntax("(")
  let pred = self.require(self.parse_expression(), ")").keep()
  let if_node = Node::new_if(self._scope.input(0), pred).peephole()
  let if_t = Node::new_cproj(if_node.keep(), 0, "True").peephole().keep()
  let if_f = Node::new_cproj(if_node.unkeep(), 1, "False").peephole().keep()
  let ndefs = self._scope.n_ins()
  let mut f_scope = self._scope.dup()
  let if_t_ctrl = if_t.unkeep()
  ignore(self._scope.set_def(0, Some(if_t_ctrl)))
  ignore(self._scope.upcast_(if_t_ctrl, pred, false))
  self.parse_statement()
  let t_scope = self._scope
  self._scope = f_scope
  let if_f_ctrl = if_f.unkeep()
  ignore(self._scope.set_def(0, Some(if_f_ctrl)))
  ignore(self._scope.upcast_(if_f_ctrl, pred, true))
  if self._lexer.matchx_syntax("else") {
    self.parse_statement()
    f_scope = self._scope
  }
  ignore(pred.unkeep())
  if t_scope.n_ins() != ndefs || f_scope.n_ins() != ndefs {
    raise ParseError::Msg("Cannot define a new name on one arm of an if")
  }
  self._scope = t_scope
  let r = self._scope.merge_scopes(f_scope)
  ignore(self._scope.set_def(0, Some(r)))
  r
}

///|
fn Parser::parse_while(self : Parser) -> Node raise ParseError {
  let saved_continue_scope = self._continue_scope
  let saved_break_scope = self._break_scope
  self.require_syntax("(")
  ignore(
    self._scope.set_def(
      0,
      Some(Node::new_loop(self._scope.input(0)).peephole()),
    ),
  )
  let head = self._scope.keep()
  self._scope = self._scope.dup(is_loop=true)
  let pred = self.require(self.parse_expression(), ")")
  let if_node = Node::new_if(self._scope.input(0), pred).keep().peephole()
  let if_t = Node::new_cproj(if_node, 0, "True").peephole()
  ignore(if_node.unkeep())
  let if_f = Node::new_cproj(if_node, 1, "False").peephole()
  ignore(self._scope.set_def(0, Some(if_f)))
  self._break_scope = Some(self._scope.dup())
  self._continue_scope = None
  ignore(self._scope.set_def(0, Some(if_t)))
  self.parse_statement()
  if self._continue_scope is Some(_) {
    let cont = self.jump_to(self._continue_scope)
    self._continue_scope = Some(cont)
    self._scope.kill()
    self._scope = cont
  }
  let exit = match self._break_scope {
    Some(exit) => exit
    None => panic()
  }
  head.end_loop(self._scope, exit)
  head.unkeep().kill()
  self._continue_scope = saved_continue_scope
  self._break_scope = saved_break_scope
  self._scope = exit
  exit
}

///|
fn Parser::jump_to(self : Parser, to_scope : Node?) -> Node {
  let cur = self._scope.dup()
  ignore(self._scope.set_def(0, Some(xctrl.val)))
  let break_scope = match self._break_scope {
    Some(s) => s
    None => panic()
  }
  while cur._lex_size.length() > break_scope._lex_size.length() {
    cur.pop()
  }
  match to_scope {
    None => cur
    Some(to_scope) => {
      ignore(to_scope.merge_scopes(cur))
      to_scope
    }
  }
}

///|
fn Parser::check_loop_active(self : Parser) -> Unit raise ParseError {
  if self._break_scope is None {
    raise ParseError::Msg("No active loop for a break or continue")
  }
}

///|
fn Parser::parse_break(self : Parser) -> Node raise ParseError {
  self.check_loop_active()
  let scope = self.require(self.jump_to(self._break_scope), ";")
  self._break_scope = Some(scope)
  scope
}

///|
fn Parser::parse_continue(self : Parser) -> Node raise ParseError {
  self.check_loop_active()
  let scope = self.require(self.jump_to(self._continue_scope), ";")
  self._continue_scope = Some(scope)
  scope
}

///|
fn Parser::parse_return(self : Parser) -> Node raise ParseError {
  let expr = self.require(self.parse_expression(), ";")
  let ret = self._stop.add_return(
    Node::new_return(self._scope.input(0), expr, self._scope).peephole(),
  )
  ignore(self._scope.set_def(0, Some(xctrl.val)))
  ret
}

///|
fn Parser::show_graph(_self : Parser) -> Node? {
  None
}

///|
fn Parser::parse_type(self : Parser) -> Type? raise ParseError {
  let old1 = self._lexer._position
  let tname = self._lexer.match_id()
  match tname {
    None => None
    Some(tname) => {
      let t0 = types.val.get(tname)
      let mut t1 = match t0 {
        Some(t) => t
        None => MemPtr(TypeStruct::make_forward(tname), false)
      }

      while true {
        if self._lexer.match_syntax("?") {
          match t1 {
            MemPtr(obj, nil) =>
              if nil {
                raise ParseError::Msg("Type \{t1.str()} already allows null")
              } else {
                t1 = MemPtr(obj, true)
                continue
              }
            _ => raise ParseError::Msg("Type \{t1.str()} cannot be null")
          }
        }
        if self._lexer.match_syntax("[]") {
          t1 = self.type_ary(t1)
          continue
        }
        break
      }

      match t0 {
        Some(_) => Some(t1)
        None => {
          let old2 = self._lexer._position
          match self._lexer.match_id() {
            None => {
              self._lexer._position = old1
              None
            }
            Some(_) => {
              self._lexer._position = old2
              types.val[tname] = t1
              Some(t1)
            }
          }
        }
      }
    }
  }
}

fn Parser::type_ary(self : Parser, t : Type) -> Type raise ParseError {
  match t {
    MemPtr(_, nil) if !nil =>
      raise ParseError::Msg("Arrays of reference types must always be nullable")
    _ => ()
  }

  let tname = "[" + t.str() + "]"
  match types.val.get(tname) {
    Some(ta) => ta
    None => {
      let len_alias = next_alias.val
      next_alias.val = next_alias.val + 1
      let body_alias = next_alias.val
      next_alias.val = next_alias.val + 1
      let ts = TypeStruct::make_ary(type_integer_bot, len_alias, t, body_alias)
      let tary = MemPtr(ts, false)
      types.val[tname] = tary
      tary
    }
  }
}

///|
fn Parser::parse_expression_statement(self : Parser) -> Node raise ParseError {
  let n =
    match self.parse_type() {
      Some(t) => {
        let mut last = self.parse_final(t)
        while self._lexer.match_syntax(",") {
          last = self.parse_final(t)
        }
        last
      }
      None =>
        match self.parse_asgn(None, false) {
          Some(asgn) => asgn
          None => self.parse_expression()
        }
    }
  self.require(n, ";")
}

///|
fn Parser::parse_asgn(
  self : Parser,
  t : Type?,
  xfinal : Bool,
) -> Node? raise ParseError {
  let is_decl = t is Some(_)
  let old = self._lexer._position
  let name = self.require_id()

  let mut expr =
    if self._lexer.peek_char(';') || self._lexer.peek_char(',') {
      match t {
        None => raise ParseError::Msg(self.error_syntax("expression"))
        Some(t) => {
          let init =
            if xfinal {
              top
            } else {
              match t {
                MemPtr(_, nil) if !nil => top
                _ => t.make_init()
              }
            }
          Node::new_constant(init).peephole()
        }
      }
    } else if !self._lexer.match_syntax("=") {
      self._lexer._position = old
      return None
    } else {
      self.parse_expression()
    }

  let declared =
    match t {
      Some(t) => t
      None =>
        match self._scope.lookup(name) {
          None => raise ParseError::Msg("Undefined name '\{name}'")
          Some(def) => {
            if self._scope.input_exn(def._idx).ty() != top && def._final {
              raise ParseError::Msg("Cannot reassign final '\{name}'")
            }
            def._type
          }
        }
    }

  if _is_int_type(expr.ty()) && _is_float_type(declared) {
    expr = Node::new_to_float(expr).peephole()
  }
  expr = self.zs_mask(expr, declared)
  let mut expr_ty = expr.ty()
  match expr_ty {
    MemPtr(obj, nil) =>
      match obj._fields {
        None =>
          match types.val.get(obj._name) {
            Some(MemPtr(obj0, _)) => expr_ty = MemPtr(obj0, nil)
            _ => ()
          }
        Some(_) => ()
      }
    _ => ()
  }
  if !expr_ty.isa(declared) {
    raise ParseError::Msg(
      "Type \{expr_ty.str()} is not of declared type \{declared.str()}",
    )
  }

  if is_decl {
    if !self._scope.define_(name, declared, xfinal, expr) {
      raise ParseError::Msg("Redefining name '\{name}'")
    }
  } else {
    self._scope.update(name, expr)
  }
  Some(expr)
}

///|
fn Parser::parse_final(self : Parser, t : Type) -> Node raise ParseError {
  let xfinal = self._lexer.match_syntax("!")
  match self.parse_asgn(Some(t), xfinal) {
    Some(n) => n
    None => raise ParseError::Msg(self.error_syntax("="))
  }
}

///|
fn Parser::parse_expression(self : Parser) -> Node raise ParseError {
  self.parse_bitwise()
}

///|
fn Parser::parse_bitwise(self : Parser) -> Node raise ParseError {
  let mut lhs = self.parse_comparison()
  while true {
    if self._lexer.match_syntax("&") {
      lhs = Node::new_and(lhs, self.parse_comparison()).peephole()
    } else if self._lexer.match_syntax("|") {
      lhs = Node::new_or(lhs, self.parse_comparison()).peephole()
    } else if self._lexer.match_syntax("^") {
      lhs = Node::new_xor(lhs, self.parse_comparison()).peephole()
    } else {
      break
    }
  }
  lhs
}

///|
fn Parser::parse_comparison(self : Parser) -> Node raise ParseError {
  let mut lhs = self.parse_shift()
  while true {
    if self._lexer.match_syntax("==") {
      lhs = Node::new_bool_eq(lhs, self.parse_shift()).widen().peephole()
    } else if self._lexer.match_syntax("!=") {
      lhs =
        Node::new_not(
          Node::new_bool_eq(lhs, self.parse_shift()).widen().peephole(),
        ).peephole()
    } else if self._lexer.match_syntax("<=") {
      lhs = Node::new_bool_le(lhs, self.parse_shift()).widen().peephole()
    } else if self._lexer.match_syntax("<") {
      lhs = Node::new_bool_lt(lhs, self.parse_shift()).widen().peephole()
    } else if self._lexer.match_syntax(">=") {
      lhs = Node::new_bool_le(self.parse_shift(), lhs).widen().peephole()
    } else if self._lexer.match_syntax(">") {
      lhs = Node::new_bool_lt(self.parse_shift(), lhs).widen().peephole()
    } else {
      break
    }
  }
  lhs
}

///|
fn Parser::parse_shift(self : Parser) -> Node raise ParseError {
  let mut lhs = self.parse_addition()
  while true {
    if self._lexer.match_syntax("<<") {
      lhs = Node::new_shl(lhs, self.parse_addition()).widen().peephole()
    } else if self._lexer.match_syntax(">>>") {
      lhs = Node::new_shr(lhs, self.parse_addition()).widen().peephole()
    } else if self._lexer.match_syntax(">>") {
      lhs = Node::new_sar(lhs, self.parse_addition()).widen().peephole()
    } else {
      break
    }
  }
  lhs
}

///|
fn Parser::parse_addition(self : Parser) -> Node raise ParseError {
  let mut lhs = self.parse_multiplication()
  while true {
    if self._lexer.match_syntax("+") {
      lhs = Node::new_add(lhs, self.parse_multiplication()).widen().peephole()
    } else if self._lexer.match_syntax("-") {
      lhs = Node::new_sub(lhs, self.parse_multiplication()).widen().peephole()
    } else {
      break
    }
  }
  lhs
}

///|
fn Parser::parse_multiplication(self : Parser) -> Node raise ParseError {
  let mut lhs = self.parse_unary()
  while true {
    if self._lexer.match_syntax("*") {
      lhs = Node::new_mul(lhs, self.parse_unary()).widen().peephole()
    } else if self._lexer.match_syntax("/") {
      lhs = Node::new_div(lhs, self.parse_unary()).widen().peephole()
    } else {
      break
    }
  }
  lhs
}

///|
fn Parser::parse_unary(self : Parser) -> Node raise ParseError {
  if self._lexer.match_syntax("-") {
    return Node::new_minus(self.parse_unary()).widen().peephole()
  }
  if self._lexer.match_syntax("!") {
    return Node::new_not(self.parse_unary()).peephole()
  }
  self.parse_postfix(self.parse_primary())
}

///|
fn Parser::parse_primary(self : Parser) -> Node raise ParseError {
  if self._lexer.is_number() {
    self.parse_integer_literal()
  } else if self._lexer.match_syntax("(") {
    self.require(self.parse_expression(), ")")
  } else if self._lexer.matchx_syntax("true") {
    Node::new_constant(TypeInteger::constant(1L)).peephole()
  } else if self._lexer.matchx_syntax("false") {
    Node::new_constant(TypeInteger::constant(0L)).peephole()
  } else if self._lexer.matchx_syntax("null") {
    Node::new_constant(type_mem_ptr_nullptr).peephole()
  } else if self._lexer.matchx_syntax("new") {
    self.alloc()
  } else {
    match self._lexer.match_id() {
      Some(name) =>
        match self._scope.lookup(name) {
          Some(v) => self._scope.input_exn(v._idx)
          None => raise ParseError::Msg("Undefined name '\{name}'")
        }
      None =>
        raise ParseError::Msg(self.error_syntax("an identifier or expression"))
    }
  }
}

///|
fn Parser::alloc(self : Parser) -> Node raise ParseError {
  let t = match self.parse_type() {
    Some(t) => t
    None => raise ParseError::Msg("Expected a type")
  }
  if self._lexer.match_syntax("[") {
    let len = self.parse_expression().keep()
    match len.ty() {
      Int(_) => ()
      _ => raise ParseError::Msg("Cannot allocate an array with length \{len.ty().str()}")
    }
    self.require_syntax("]")
    let tmp = self.type_ary(t)
    match tmp {
      MemPtr(obj, _) => self.new_array(obj, len)
      _ => panic()
    }
  } else {
    match t {
      MemPtr(obj, _) => {
        let s =
          match inits.val.get(obj._name) {
            Some(s) => s
            None => raise ParseError::Msg("Unknown struct type '\{obj._name}'")
          }
        let fs =
          match s._struct_ts {
            Some(ts) =>
              match ts._fields {
                Some(fs) => fs
                None => panic()
              }
            None => panic()
          }
        let has_constructor = self._lexer.match_syntax("{")
        let mut init = s._inputs
        let mut idx = 0
        if has_constructor {
          idx = self._scope.n_ins()
          self._scope.push()
          for i = 0; i < fs.length(); i = i + 1 {
            let f = fs[i]
            ignore(
              self._scope.define_(
                f._fname,
                f._type,
                f._final,
                s.input_exn(i),
              ),
            )
          }
          self.parse_block()
          self.require_syntax("}")
          init = self._scope._inputs
        }
        for i = idx; i < init.length(); i = i + 1 {
          match init[i] {
            Some(n) =>
              if n.ty() == top {
                raise ParseError::Msg(
                  "'\{obj._name}' is not fully initialized, field '\{fs[i - idx]._fname}' needs to be set in a constructor",
                )
              }
            None => panic()
          }
        }
        let size =
          Node::new_constant(
            TypeInteger::constant(Int64::from_int(obj.offset(fs.length()))),
          ).peephole()
        let ptr = self.new_struct(obj, size, idx, init)
        if has_constructor {
          self._scope.pop()
        }
        ptr
      }
      _ => raise ParseError::Msg("Cannot allocate a \{t.str()}")
    }
  }
}

///|
pub fn Parser::mem_name(alias_id : Int) -> String {
  "$\{alias_id}"
}

///|
fn Parser::mem_alias(self : Parser, alias_id : Int) -> Node {
  self._scope.mem_alias(alias_id)
}

///|
fn Parser::mem_alias_set(self : Parser, alias_id : Int, st : Node) -> Unit {
  self._scope.mem_alias_set(alias_id, st)
}

///|
fn Parser::new_struct(
  self : Parser,
  obj : TypeStruct,
  size : Node,
  idx : Int,
  init : Array[Node?],
) -> Node {
  let fields = match obj._fields {
    Some(fields) => fields
    None => panic()
  }
  let mems : Array[Node] = []
  for f in fields {
    mems.push(self.mem_alias(f._alias))
  }
  let inits : Array[Node] = []
  for i = 0; i < fields.length(); i = i + 1 {
    inits.push(match init[i + idx] {
      Some(n) => n
      None => panic()
    })
  }
  let nnn =
    Node::new_new(MemPtr(obj, false), self._scope.ctrl(), size, mems, inits)
      .peephole()
      .keep()
  for i = 0; i < fields.length(); i = i + 1 {
    let alias_id = fields[i]._alias
    self.mem_alias_set(
      alias_id,
      Node::new_proj(nnn, i + 2, Parser::mem_name(alias_id)).peephole(),
    )
  }
  Node::new_proj(nnn.unkeep(), 1, obj._name).peephole()
}

fn Parser::new_array(self : Parser, ary : TypeStruct, len : Node) -> Node {
  let base =
    Node::new_constant(TypeInteger::constant(Int64::from_int(ary.ary_base()))).peephole()
  let scale =
    Node::new_constant(TypeInteger::constant(Int64::from_int(ary.ary_scale()))).peephole()
  let size =
    Node::new_add(base, Node::new_shl(len, scale).peephole()).peephole()
  let fields = match ary._fields {
    Some(fields) => fields
    None => panic()
  }
  let init : Array[Node?] = [
    Some(len),
    Some(Node::new_constant(fields[1]._type.make_init()).peephole()),
  ]
  self.new_struct(ary, size, 0, init)
}

///|
fn Parser::parse_postfix(self : Parser, expr : Node) -> Node raise ParseError {
  let name =
    if self._lexer.match_syntax(".") {
      self.require_id()
    } else if self._lexer.match_syntax("#") {
      "#"
    } else if self._lexer.match_syntax("[") {
      "[]"
    } else {
      return expr
    }

  let ptr_obj = match expr.ty() {
    MemPtr(obj, _) => obj
    _ => raise ParseError::Msg("Expected reference but got \{expr.ty().str()}")
  }

  if self._scope.ctrl().ty() == xcontrol {
    return if self._lexer.match_opx('=', '=') {
      self.parse_expression()
    } else {
      self.parse_postfix(Node::new_constant(top).peephole())
    }
  }

  let base_obj =
    match types.val.get(ptr_obj._name) {
      Some(MemPtr(obj, _)) => obj
      _ =>
        raise ParseError::Msg(
          "Accessing unknown field '\{name}' from '\{expr.ty().str()}'",
        )
    }
  let idx = base_obj.find(name)
  if idx == -1 {
    raise ParseError::Msg(
      "Accessing unknown field '\{name}' from '\{expr.ty().str()}'",
    )
  }
  ignore(expr.keep())
  let fields = match base_obj._fields {
    Some(fields) => fields
    None =>
      raise ParseError::Msg(
        "Accessing unknown field '\{name}' from '\{expr.ty().str()}'",
      )
  }
  let field = fields[idx]
  let off =
    if name == "[]" {
      let idx = self.require(self.parse_expression(), "]")
      let shl =
        Node::new_shl(
          idx,
          Node::new_constant(
            TypeInteger::constant(Int64::from_int(base_obj.ary_scale())),
          ).peephole(),
        ).peephole()
      Node::new_add(
        Node::new_constant(
          TypeInteger::constant(Int64::from_int(base_obj.ary_base())),
        ).peephole(),
        shl,
      ).peephole()
    } else {
      Node::new_constant(
        TypeInteger::constant(Int64::from_int(base_obj.offset(idx))),
      ).peephole()
    }

  // Disambiguate "obj.fld==x" boolean test from "obj.fld=x" field assignment
  if self._lexer.match_opx('=', '=') {
    let val = self.zs_mask(self.parse_expression(), field._type)
    let st =
      Node::new_store(
        name,
        field._alias,
        field._type,
        self.mem_alias(field._alias),
        expr.unkeep(),
        off,
        val,
        init=false,
      )
    if base_obj.is_ary() {
      ignore(st.set_def(0, Some(self._scope.ctrl())))
    }
    self.mem_alias_set(field._alias, st.peephole())
    return val
  }

  let load =
    Node::new_load(
      name,
      field._alias,
      field._type.glb(),
      self.mem_alias(field._alias),
      expr.unkeep(),
      off,
    )
  self.parse_postfix(load.peephole())
}

///|
fn Parser::zs_mask(_self : Parser, val : Node, t : Type) -> Node {
  match (val.ty(), t) {
    (Int(_), Int(t0)) =>
      if val.ty().isa(t) {
        val
      } else if t0._min == 0L {
        // Unsigned truncation
        Node::new_and(
          val,
          Node::new_constant(TypeInteger::constant(t0._max)).peephole(),
        ).peephole()
      } else {
        // Signed extension
        let shift = t0._max.clz() - 1
        if shift <= 0 {
          val
        } else {
          let shf =
            Node::new_constant(
              TypeInteger::constant(Int64::from_int(shift)),
            ).peephole()
          Node::new_sar(
            Node::new_shl(val, shf.keep()).peephole(),
            shf.unkeep(),
          ).peephole()
        }
      }
    (Flt(_), Flt(_)) =>
      if val.ty().isa(t) {
        val
      } else {
        Node::new_round_f32(val).peephole()
      }
    _ => val
  }
}

///|
fn Parser::parse_integer_literal(self : Parser) -> Node raise ParseError {
  Node::new_constant(self._lexer.parse_number()).peephole()
}

///|
fn Parser::is_keyword(id : String) -> Bool {
  id == "bool" ||
  id == "break" ||
  id == "byte" ||
  id == "continue" ||
  id == "else" ||
  id == "f32" ||
  id == "f64" ||
  id == "false" ||
  id == "flt" ||
  id == "i16" ||
  id == "i32" ||
  id == "i64" ||
  id == "i8" ||
  id == "if" ||
  id == "int" ||
  id == "new" ||
  id == "null" ||
  id == "return" ||
  id == "struct" ||
  id == "true" ||
  id == "u1" ||
  id == "u16" ||
  id == "u32" ||
  id == "u8" ||
  id == "while"
}

///|
fn Parser::require_id(self : Parser) -> String raise ParseError {
  match self._lexer.match_id() {
    Some(id) =>
      if !Parser::is_keyword(id) {
        id
      } else {
        raise ParseError::Msg("Expected an identifier, found '\{id}'")
      }
    None => raise ParseError::Msg("Expected an identifier, found 'null'")
  }
}

///|
fn Parser::require_syntax(
  self : Parser,
  syntax : String,
) -> Unit raise ParseError {
  if !self._lexer.match_syntax(syntax) {
    raise ParseError::Msg(self.error_syntax(syntax))
  }
}

///|
fn Parser::require(
  self : Parser,
  n : Node,
  syntax : String,
) -> Node raise ParseError {
  if self._lexer.match_syntax(syntax) {
    n
  } else {
    raise ParseError::Msg(self.error_syntax(syntax))
  }
}

///|
fn Parser::error_syntax(self : Parser, syntax : String) -> String {
  "Syntax error, expected \{syntax}: \{self._lexer.get_any_next_token()}"
}

///|
priv struct Lexer {
  _input : StringView
  mut _position : Int
}

///|
fn Lexer::new(source : String) -> Lexer {
  { _input: source.to_string_view(), _position: 0 }
}

///|
fn Lexer::is_eof(self : Lexer) -> Bool {
  self._position >= self._input.length()
}

///|
fn Lexer::peek(self : Lexer) -> Char? {
  self._input.get_char(self._position)
}

///|
fn Lexer::skip_white_space(self : Lexer) -> Unit {
  while true {
    match self.peek() {
      Some(ch) if ch <= ' ' => self._position += 1
      Some('/') =>
        match self._input.get_char(self._position + 1) {
          Some('/') => {
            self._position += 2
            while !self.is_eof() && self.peek() != Some('\n') {
              self._position += 1
            }
          }
          _ => break
        }
      _ => break
    }
  }
}

///|
fn Lexer::match_syntax(self : Lexer, syntax : String) -> Bool {
  self.skip_white_space()
  let syntax_view = syntax.to_string_view()
  let rest = try! self._input[self._position:]
  if rest.has_prefix(syntax_view) {
    self._position += syntax_view.length()
    true
  } else {
    false
  }
}

///|
fn Lexer::matchx_syntax(self : Lexer, syntax : String) -> Bool {
  if !self.match_syntax(syntax) {
    return false
  }
  match self.peek() {
    Some(ch) if Lexer::is_id_letter(ch) => {
      self._position -= syntax.length()
      false
    }
    _ => true
  }
}

///|
fn Lexer::get_any_next_token(self : Lexer) -> String {
  if self.is_eof() {
    ""
  } else if self.is_id_start() {
    self.parse_id()
  } else if self.is_number() {
    self.parse_number_string()
  } else if self.is_punctuation() {
    self.parse_punctuation()
  } else {
    match self.peek() {
      Some(ch) => ch.to_string()
      None => ""
    }
  }
}

///|
fn Lexer::is_number(self : Lexer) -> Bool {
  match self.peek() {
    Some(ch) => ch.is_ascii_digit()
    None => false
  }
}

///|
fn Lexer::is_long_or_double(self : Lexer) -> Int {
  let old = self._position
  let mut pos = old
  while true {
    match self._input.get_char(pos) {
      Some(ch) if ch.is_ascii_digit() => pos += 1
      _ => break
    }
  }
  match self._input.get_char(pos) {
    Some('e') | Some('.') => {
      pos += 1
      while true {
        match self._input.get_char(pos) {
          Some(ch) if ch.is_ascii_digit() || ch == 'e' || ch == '.' => pos += 1
          _ => break
        }
      }
      -(pos - old)
    }
    _ => pos - old
  }
}

///|
fn Lexer::parse_number(self : Lexer) -> Type raise ParseError {
  let old = self._position
  let len = self.is_long_or_double()
  let abs_len = if len < 0 { -len } else { len }
  let end = old + abs_len
  let view = try! self._input[old:end]
  self._position = end
  if len > 0 {
    if abs_len > 1 && view.get_char(0) == Some('0') {
      raise ParseError::Msg(
        "Syntax error: integer values cannot start with '0'",
      )
    }
    let val = @strconv.parse_int64(view, base=10) catch {
      _ => raise ParseError::Msg("Syntax error, expected integer literal")
    }
    TypeInteger::constant(val)
  } else {
    let val = @strconv.parse_double(view) catch {
      _ => raise ParseError::Msg("Syntax error, expected float literal")
    }
    TypeFloat::constant(val)
  }
}

///|
fn Lexer::parse_number_string(self : Lexer) -> String {
  let start = self._position
  let len = self.is_long_or_double()
  let abs_len = if len < 0 { -len } else { len }
  let end = start + abs_len
  self._position = end
  let view = try! self._input[start:end]
  view.to_string()
}

///|
fn Lexer::is_id_start(self : Lexer) -> Bool {
  match self.peek() {
    Some(ch) => ch.is_ascii_alphabetic() || ch == '_'
    None => false
  }
}

///|
fn Lexer::peek_char(self : Lexer, ch : Char) -> Bool {
  self.skip_white_space()
  match self.peek() {
    Some(next) => next == ch
    None => false
  }
}

///|
fn Lexer::match_id(self : Lexer) -> String? {
  self.skip_white_space()
  if self.is_id_start() {
    Some(self.parse_id())
  } else {
    None
  }
}

///|
fn Lexer::match_opx(self : Lexer, c0 : Char, c1 : Char) -> Bool {
  self.skip_white_space()
  if self._position + 1 >= self._input.length() {
    return false
  }
  match (
    self._input.get_char(self._position),
    self._input.get_char(self._position + 1),
  ) {
    (Some(c), Some(next)) if c == c0 && next != c1 => {
      self._position += 1
      true
    }
    _ => false
  }
}

///|
fn Lexer::is_id_letter(ch : Char) -> Bool {
  ch.is_ascii_alphabetic() || ch.is_ascii_digit() || ch == '_'
}

///|
fn Lexer::parse_id(self : Lexer) -> String {
  let start = self._position
  while true {
    match self.peek() {
      Some(ch) if Lexer::is_id_letter(ch) => self._position += 1
      _ => break
    }
  }
  let end = self._position
  let view = try! self._input[start:end]
  view.to_string()
}

///|
fn Lexer::is_punctuation(self : Lexer) -> Bool {
  match self.peek() {
    Some(ch) => "=;[]<>(){}+-/*!.?".contains_char(ch)
    None => false
  }
}

///|
fn Lexer::parse_punctuation(self : Lexer) -> String {
  match self.peek() {
    Some(ch) => {
      self._position += 1
      ch.to_string()
    }
    None => ""
  }
}
