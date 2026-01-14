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
let objs : Ref[Map[String, TypeStruct]] = Ref::{ val: Map::new() }

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
  objs.val = Map::new()
  scheduled.val = false
  let lexer = Lexer::new(source)
  let scope = Node::new_scope()
  start.val = Node::new_start([control, arg])
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
  ignore(
    self._scope.define_(
      scope_ctrl,
      control,
      Node::new_cproj(start.val, 0, scope_ctrl).peephole(),
    ),
  )
  ignore(
    self._scope.define_(
      scope_arg0,
      type_integer_bot,
      Node::new_proj(start.val, 1, scope_arg0).peephole(),
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
  } else if self._lexer.matchx_syntax("int") {
    ignore(self.parse_decl(type_integer_bot))
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
fn Parser::parse_field(self : Parser) -> Field raise ParseError {
  match self.parse_type() {
    Some(t) => {
      let fname = self.require_id()
      self.require_syntax(";")
      Field::make(fname, t)
    }
    None =>
      raise ParseError::Msg(
        self.error_syntax(
          "Requires a field type, found '\{self._lexer.get_any_next_token()}'",
        ),
      )
  }
}

///|
fn Parser::parse_struct(self : Parser) -> Unit raise ParseError {
  if self._scope._scopes.length() > 2 {
    raise ParseError::Msg(
      self.error_syntax("struct declarations can only appear in top level scope"),
    )
  }
  let type_name = self.require_id()
  match objs.val.get(type_name) {
    Some(t) =>
      match t._fields {
        None => ()
        Some(_) =>
          raise ParseError::Msg(
            self.error_syntax("struct '\{type_name}' cannot be redefined"),
          )
      }
    None => ()
  }
  let fields : Array[Field] = []
  self.require_syntax("{")
  while !self._lexer.peek_char('}') && !self._lexer.is_eof() {
    let field = self.parse_field()
    let mut dup = false
    for f in fields {
      if f._fname == field._fname {
        dup = true
        break
      }
    }
    if dup {
      raise ParseError::Msg(
        self.error_syntax(
          "Field '\{field._fname}' already defined in struct '\{type_name}'",
        ),
      )
    }
    fields.push(field)
  }
  self.require_syntax("}")
  let ts = TypeStruct::make(type_name, fields)
  objs.val[type_name] = ts
  start.val.add_mem_proj(ts, self._scope)
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
  while cur._scopes.length() > break_scope._scopes.length() {
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
fn Parser::parse_type(self : Parser) -> Type? {
  let old = self._lexer._position
  match self._lexer.match_id() {
    None => None
    Some(tname) =>
      if tname == "bool" || tname == "u1" {
        Some(type_integer_bool)
      } else if tname == "byte" || tname == "u8" {
        Some(type_integer_u8)
      } else if tname == "i8" {
        Some(type_integer_i8)
      } else if tname == "i16" {
        Some(type_integer_i16)
      } else if tname == "i32" {
        Some(type_integer_i32)
      } else if tname == "u16" {
        Some(type_integer_u16)
      } else if tname == "u32" {
        Some(type_integer_u32)
      } else if tname == "int" || tname == "i64" {
        Some(type_integer_bot)
      } else if tname == "f32" {
        Some(type_float_b32)
      } else if tname == "flt" || tname == "f64" {
        Some(type_float_bot)
      } else {
        let nullable = self._lexer.match_syntax("?")
        match objs.val.get(tname) {
          Some(obj) => Some(MemPtr(obj, nullable))
          None => {
            let old2 = self._lexer._position
            match self._lexer.match_id() {
              None => {
                self._lexer._position = old
                None
              }
              Some(_) => {
                let fwd = TypeStruct::make_forward(tname)
                objs.val[tname] = fwd
                self._lexer._position = old2
                Some(MemPtr(fwd, nullable))
              }
            }
          }
        }
      }
  }
}

///|
fn Parser::parse_expression_statement(self : Parser) -> Node raise ParseError {
  let old = self._lexer._position
  let t = self.parse_type()
  let name = self.require_id()
  let mut expr =
    if self._lexer.match_syntax(";") {
      match t {
        Some(t) => Node::new_constant(t.make_init()).peephole()
        None => raise ParseError::Msg(self.error_syntax("expression"))
      }
    } else if self._lexer.match_syntax("=") {
      self.require(self.parse_expression(), ";")
    } else {
      self._lexer._position = old
      return self.require(self.parse_expression(), ";")
    }

  let declared =
    match t {
      Some(t) => t
      None =>
        match self._scope.lookup(name) {
          None => raise ParseError::Msg("Undefined name '\{name}'")
          Some(_) =>
            match self._scope.lookup_declared_type(name) {
              Some(t) => t
              None => panic()
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
          match objs.val.get(obj._name) {
            Some(obj0) => expr_ty = MemPtr(obj0, nil)
            None => ()
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
  match t {
    Some(_) =>
      if self._scope.define_(name, declared, expr) is None {
        raise ParseError::Msg("Redefining name '\{name}'")
      }
    None => ()
  }
  match self._scope.update(name, expr) {
    Some(n) => n
    None => panic()
  }
}

///|
fn Parser::parse_decl(self : Parser, t : Type) -> Node raise ParseError {
  let name = self.require_id()
  let mut expr =
    if self._lexer.match_syntax(";") {
      Node::new_constant(t.make_init()).peephole()
    } else {
      self.require_syntax("=")
      self.require(self.parse_expression(), ";")
    }
  if _is_int_type(expr.ty()) && _is_float_type(t) {
    expr = Node::new_to_float(expr).peephole()
  }
  expr = self.zs_mask(expr, t)
  if !expr.ty().isa(t) {
    raise ParseError::Msg(
      "Type \{expr.ty().str()} is not of declared type \{t.str()}",
    )
  }
  if self._scope.define_(name, t, expr) is None {
    raise ParseError::Msg("Redefining name '\{name}'")
  }
  expr
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
    let struct_name = self.require_id()
    match objs.val.get(struct_name) {
      Some(obj) =>
        match obj._fields {
          Some(_) => self.new_struct(obj)
          None => raise ParseError::Msg("Unknown struct type '\{struct_name}'")
        }
      None => raise ParseError::Msg("Unknown struct type '\{struct_name}'")
    }
  } else {
    match self._lexer.match_id() {
      Some(name) =>
        match self._scope.lookup(name) {
          Some(n) => n
          None => raise ParseError::Msg("Undefined name '\{name}'")
        }
      None =>
        raise ParseError::Msg(self.error_syntax("an identifier or expression"))
    }
  }
}

///|
pub fn Parser::mem_name(alias_id : Int) -> String {
  "$\{alias_id}"
}

///|
fn Parser::mem_alias(self : Parser, alias_id : Int) -> Node {
  match self._scope.lookup(Parser::mem_name(alias_id)) {
    Some(n) => n
    None => panic()
  }
}

///|
fn Parser::mem_alias_set(self : Parser, alias_id : Int, st : Node) -> Unit {
  if self._scope.update(Parser::mem_name(alias_id), st) is None {
    panic()
  }
}

///|
fn Parser::new_struct(self : Parser, obj : TypeStruct) -> Node {
  let n = Node::new_new(MemPtr(obj, false), self._scope.ctrl()).peephole().keep()
  let ctrl = self._scope.ctrl()
  let mut alias_id = match start.val._alias_starts.get(obj._name) {
    Some(aid) => aid
    None => panic()
  }
  match obj._fields {
    None => panic()
    Some(fields) =>
      for field in fields {
        let init_value = Node::new_constant(field._type.make_init()).peephole()
        let st = Node::new_store(
          field._fname,
          alias_id,
          field._type,
          ctrl,
          self.mem_alias(alias_id),
          n,
          init_value,
          init=true,
        ).peephole()
        self.mem_alias_set(alias_id, st)
        alias_id = alias_id + 1
      }
  }
  n.unkeep()
}

///|
fn Parser::parse_postfix(self : Parser, expr : Node) -> Node raise ParseError {
  if !self._lexer.match_syntax(".") {
    return expr
  }

  let ptr_obj = match expr.ty() {
    MemPtr(obj, _) => obj
    _ =>
      raise ParseError::Msg(
        "Expected struct reference but got \{expr.ty().str()}",
      )
  }

  let name = self.require_id()
  let base_obj = match objs.val.get(ptr_obj._name) {
    Some(obj) => obj
    None => ptr_obj
  }
  let idx = base_obj.find(name)
  if idx == -1 {
    raise ParseError::Msg(
      "Accessing unknown field '\{name}' from '\{expr.ty().str()}'",
    )
  }
  let base = match start.val._alias_starts.get(ptr_obj._name) {
    Some(aid) => aid
    None => panic()
  }
  let alias_id = base + idx

  let fields = match base_obj._fields {
    Some(fields) => fields
    None => panic()
  }

  if self._lexer.match_syntax("=") {
    // Disambiguate "obj.fld==x" boolean test from "obj.fld=x" field assignment
    if self._lexer.peek_char('=') {
      self._lexer._position -= 1
    } else {
      let glb = fields[idx]._type
      let val = self.zs_mask(self.parse_expression(), glb)
      self.mem_alias_set(
        alias_id,
        Node::new_store(
          name,
          alias_id,
          glb,
          self._scope.ctrl(),
          self.mem_alias(alias_id),
          expr,
          val,
          init=false,
        ).peephole(),
      )
      return expr
    }
  }

  let declared_type = fields[idx]._type
  self.parse_postfix(
    Node::new_load(
      name,
      alias_id,
      declared_type.glb(),
      self.mem_alias(alias_id),
      expr,
    ).peephole(),
  )
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
