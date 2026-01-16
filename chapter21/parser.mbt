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

///|
let next_alias : Ref[Int] = Ref::{ val: 2 }

///|
let inits : Ref[Map[String, Node]] = Ref::{ val: Map::new() }

///|
pub let scheduled : Ref[Bool] = Ref::{ val: false }

///|
pub let local_scheduled : Ref[Bool] = Ref::{ val: false }

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
  // `var`/`val` are type-position markers for inference & mutability
  types.val["val"] = top
  types.val["var"] = bottom
  scheduled.val = false
  local_scheduled.val = false
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
  ignore(mem.add_def(Some(Node::new_proj(start.val, 1, scope_mem0).peephole())))
  ignore(
    self._scope.define_(
      scope_ctrl,
      control,
      false,
      Node::new_cproj(start.val, 0, scope_ctrl).peephole(),
    ),
  )
  ignore(self._scope.define_(scope_mem0, type_mem_top, false, mem.peephole()))
  ignore(
    self._scope.define_(
      scope_arg0,
      type_integer_bot,
      false,
      Node::new_proj(start.val, 2, scope_arg0).peephole(),
    ),
  )
  self.parse_block(false)
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
fn Parser::parse_block(self : Parser, in_con : Bool) -> Unit raise ParseError {
  self._scope.push(in_con~)
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
    self.parse_block(false)
    self.require_syntax("}")
  } else if self._lexer.matchx_syntax("if") {
    ignore(self.parse_if())
  } else if self._lexer.matchx_syntax("while") {
    ignore(self.parse_while())
  } else if self._lexer.matchx_syntax("for") {
    ignore(self.parse_for())
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
    ignore(self.parse_declaration_statement())
  }
}

///|

///|
fn Parser::parse_struct(self : Parser) -> Unit raise ParseError {
  if self._scope._lex_size.length() > 2 {
    raise ParseError::Msg(
      self.error_syntax(
        "struct declarations can only appear in top level scope",
      ),
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
  self._scope.push(in_con=true)
  self.require_syntax("{")
  while !self._lexer.peek_char('}') && !self._lexer.is_eof() {
    self.parse_statement()
  }
  let lexlen = match self._scope._lex_size.last() {
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
  types.val[type_name] = MemPtr(ts, 2)
  inits.val[type_name] = s.peephole().keep()
  self.require_syntax("}")
  self.require_syntax(";")
  self._scope.pop()
}

///|
fn Parser::parse_if(self : Parser) -> Node raise ParseError {
  // Parse predicate
  self.require_syntax("(")
  let pred = self.require(self.parse_asgn(), ")")
  self.parse_trinary(pred, true, "else")
}

///|
fn Parser::parse_trinary(
  self : Parser,
  pred : Node,
  stmt : Bool,
  fside : String,
) -> Node raise ParseError {
  ignore(pred.keep())
  let if_node = Node::new_if(Some(self._scope.ctrl()), pred).peephole()
  let if_t = Node::new_cproj(if_node.keep(), 0, "True").peephole().keep()
  let if_f = Node::new_cproj(if_node.unkeep(), 1, "False").peephole().keep()
  let ndefs = self._scope.n_ins()
  let mut f_scope = self._scope.dup()

  // Parse true side
  ignore(self._scope.set_def(0, Some(if_t.unkeep())))
  self._scope.add_guards(if_t, Some(pred), false)
  let mut lhs : Node? = None
  if stmt {
    self.parse_statement()
  } else {
    lhs = Some(self.parse_asgn().keep())
  }
  self._scope.remove_guards(if_t)
  let t_scope = self._scope

  // Parse false side
  self._scope = f_scope
  ignore(self._scope.set_def(0, Some(if_f.unkeep())))
  self._scope.add_guards(if_f, Some(pred), true)
  let do_rhs = self._lexer.match_syntax(fside)
  let mut rhs : Node? = None
  if do_rhs {
    if stmt {
      self.parse_statement()
    } else {
      rhs = Some(self.parse_asgn())
    }
  } else if !stmt {
    let lhs0 = match lhs {
      Some(n) => n
      None => panic()
    }
    rhs = Some(Node::new_constant(lhs0.ty().make_zero()).peephole())
  }
  self._scope.remove_guards(if_f)
  if do_rhs {
    f_scope = self._scope
  }
  ignore(pred.unkeep())
  if t_scope.n_ins() != ndefs || f_scope.n_ins() != ndefs {
    raise ParseError::Msg("Cannot define a new name on one arm of an if")
  }

  // Widen ints to floats in a trinary
  if !stmt {
    let rhs0 = match rhs {
      Some(n) => n
      None => panic()
    }
    let lhs0 = match lhs {
      Some(n) => n
      None => panic()
    }
    let rhs1 = self.widen_int(rhs0, lhs0.ty()).keep()
    let lhs1 = self.widen_int(lhs0.unkeep(), rhs1.ty()).keep()
    rhs = Some(rhs1.unkeep())
    lhs = Some(lhs1)
  }

  // Merge results
  self._scope = t_scope
  let r = self._scope.merge_scopes(f_scope)
  ignore(self._scope.set_def(0, Some(r)))
  ignore(r.peephole())
  if stmt {
    r
  } else {
    let rhs0 = match rhs {
      Some(n) => n
      None => panic()
    }
    let lhs0 = match lhs {
      Some(n) => n
      None => panic()
    }
    self.peep(
      Node::new_phi("", lhs0.ty().meet(rhs0.ty()), [
        Some(r),
        Some(lhs0.unkeep()),
        Some(rhs0),
      ]),
    )
  }
}

///|
fn Parser::parse_while(self : Parser) -> Node raise ParseError {
  self.require_syntax("(")
  self.parse_looping(false)
}

///|
fn Parser::parse_for(self : Parser) -> Node raise ParseError {
  self.require_syntax("(")
  // Scope for the index variables
  self._scope.push()
  // Can be empty init "for(;test;next) body"
  if !self._lexer.match_syntax(";") {
    ignore(self.parse_declaration_statement())
  }
  let rez = self.parse_looping(true)
  // Exit index variable scope
  self._scope.pop()
  rez
}

///|
fn Parser::parse_looping(self : Parser, do_for : Bool) -> Node raise ParseError {
  let saved_continue_scope = self._continue_scope
  let saved_break_scope = self._break_scope

  // Note we set back edge to null here
  ignore(
    self._scope.set_def(
      0,
      Some(Node::new_loop(self._scope.input(0)).peephole()),
    ),
  )

  // Save the current scope as the loop head
  let head = self._scope.keep()
  // Clone the head Scope to create a new Scope for the body.
  self._scope = self._scope.dup(is_loop=true)

  // Parse predicate
  let pred = if self._lexer.peek_char(';') {
    Node::new_constant(TypeInteger::constant(1L)).peephole()
  } else {
    self.parse_asgn()
  }
  self.require_syntax(if do_for { ";" } else { ")" })

  // IfNode takes current control and predicate
  let if_node = Node::new_if(Some(self._scope.ctrl()), pred.keep()).peephole()
  // Setup projection nodes
  let if_t = Node::new_cproj(if_node.keep(), 0, "True").peephole().keep()
  let if_f = Node::new_cproj(if_node.unkeep(), 1, "False").peephole()

  // for( ;;next ) body
  let mut next_pos = -1
  let mut next_end = -1
  if do_for {
    // Skip the next expression and parse it later
    next_pos = self._lexer._position
    self.skip_asgn()
    next_end = self._lexer._position
    self.require_syntax(")")
  }

  // Clone the body Scope to create the break/exit Scope which accounts for any
  // side effects in the predicate.
  ignore(self._scope.set_def(0, Some(if_f)))
  let break_scope = self._scope.dup()
  break_scope.add_guards(if_f, Some(pred), true)
  self._break_scope = Some(break_scope)

  // No continues yet
  self._continue_scope = None

  // Parse the true side, which corresponds to loop body
  ignore(self._scope.set_def(0, Some(if_t.unkeep())))
  self._scope.add_guards(if_t, Some(pred.unkeep()), false)
  self.parse_statement()
  self._scope.remove_guards(if_t)

  // Merge the loop bottom into other continue statements
  if self._continue_scope is Some(_) {
    let cont = self.jump_to(self._continue_scope)
    self._continue_scope = Some(cont)
    self._scope.kill()
    self._scope = cont
  }

  // Now append the next code onto the body code
  if do_for {
    let old = self._lexer._position
    self._lexer._position = next_pos
    if !self._lexer.peek_char(')') {
      ignore(self.parse_asgn())
    }
    if self._lexer._position != next_end {
      raise ParseError::Msg(
        self.error_syntax("Unexpected code after expression"),
      )
    }
    self._lexer._position = old
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
  let break_scope = match self._break_scope {
    Some(s) => s
    None => panic()
  }
  break_scope.remove_guards(break_scope.ctrl())
  let scope = self.require(self.jump_to(self._break_scope), ";")
  self._break_scope = Some(scope)
  scope.add_guards(scope.ctrl(), None, false)
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
  let expr = self.require(self.parse_asgn(), ";")
  let ret = self._stop.add_return(
    Node::new_return(self._scope.input(0), expr, self._scope).peephole(),
  )
  ignore(self._scope.set_def(0, Some(xctrl.val)))
  ret
}

// Look for an unbalanced `)`, skipping balanced

///|
fn Parser::skip_asgn(self : Parser) -> Unit raise ParseError {
  let mut paren = 0
  while true {
    match self._lexer.next_x_char() {
      None => raise ParseError::Msg("unexpected EOF while scanning for ')'")
      Some(')') => {
        paren = paren - 1
        if paren < 0 {
          // Leave the ')' behind
          self._lexer._position = self._lexer._position - 1
          return
        }
      }
      Some('(') => paren = paren + 1
      Some(_) => ()
    }
  }
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
      if t0 is None && Parser::is_keyword(tname) {
        self._lexer._position = old1
        return None
      }
      // Match refs/simple: for forward refs, remember the base (non-? / non-array)
      // type under the name, and apply "[]"/"?" on a separate working type.
      let base_t = match t0 {
        Some(t) => t
        None => MemPtr(TypeStruct::make_forward(tname), 2)
      }
      let mut t1 = base_t
      while true {
        if self._lexer.match_syntax("?") {
          match t1 {
            MemPtr(obj, nil) =>
              if nil == 0 || nil == 3 {
                raise ParseError::Msg("Type \{t1.str()} already allows null")
              } else {
                t1 = MemPtr(obj, 3)
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
          let id = self._lexer.match_id()
          self._lexer._position = old2
          match id {
            None => {
              self._lexer._position = old1
              None
            }
            Some(id) =>
              if self._scope.lookup(id) is Some(_) {
                self._lexer._position = old1
                None
              } else {
                types.val[tname] = base_t
                Some(t1)
              }
          }
        }
      }
    }
  }
}

///|
fn Parser::type_ary(self : Parser, t : Type) -> Type raise ParseError {
  match t {
    MemPtr(_, nil) if nil == 1 || nil == 2 =>
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
      let tary = MemPtr(ts, 2)
      types.val[tname] = tary
      tary
    }
  }
}

///|
fn Parser::peep(self : Parser, n : Node) -> Node {
  // Peephole, then improve with lexically scoped guards.
  self._scope.upcast_guard(n.peephole())
}

///|
/// Parse: [name '='] exprAsgn
fn Parser::parse_asgn(self : Parser) -> Node raise ParseError {
  let old = self._lexer._position
  let name0 = self._lexer.match_id()
  let name = match name0 {
    Some(id) if !Parser::is_keyword(id) && self._lexer.match_opx('=', '=') => id
    _ => {
      self._lexer._position = old
      return self.parse_expression()
    }
  }

  // Parse assignment expression
  let expr = self.parse_asgn()

  // Final variable to update
  let def = match self._scope.lookup(name) {
    Some(v) => v
    None => raise ParseError::Msg("Undefined name '\{name}'")
  }

  // TOP fields are for late-initialized fields; these have never been written
  // to, and this must be the final write.  Other writes outside the
  // constructor need to check the final bit.
  let lexlen = match self._scope._lex_size.last() {
    Some(n) => n
    None => panic()
  }
  if self._scope.input_exn(def._idx).ty() != top &&
    def._final &&
    !(self._scope.in_con() && def._idx >= lexlen) {
    raise ParseError::Msg("Cannot reassign final '\{name}'")
  }

  // Lift expression based on the declared type, but return the un-lifted expr
  // (matches refs/simple).
  let lift = self.lift_expr(expr.keep(), def._type, def._final)
  self._scope.update(name, lift)
  expr.unkeep()
}

// Make finals deep; widen ints to floats; narrow wide int types.
// Early error if types do not match variable.

///|
fn Parser::lift_expr(
  self : Parser,
  expr0 : Node,
  t0 : Type,
  xfinal : Bool,
) -> Node raise ParseError {
  let mut expr = expr0
  let mut t = t0

  // Update declared forward-ref type to actual, if possible.
  match t {
    MemPtr(obj, nil) =>
      match obj._fields {
        None =>
          match types.val.get(obj._name) {
            Some(t1) => t = t.meet(t1)
            None => ()
          }
        Some(_) => ()
      }
    _ => ()
  }

  // Final is deep on ptrs
  match t {
    MemPtr(_, _) if xfinal => {
      t = t.make_ro()
      expr = self.peep(Node::new_read_only(expr))
    }
    _ => ()
  }

  // Auto-widen int to float
  expr = self.widen_int(expr, t)
  // Auto-narrow wide ints to narrow ints
  expr = self.zs_mask(expr, t)
  if !expr.ty().isa(t) {
    raise ParseError::Msg(
      "Type \{expr.ty().str()} is not of declared type \{t.str()}",
    )
  }
  expr
}

///|
fn Parser::widen_int(self : Parser, expr : Node, t : Type) -> Node {
  if (_is_int_type(expr.ty()) || expr.ty() == type_nil) && _is_float_type(t) {
    self.peep(Node::new_to_float(expr))
  } else {
    expr
  }
}

///|
fn Parser::parse_declaration_statement(self : Parser) -> Node raise ParseError {
  match self.parse_type() {
    None => self.require(self.parse_asgn(), ";")
    Some(t) => {
      let mut n = self.parse_declaration(t)
      while self._lexer.match_syntax(",") {
        n = self.parse_declaration(t)
      }
      self.require(n, ";")
    }
  }
}

///|
/// Parse final: [!]var['=' asgn]
fn Parser::parse_declaration(self : Parser, t0 : Type) -> Node raise ParseError {
  let mut t = t0
  // Has var/val instead of a user-declared type
  let infer_type = t == top || t == bottom
  let has_bang = self._lexer.match_syntax("!")
  let name = self.require_id()

  // Optional initializing expression follows
  let mut xfinal = false
  let expr = if self._lexer.match_syntax("=") {
    let expr = self.parse_asgn()
    // Match refs/simple:
    // - TOP means val and val is always final
    // - BOTTOM is var and var is always not-final
    // - pointers are final by default (unless explicitly ! or initialized with null)
    xfinal = t == top ||
      (
        t != bottom &&
        !has_bang &&
        expr.ty() != type_nil &&
        (match t {
          Ptr(_) => true
          MemPtr(_, _) => true
          FunPtr(_) => true
          _ => false
        })
      )
    // var/val: infer type from expression
    if infer_type {
      if expr.ty() == type_nil {
        raise ParseError::Msg("a not-null/non-zero expression")
      }
      t = expr.ty()
      if !xfinal {
        t = t.glb()
      }
    }
    // Debug-only: if we have a constant funptr, attach its name.
    match (t, expr.ty()) {
      (FunPtr(_), FunPtr(fp)) if fp.is_constant() =>
        expr._type = Some(FunPtr(fp.set_name(Some(name))))
      _ => ()
    }
    expr
  } else {
    // Need an expression to infer the type.
    // Also, if not-null then need an initializing expression.
    // Allowed in a constructor, because type/init will happen in the constructor.
    let needs_init = infer_type ||
      (match t {
        Ptr(nil) => nil == 1 || nil == 2
        MemPtr(_, nil) => nil == 1 || nil == 2
        FunPtr(fp) => fp._nil == 1 || fp._nil == 2
        _ => false
      })
    if needs_init && !self._scope.in_con() {
      raise ParseError::Msg(self.error_syntax("=expression"))
    }
    let init_ty = match t {
      Ptr(nil) => if nil == 0 || nil == 3 { type_nil } else { top }
      MemPtr(_, nil) => if nil == 0 || nil == 3 { type_nil } else { top }
      FunPtr(fp) => if fp._nil == 0 || fp._nil == 3 { type_nil } else { top }
      Int(_) => type_integer_zero
      Flt(_) => type_float_zero
      _ => bottom
    }
    Node::new_constant(init_ty).peephole()
  }

  // Lift expression, based on type
  let mut lift = self.lift_expr(expr, t, xfinal)
  if xfinal && t is MemPtr(_, _) {
    t = t.make_ro()
  }
  // Lift type to the declaration (matches refs/simple; typically no-op after lift_expr).
  if !lift.ty().isa(t) {
    lift = self.peep(Node::new_cast(t, None, lift))
  }
  if !self._scope.define_(name, t, xfinal, lift) {
    raise ParseError::Msg("Redefining name '\{name}'")
  }
  lift
}

///|
fn Parser::parse_expression(self : Parser) -> Node raise ParseError {
  let expr = self.parse_bitwise()
  if self._lexer.match_syntax("?") {
    self.parse_trinary(expr, false, ":")
  } else {
    expr
  }
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
      lhs = Node::new_not(
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
  // Pre-dec/pre-inc
  let old = self._lexer._position
  let mut delta = 0L
  if self._lexer.match_syntax("--") {
    delta = -1L
  } else if self._lexer.match_syntax("++") {
    delta = 1L
  }
  if delta != 0L {
    match self._lexer.match_id() {
      Some(name) =>
        match self._scope.lookup(name) {
          Some(v) => {
            if v._final {
              raise ParseError::Msg("Cannot reassign final '\{v._name}'")
            }
            let expr = self.zs_mask(
              self.peep(
                Node::new_add(
                  self._scope.input_exn(v._idx),
                  Node::new_constant(TypeInteger::constant(delta)).peephole(),
                ),
              ),
              v._type,
            )
            self._scope.update(v._name, expr)
            return expr
          }
          None => ()
        }
      None => ()
    }
    // Reset, try again
    self._lexer._position = old
  }
  if self._lexer.match_syntax("-") {
    return self.peep(Node::new_minus(self.parse_unary()).widen())
  }
  if self._lexer.match_syntax("!") {
    return self.peep(Node::new_not(self.parse_unary()))
  }
  self.parse_postfix(self.parse_primary())
}

///|
fn Parser::parse_primary(self : Parser) -> Node raise ParseError {
  if self._lexer.is_number() {
    self.parse_integer_literal()
  } else if self._lexer.match_syntax("(") {
    self.require(self.parse_asgn(), ")")
  } else if self._lexer.matchx_syntax("true") {
    Node::new_constant(TypeInteger::constant(1L)).peephole()
  } else if self._lexer.matchx_syntax("false") {
    Node::new_constant(TypeInteger::constant(0L)).peephole()
  } else if self._lexer.matchx_syntax("null") {
    Node::new_constant(type_nil).peephole()
  } else if self._lexer.matchx_syntax("new") {
    self.alloc()
  } else {
    let v = self.require_lookup_id("an identifier or expression")
    let rvalue = self._scope.input_exn(v._idx)
    if rvalue.ty() == bottom {
      raise ParseError::Msg("Cannot read uninitialized field '\{v._name}'")
    }

    // Assign-update: x += e0;  x++;
    let ch = self._lexer.match_oper_assign()
    if ch == '\u{0000}' {
      return rvalue
    }
    if v._final {
      raise ParseError::Msg("Cannot reassign final '\{v._name}'")
    }
    let mut op = match ch {
      '+' => Node::new_raw(Add, [None, Some(rvalue), None])
      '-' => Node::new_raw(Sub, [None, Some(rvalue), None])
      '*' => Node::new_raw(Mul, [None, Some(rvalue), None])
      '/' => Node::new_raw(Div, [None, Some(rvalue), None])
      // As a convenience, "++" is a char 1 and "--" is char -1 (65535)
      '\u{0001}' =>
        Node::new_add(
          rvalue,
          Node::new_constant(TypeInteger::constant(1L)).peephole(),
        )
      '\u{FFFF}' =>
        Node::new_add(
          rvalue,
          Node::new_constant(TypeInteger::constant(-1L)).peephole(),
        )
      _ => panic()
    }

    // Return pre-value (x+=e0) or post-value (x++)
    let pre = op.input(2) is None
    if pre {
      let ok = op.keep()
      ignore(ok.set_def(2, Some(self.parse_asgn())))
      ignore(ok.unkeep())
    } else {
      ignore(rvalue.keep())
    }
    op = self.zs_mask(self.peep(op), v._type)
    self._scope.update(v._name, op)
    if pre {
      op
    } else {
      rvalue.unkeep()
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
    let len = self.parse_asgn()
    if !_is_int_type(len.ty()) {
      raise ParseError::Msg(
        "Cannot allocate an array with length \{len.ty().str()}",
      )
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
        let s = match inits.val.get(obj._name) {
          Some(s) => s
          None => raise ParseError::Msg("Unknown struct type '\{obj._name}'")
        }
        let fs = match s._struct_ts {
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
                if s.input_exn(i).ty() == top {
                  Node::new_constant(bottom).peephole()
                } else {
                  s.input_exn(i)
                },
              ),
            )
          }
          self.parse_block(true)
          self.require_syntax("}")
          init = self._scope._inputs
        }
        for i = idx; i < init.length(); i = i + 1 {
          match init[i] {
            Some(n) =>
              if n.ty() == bottom || n.ty() == top {
                raise ParseError::Msg(
                  "'\{obj._name}' is not fully initialized, field '\{fs[i - idx]._fname}' needs to be set in a constructor",
                )
              }
            None => panic()
          }
        }
        let size = Node::new_constant(
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
    inits.push(
      match init[i + idx] {
        Some(n) => n
        None => panic()
      },
    )
  }
  let nnn = Node::new_new(MemPtr(obj, 2), self._scope.ctrl(), size, mems, inits)
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

///|
fn Parser::new_array(self : Parser, ary : TypeStruct, len : Node) -> Node {
  let base = Node::new_constant(
    TypeInteger::constant(Int64::from_int(ary.ary_base())),
  ).peephole()
  let scale = Node::new_constant(
    TypeInteger::constant(Int64::from_int(ary.ary_scale())),
  ).peephole()
  let size = Node::new_add(base, Node::new_shl(len, scale).peephole()).peephole()
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
  let name = if self._lexer.match_syntax(".") {
    self.require_id()
  } else if self._lexer.match_syntax("#") {
    "#"
  } else if self._lexer.match_syntax("[") {
    "[]"
  } else {
    return expr
  }
  if expr.ty() == type_nil {
    raise ParseError::Msg("Accessing unknown field '\{name}' from 'null'")
  }
  let ptr_obj = match expr.ty() {
    MemPtr(obj, _) => obj
    _ => raise ParseError::Msg("Expected reference but got \{expr.ty().str()}")
  }
  let base_obj = match types.val.get(ptr_obj._name) {
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
  let fields = match base_obj._fields {
    Some(fields) => fields
    None =>
      raise ParseError::Msg(
        "Accessing unknown field '\{name}' from '\{expr.ty().str()}'",
      )
  }
  let field = fields[idx]
  let mut tf = field._type
  // Update declared forward ref to the actual
  match tf {
    MemPtr(obj, nil) =>
      match obj._fields {
        None =>
          match types.val.get(obj._name) {
            Some(t1) => tf = tf.meet(t1)
            None => ()
          }
        Some(_) => ()
      }
    _ => ()
  }
  let off = (if name == "[]" {
    // Array index math
    let idx = self.require(self.parse_asgn(), "]")
    let shl = self.peep(
      Node::new_shl(
        idx,
        Node::new_constant(
          TypeInteger::constant(Int64::from_int(base_obj.ary_scale())),
        ).peephole(),
      ),
    )
    self.peep(
      Node::new_add(
        Node::new_constant(
          TypeInteger::constant(Int64::from_int(base_obj.ary_base())),
        ).peephole(),
        shl,
      ),
    )
  } else {
    // Struct field offsets are hardwired
    Node::new_constant(
      TypeInteger::constant(Int64::from_int(base_obj.offset(idx))),
    ).peephole()
  }).keep()

  // Disambiguate "obj.fld==x" boolean test from "obj.fld=x" field assignment
  if self._lexer.match_opx('=', '=') {
    let val = self.parse_asgn().keep()
    let lift = self.lift_expr(val, tf, field._final)
    let st = Node::new_store(
      name,
      field._alias,
      tf,
      self.mem_alias(field._alias),
      expr,
      off.unkeep(),
      lift,
      init=false,
    )
    if base_obj.is_ary() {
      ignore(st.set_def(0, Some(self._scope.ctrl())))
    }
    self.mem_alias_set(field._alias, st.peephole())
    return val.unkeep()
  }
  let mut load = Node::new_load(
    name,
    field._alias,
    tf.glb(),
    self.mem_alias(field._alias),
    expr.keep(),
    off,
  )
  if base_obj.is_ary() {
    ignore(load.set_def(0, Some(self._scope.ctrl())))
  }
  load = self.peep(load)

  // ary[idx]++ or ptr.fld++
  if self._lexer.matchx_syntax("++") {
    let inc = self.peep(
      Node::new_add(
        load,
        Node::new_constant(TypeInteger::constant(1L)).peephole(),
      ),
    )
    let val = self.zs_mask(inc, tf)
    let st = Node::new_store(
      name,
      field._alias,
      tf,
      self.mem_alias(field._alias),
      expr.unkeep(),
      off,
      val,
      init=false,
    )
    if base_obj.is_ary() {
      ignore(st.set_def(0, Some(self._scope.ctrl())))
    }
    self.mem_alias_set(field._alias, self.peep(st))
  } else if self._lexer.matchx_syntax("--") {
    let inc = self.peep(
      Node::new_add(
        load,
        Node::new_constant(TypeInteger::constant(-1L)).peephole(),
      ),
    )
    let val = self.zs_mask(inc, tf)
    let st = Node::new_store(
      name,
      field._alias,
      tf,
      self.mem_alias(field._alias),
      expr.unkeep(),
      off,
      val,
      init=false,
    )
    if base_obj.is_ary() {
      ignore(st.set_def(0, Some(self._scope.ctrl())))
    }
    self.mem_alias_set(field._alias, self.peep(st))
  } else {
    ignore(expr.unkeep())
  }
  ignore(off.unkeep())
  self.parse_postfix(load)
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
          let shf = Node::new_constant(
            TypeInteger::constant(Int64::from_int(shift)),
          ).peephole()
          Node::new_sar(Node::new_shl(val, shf.keep()).peephole(), shf.unkeep()).peephole()
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
  id == "for" ||
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
  id == "val" ||
  id == "var" ||
  id == "while"
}

///|
fn Parser::require_lookup_id(
  self : Parser,
  msg : String,
) -> Var raise ParseError {
  let old = self._lexer._position
  match self._lexer.match_id() {
    Some(id) if !Parser::is_keyword(id) =>
      match self._scope.lookup(id) {
        Some(v) => v
        None => raise ParseError::Msg("Undefined name '\{id}'")
      }
    _ => {
      self._lexer._position = old
      raise ParseError::Msg(self.error_syntax(msg))
    }
  }
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

// Next non-white-space character, or EOF.

///|
fn Lexer::next_x_char(self : Lexer) -> Char? {
  self.skip_white_space()
  match self.peek() {
    Some(ch) => {
      self._position += 1
      Some(ch)
    }
    None => None
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
  match
    (
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

// Next oper= character, or 0.
// As a convenience, mark "++" as a char 1 and "--" as char -1 (65535).
// Disallow e.g. "arg--1" which should parse as "arg - -1".

///|
fn Lexer::match_oper_assign(self : Lexer) -> Char {
  self.skip_white_space()
  if self._position + 2 >= self._input.length() {
    return '\u{0000}'
  }
  let ch0 = match self._input.get_char(self._position) {
    Some(ch) => ch
    None => return '\u{0000}'
  }
  if !"+-/*&|^".contains_char(ch0) {
    return '\u{0000}'
  }
  let ch1 = match self._input.get_char(self._position + 1) {
    Some(ch) => ch
    None => return '\u{0000}'
  }
  if ch1 == '=' {
    self._position += 2
    return ch0
  }
  match self._input.get_char(self._position + 2) {
    Some(ch2) if Lexer::is_id_letter(ch2) => return '\u{0000}'
    _ => ()
  }
  if ch0 == '+' && ch1 == '+' {
    self._position += 2
    return '\u{0001}'
  }
  if ch0 == '-' && ch1 == '-' {
    self._position += 2
    return '\u{FFFF}'
  }
  '\u{0000}'
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
