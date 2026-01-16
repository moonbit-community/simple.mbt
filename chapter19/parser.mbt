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
  mut _fun : Node?
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
  next_alias.val = 2
  inits.val = Map::new()
  fun_table_reset()
  main_sig.val = make_fun([arg], bottom)
  let lexer = Lexer::new(source)
  let scope = Node::new_scope()
  start.val = Node::new_start([control, type_mem_top, arg])
  stop.val = Node::new_stop()
  let stop_node = stop.val
  zero.val = Node::new_constant(type_integer_zero).peephole().keep()
  xctrl.val = Node::new_xctrl().peephole().keep()
  {
    _lexer: lexer,
    _scope: scope,
    _stop: stop_node,
    _continue_scope: None,
    _break_scope: None,
    _fun: None,
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

  // Placeholder top scope bindings; the whole program is parsed as a function body.
  ignore(self._scope.define_(scope_ctrl, control, false, Node::new_cproj(start.val, 0, scope_ctrl).peephole()))
  let mem = Node::new_mem()
  ignore(mem.add_def(None))
  ignore(mem.add_def(Some(Node::new_proj(start.val, 1, scope_mem0).peephole())))
  ignore(self._scope.define_(scope_mem0, type_mem_bot, false, mem.peephole()))
  ignore(
    self._scope.define_(
      scope_arg0,
      type_integer_bot,
      false,
      Node::new_proj(start.val, 2, scope_arg0).peephole(),
    ),
  )

    // Start parsing with dead control (matches refs/simple).
  ignore(self._scope.set_def(0, Some(xctrl.val)))

// Parse whole program, as-if function header "{ int arg -> body }".
  let ret = self.parse_function_body(main_sig.val, self._lexer, [scope_arg0])
  match ret._ret_fun {
    Some(fun) => fun._fun_name = Some("main")
    None => ()
  }

  if !self._lexer.is_eof() {
    raise ParseError::Msg(
      "Syntax error, unexpected \{self._lexer.get_any_next_token()}",
    )
  }

  // Match refs/simple: unresolved forward refs are errors at end of parsing.
  self.check_forward_refs()

  self._scope.pop()

  for _, init in inits.val {
    ignore(init.unkeep())
    init.kill()
  }
  inits.val = Map::new()

  ignore(self._stop.peephole())
  if show {
    ignore(self.show_graph())
  }
  self._stop
}

///|
fn Parser::check_forward_refs(self : Parser) -> Unit raise ParseError {
  for v in self._scope._vars {
    if v._fref {
      raise ParseError::Msg("Undefined name '\{v._name}'")
    }
  }
}

///|
/// Parses a function body, assuming the header is parsed.
fn Parser::parse_function_body(
  self : Parser,
  sig : TypeFunPtr,
  loc : Lexer,
  ids : Array[String],
) -> Node raise ParseError {
  // Stack parser state on the local stack, and unstack it later.
  ignore(loc)
  let oldctrl = self._scope.ctrl().keep()
  let oldmem = self._scope.mem().keep()
  let oldfun = self._fun
  let old_break = self._break_scope
  let old_continue = self._continue_scope
  self._break_scope = None
  self._continue_scope = None

  let fun = self.peep(Node::new_fun(sig, start.val))
  self._fun = Some(fun)
  // Once the function header is available, install in linker table - allowing recursion.
  link_put(fun)

  let rpc = Node::new_parm(
    "$rpc",
    0,
    type_rpc_bot,
    fun,
    Node::new_constant(type_rpc_bot).peephole(),
  ).peephole()

  // Build a multi-exit return point for all function returns.
  let r = Node::new_region_in_progress().peephole()
  let rmem = Node::new_phi(scope_mem0, type_mem_bot, [Some(r), None]).peephole()
  let rrez = Node::new_phi(scope_arg0, bottom, [Some(r), None]).peephole()
  let ret = Node::new_return(r, rmem, rrez, rpc, fun).peephole()
  fun._fun_ret = Some(ret)
  ignore(self._stop.add_return(ret))

  // Pre-call the function from Start, with worse-case arguments.
  self._scope.push(in_fun=true)
  ignore(self._scope.set_def(0, Some(fun)))

  // Private mem alias tracking per function.
  let mem = Node::new_mem()
  ignore(mem.add_def(None))
  ignore(
    mem.add_def(
      Some(
        Node::new_parm(
          scope_mem0,
          1,
          type_mem_bot,
          fun,
          Node::new_constant(type_mem_bot).peephole(),
        ).peephole(),
      ),
    ),
  )
  ignore(self._scope.set_def(1, Some(mem)))

  // All args, "as-if" called externally.
  for i = 0; i < ids.length(); i = i + 1 {
    let t = sig.arg(i)
    ignore(
      self._scope.define_(
        ids[i],
        t,
        false,
        Node::new_parm(
          ids[i],
          i + 2,
          t,
          fun,
          Node::new_constant(t).peephole(),
        ).peephole(),
      ),
    )
  }

  // Parse the body.
  let mut last = zero.val
  while !self._lexer.peek_char('}') && !self._lexer.is_eof() {
    last = self.parse_statement()
  }

  // Last expression is the return.
  if self._scope.ctrl().ty() == control {
    self.fun_add_return(self._scope.ctrl(), self._scope.mem().merge(), last)
  }

  // Pop off the in-progress null on the multi-exit Region merge.
  let r0 = ret.ctrl()
  let rmem0 = ret.input_exn(1)
  let rrez0 = ret.input_exn(2)
  r0.pop_n(1)
  rmem0.pop_n(1)
  rrez0.pop_n(1)

  // Force peeps, which have been avoided due to in-progress.
  let rmem1 = rmem0.peephole()
  let rrez1 = rrez0.peephole()
  let r1 = r0.peephole()
  ignore(ret.set_def(1, Some(rmem1)))
  ignore(ret.set_def(2, Some(rrez1)))
  ignore(ret.set_def(0, Some(r1)))
  ignore(ret.peephole())

  // Function scope ends.
  self._scope.pop()
  self._fun = oldfun
  self._break_scope = old_break
  self._continue_scope = old_continue

  // Reset control and memory to pre-function parsing days.
  ignore(self._scope.set_def(0, Some(oldctrl.unkeep())))
  ignore(self._scope.set_def(1, Some(oldmem.unkeep())))

  ret
}

///|
/// Add a function return exit to the current parsing function.
fn Parser::fun_add_return(self : Parser, ctrl : Node, rmem : Node, expr : Node) -> Unit {
  let fun = match self._fun {
    Some(fun) => fun
    None => panic()
  }
  let ret = match fun._fun_ret {
    Some(ret) => ret
    None => panic()
  }

  // Gather parse-time return types for error reporting (matches refs/simple).
  let t = expr.ty()
  ret._ret_mt = ret._ret_mt.meet(t)
  match t {
    Int(_) => ret._ret_ti = true
    Flt(_) => ret._ret_tf = true
    MemPtr(_, _) => ret._ret_tp = true
    _ => ()
  }
  if t == type_nil {
    ret._ret_tn = true
  }

  // Merge path into the one true Return.
  let r = ret.ctrl()
  let rmem_phi = ret.input_exn(1)
  let rrez_phi = ret.input_exn(2)

  // Pop "in-progress" null off.
  r.pop_n(1)
  rmem_phi.pop_n(1)
  rrez_phi.pop_n(1)

  // Add new return point.
  ignore(r.add_def(Some(ctrl)))
  ignore(rmem_phi.add_def(Some(rmem)))
  ignore(rrez_phi.add_def(Some(expr)))

  // Back to being in-progress.
  ignore(r.add_def(None))
  ignore(rmem_phi.add_def(None))
  ignore(rrez_phi.add_def(None))
}

///|
fn Parser::parse_block(self : Parser, in_con : Bool) -> Node raise ParseError {
  self._scope.push(in_con~)
  let mut last = zero.val
  while !self._lexer.peek_char('}') && !self._lexer.is_eof() {
    last = self.parse_statement()
  }
  ignore(last.keep())
  self._scope.pop()
  last.unkeep()
}

///|
fn Parser::parse_statement(self : Parser) -> Node raise ParseError {
  if self._lexer.matchx_syntax("return") {
    self.parse_return()
  } else if self._lexer.matchx_syntax("if") {
    self.parse_if()
  } else if self._lexer.matchx_syntax("while") {
    self.parse_while()
  } else if self._lexer.matchx_syntax("for") {
    self.parse_for()
  } else if self._lexer.matchx_syntax("break") {
    self.parse_break()
  } else if self._lexer.matchx_syntax("continue") {
    self.parse_continue()
  } else if self._lexer.matchx_syntax("struct") {
    ignore(self.parse_struct())
    zero.val
  } else if self._lexer.matchx_syntax("#showGraph") {
    ignore(self.show_graph())
    self.require_syntax(";")
    zero.val
  } else if self._lexer.matchx_syntax(";") {
    zero.val
  } else if self._lexer.peek_char('{') && !self.is_type_fun() {
    self.require_syntax("{")
    self.require(self.parse_block(false), "}")
  } else {
    self.parse_declaration_statement()
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
    ignore(self.parse_statement())
  }
  let lexlen = match self._scope._lex_size.last() {
    Some(n) => n
    None => panic()
  }
  let varlen = self._scope._vars.length()
  let s = Node::new_struct()
  let fields : Array[Field] = []
  for i = lexlen; i < varlen; i = i + 1 {
    let v = self._scope._vars[i]
    if v._fref {
      continue
    }
    ignore(s.add_def(self._scope.input(i)))
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
  let mut f_scope = self._scope.dup()

  // Parse true side
  ignore(self._scope.set_def(0, Some(if_t.unkeep())))
  self._scope.add_guards(if_t, Some(pred), false)
  let lhs0 = if stmt {
    self.parse_statement()
  } else {
    self.parse_asgn()
  }
  let mut lhs = lhs0.keep()
  self._scope.remove_guards(if_t)
  // Match refs/simple: one-sided defs are errors; forward refs get copied across arms.
  f_scope.balance_if(self._scope)
  let t_scope = self._scope

  // Parse false side
  self._scope = f_scope
  ignore(self._scope.set_def(0, Some(if_f.unkeep())))
  self._scope.add_guards(if_f, Some(pred), true)
  let do_rhs = self._lexer.match_syntax(fside)
  let rhs0 = if do_rhs {
    if stmt {
      self.parse_statement()
    } else {
      self.parse_asgn()
    }
  } else {
    Node::new_constant(lhs.ty().make_zero()).peephole()
  }
  let mut rhs = rhs0.keep()
  self._scope.remove_guards(if_f)
  if do_rhs {
    f_scope = self._scope
  }
  ignore(pred.unkeep())

  // Widen ints to floats in a trinary
  if !stmt {
    let rhs1 = self.widen_int(rhs.unkeep(), lhs.ty()).keep()
    let lhs1 = self.widen_int(lhs.unkeep(), rhs1.ty()).keep()
    rhs = rhs1
    lhs = lhs1
  }

  // Merge results
  self._scope = t_scope
  t_scope.balance_if(f_scope)
  let r = self._scope.merge_scopes(f_scope)
  ignore(self._scope.set_def(0, Some(r)))
  let ret = self.peep(
    Node::new_phi("", lhs.ty().meet(rhs.ty()), [
      Some(r),
      Some(lhs.unkeep()),
      Some(rhs.unkeep()),
    ]),
  )
  if !stmt {
    match ret.err() {
      Some(err) => raise ParseError::Msg(err)
      None => ()
    }
  }
  ignore(r.peephole())
  ret
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
  ignore(self.parse_statement())
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
  zero.val
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
  self.fun_add_return(self._scope.ctrl(), self._scope.mem().merge(), expr)
  ignore(self._scope.set_def(0, Some(xctrl.val)))
  expr
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
/// A function type is `{ type... -> type }` or `{ type }`.
fn Parser::type_fun_ptr(self : Parser) -> Type? {
  let old = self._lexer._position
  if !self._lexer.match_syntax("{") {
    return None
  }
  let t0_res : Result[Type?, ParseError] = try? self.parse_type()
  let t0 = match t0_res {
    Ok(Some(t)) => t
    _ => {
      self._lexer._position = old
      return None
    }
  }
  if self._lexer.match_syntax("}") {
    let nilable = self._lexer.match_syntax("?")
    return Some(
      FunPtr({
        _nil: if nilable { 3 } else { 2 },
        _sig: Some([]),
        _ret: t0,
        _fidxs: -1L,
        _name: None,
      }),
    )
  }

  let ts : Array[Type] = [t0]
  while true {
    if self._lexer.match_syntax("->") {
      let ret_res : Result[Type?, ParseError] = try? self.parse_type()
      let ret = match ret_res {
        Ok(Some(t)) => t
        _ => {
          self._lexer._position = old
          return None
        }
      }
      if !self._lexer.match_syntax("}") {
        self._lexer._position = old
        return None
      }
      let nilable = self._lexer.match_syntax("?")
      return Some(
        FunPtr({
          _nil: if nilable { 3 } else { 2 },
          _sig: Some(ts),
          _ret: ret,
          _fidxs: -1L,
          _name: None,
        }),
      )
    }
    let t1_res : Result[Type?, ParseError] = try? self.parse_type()
    let t1 = match t1_res {
      Ok(Some(t)) => t
      _ => {
        self._lexer._position = old
        return None
      }
    }
    ts.push(t1)
  }
  // Unreachable, but required so the function has a value on all paths.
  None
}

/// True if a TypeFunPtr, without advancing parser.
fn Parser::is_type_fun(self : Parser) -> Bool {
  let old = self._lexer._position
  let tfp = self.type_fun_ptr()
  self._lexer._position = old
  tfp is Some(_)
}

///|
///|
fn Parser::parse_type(self : Parser) -> Type? raise ParseError {
  let old1 = self._lexer._position
  // Only type with a leading `{` is a function pointer.
  if self._lexer.peek_char('{') {
    return self.type_fun_ptr()
  }
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
    // If we have a constant funptr, attach its name to the linked Fun node (matches refs/simple).
    match (t, expr.ty()) {
      (FunPtr(_), FunPtr(fp)) if fp.is_constant() =>
        match link_get(fp) {
          Some(fun) => fun._fun_name = Some(name)
          None => ()
        }
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
  } else if self._lexer.matchx_syntax("true") {
    Node::new_constant(TypeInteger::constant(1L)).peephole()
  } else if self._lexer.matchx_syntax("false") {
    Node::new_constant(TypeInteger::constant(0L)).peephole()
  } else if self._lexer.matchx_syntax("null") {
    Node::new_constant(type_nil).peephole()
  } else if self._lexer.match_syntax("(") {
    self.require(self.parse_asgn(), ")")
  } else if self._lexer.matchx_syntax("new") {
    self.alloc()
  } else if self._lexer.match_syntax("{") {
    self.require(self.func(), "}")
  } else {
    let v = self.require_lookup_id("an identifier or expression")
    let rvalue = self._scope.input_exn(v._idx)
    if rvalue.ty() == bottom {
      if rvalue.kind == FRef {
        return rvalue
      }
      raise ParseError::Msg("Cannot read uninitialized field '\{v._name}'")
    }

    // Assign-update: x += e0;  x++;
    let ch = self._lexer.match_oper_assign()
    if ch == '\u{0000}' {
      return rvalue
    }
    let op = self.op_assign(ch, rvalue, v._final, v._type, v._name)
    self._scope.update(v._name, op)
    if Parser::postfix(ch) {
      rvalue.unkeep()
    } else {
      op
    }
  }
}

///|
fn Parser::postfix(ch : Char) -> Bool {
  ch == '\u{0001}' || ch == '\u{FFFF}'
}

///|
fn Parser::op_assign(
  self : Parser,
  ch : Char,
  lhs : Node,
  xfinal : Bool,
  t : Type,
  name : String,
) -> Node raise ParseError {
  if xfinal {
    raise ParseError::Msg("Cannot reassign final '\{name}'")
  }
  ignore(lhs.keep())
  let rhs = match ch {
    '\u{0001}' => Node::new_constant(TypeInteger::constant(1L)).peephole()
    '\u{FFFF}' => Node::new_constant(TypeInteger::constant(-1L)).peephole()
    _ => self.parse_asgn()
  }
  if !Parser::postfix(ch) {
    ignore(lhs.unkeep())
  }
  let op = match ch {
    '\u{0001}' | '\u{FFFF}' | '+' => Node::new_add(lhs, rhs)
    '-' => Node::new_sub(lhs, rhs)
    '*' => Node::new_mul(lhs, rhs)
    '/' => Node::new_div(lhs, rhs)
    _ => panic()
  }
  self.lift_expr(self.peep(op.widen()), t, false)
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
          ignore(self.parse_block(true))
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
  } else if self._lexer.match_syntax("(") {
    return self.parse_postfix(self.require(self.function_call(expr), ")"))
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
    tf,
    self.mem_alias(field._alias),
    expr.keep(),
    off,
  )
  if base_obj.is_ary() && name != "#" {
    ignore(load.set_def(0, Some(self._scope.ctrl())))
  }
  load = self.peep(load)

  // Check for assign-update, "ptr.fld += expr" or "ary[idx]++"
  let ch = self._lexer.match_oper_assign()
  if ch != '\u{0000}' {
    let op = self.op_assign(ch, load, field._final, tf, name)
    let st = Node::new_store(
      name,
      field._alias,
      tf,
      self.mem_alias(field._alias),
      expr.unkeep(),
      off,
      op,
      init=false,
    )
    if base_obj.is_ary() {
      ignore(st.set_def(0, Some(self._scope.ctrl())))
    }
    self.mem_alias_set(field._alias, self.peep(st))
    load = if Parser::postfix(ch) { load.unkeep() } else { op }
  } else {
    ignore(expr.unkeep())
  }
  ignore(off.unkeep())
  self.parse_postfix(load)
}

///|
/// Parse a function body; the caller will parse the surrounding "{}".
///
/// { [type arg,]* -> body }
/// { -> body }
fn Parser::func(self : Parser) -> Node raise ParseError {
  let ts : Array[Type] = []
  let ids : Array[String] = []
  self._lexer.skip_white_space()
  let loc = self._lexer
  while true {
    match self.parse_type() {
      None => break
      Some(t) => {
        let id = self.require_id()
        ts.push(t)
        ids.push(id)
        ignore(self._lexer.match_syntax(","))
      }
    }
  }
  self.require_syntax("->")

  // Make a concrete function type, with a fidx.
  let tfp = make_fun(ts, bottom)
  let ret = self.parse_function_body(tfp, loc, ids)
  let fun = match ret._ret_fun {
    Some(fun) => fun
    None => panic()
  }
  let sig = match fun._fun_sig {
    Some(sig) => sig
    None => panic()
  }
  Node::new_constant(FunPtr(sig)).peephole()
}

///|
/// Parse function call arguments; caller will parse the surrounding "()".
fn Parser::function_call(self : Parser, expr : Node) -> Node raise ParseError {
  if expr.ty() == type_nil {
    raise ParseError::Msg("Calling a null function pointer")
  }
  if expr.kind != FRef && !expr.ty().isa(type_funptr_bot) {
    raise ParseError::Msg("Expected a function but got \{expr.ty().glb().str()}")
  }
  ignore(expr.keep())

  let args : Array[Node] = []
  while !self._lexer.peek_char(')') {
    let arg = self.parse_asgn()
    args.push(arg.keep())
    if !self._lexer.match_syntax(",") {
      break
    }
  }

  let ctrl = self._scope.ctrl().keep()
  let mem = self._scope.mem().merge().keep()

  // Unkeep everything now that we have the call inputs wired.
  ignore(ctrl.unkeep())
  ignore(mem.unkeep())
  for a in args {
    ignore(a.unkeep())
  }
  ignore(expr.unkeep())

  // Dead into the call? Skip node gen.
  if ctrl.ty() == xcontrol {
    return Node::new_constant(top).peephole()
  }

  // Into the call.
  let call = Node::new_call(ctrl, mem, args, expr).peephole()

  // Post-call setup.
  let cend = Node::new_call_end(call).peephole()
  // Control from CallEnd.
  ignore(
    self._scope.set_def(
      0,
      Some(Node::new_cproj(cend, 0, scope_ctrl).peephole()),
    ),
  )
  // Memory from CallEnd.
  let mem0 = Node::new_mem()
  ignore(mem0.add_def(None))
  ignore(mem0.add_def(Some(Node::new_proj(cend, 1, scope_mem0).peephole())))
  ignore(self._scope.set_def(1, Some(mem0)))

  // Call result.
  Node::new_proj(cend, 2, "").peephole()
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
        Some(v) => {
          // Lookup worked on an out-of-function value.
          if self._scope.out_of_function(v) {
            // No closures, so this has to be a final constant (which includes forward refs).
            let def = self._scope.input_exn(v._idx)
            if def.kind != FRef && !(v._final && def.ty().is_constant()) {
              raise ParseError::Msg(
                "Variable '\{v._name}' is out of function scope and must be a final constant",
              )
            }
          }
          v
        }
        None => {
          // If missing, assume a forward reference (matches refs/simple).
          ignore(self._scope.define_(id, bottom, true, xctrl.val))
          match self._scope.lookup(id) {
            Some(v) => v
            None => panic()
          }
        }
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
