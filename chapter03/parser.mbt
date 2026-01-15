///|
pub(all) suberror ParseError {
  Msg(String)
} derive(Show, Eq)

///|
struct Parser {
  mut _lexer : Lexer
  mut _scope : Node
}

///|
pub fn Parser::new(source : String) -> Parser {
  let lexer = Lexer::new(source)
  Node::reset()
  start.val = Node::new_start()
  { _lexer: lexer, _scope: Node::new_scope() }
}

///|
pub fn Parser::src(self : Parser) -> String {
  self._lexer._input.to_string()
}

///|
pub fn Parser::parse(self : Parser) -> Node raise ParseError {
  let ret = self.parse_block()
  if !self._lexer.is_eof() {
    raise ParseError::Msg(
      "Syntax error, unexpected \{self._lexer.get_any_next_token()}",
    )
  }
  match ret {
    Some(n) => n
    None => raise ParseError::Msg(self.error_syntax("a statement"))
  }
}

///|
fn Parser::parse_block(self : Parser) -> Node? raise ParseError {
  self._scope.push()
  let mut n : Node? = None
  while !self._lexer.peek_char('}') && !self._lexer.is_eof() {
    match self.parse_statement() {
      Some(n0) => n = Some(n0)
      None => ()
    }
  }
  self._scope.pop()
  n
}

///|
fn Parser::parse_statement(self : Parser) -> Node? raise ParseError {
  if self._lexer.matchx_syntax("return") {
    Some(self.parse_return())
  } else if self._lexer.matchx_syntax("int") {
    Some(self.parse_decl())
  } else if self._lexer.match_syntax("{") {
    let n = self.parse_block()
    self.require_syntax("}")
    n
  } else if self._lexer.matchx_syntax("#showGraph") {
    let n = self.show_graph()
    self.require_syntax(";")
    n
  } else if self._lexer.matchx_syntax(";") {
    None
  } else {
    Some(self.parse_expression_statement())
  }
}

///|
fn Parser::parse_return(self : Parser) -> Node raise ParseError {
  let expr = self.require(self.parse_expression(), ";")
  Node::new_return(start.val, expr).peephole()
}

///|
fn Parser::show_graph(_self : Parser) -> Node? {
  None
}

///|
fn Parser::parse_expression_statement(self : Parser) -> Node raise ParseError {
  let name = self.require_id()
  self.require_syntax("=")
  let expr = self.require(self.parse_expression(), ";")
  if self._scope.update(name, expr) is None {
    raise ParseError::Msg("Undefined name '\{name}'")
  }
  expr
}

///|
fn Parser::parse_decl(self : Parser) -> Node raise ParseError {
  let name = self.require_id()
  self.require_syntax("=")
  let expr = self.require(self.parse_expression(), ";")
  if self._scope.define_(name, expr) is None {
    raise ParseError::Msg("Redefining name '\{name}'")
  }
  expr
}

///|
fn Parser::parse_expression(self : Parser) -> Node raise ParseError {
  self.parse_addition()
}

///|
fn Parser::parse_addition(self : Parser) -> Node raise ParseError {
  let lhs = self.parse_multiplication()
  if self._lexer.match_syntax("+") {
    Node::new_add(lhs, self.parse_addition()).peephole()
  } else if self._lexer.match_syntax("-") {
    Node::new_sub(lhs, self.parse_addition()).peephole()
  } else {
    lhs
  }
}

///|
fn Parser::parse_multiplication(self : Parser) -> Node raise ParseError {
  let lhs = self.parse_unary()
  if self._lexer.match_syntax("*") {
    Node::new_mul(lhs, self.parse_multiplication()).peephole()
  } else if self._lexer.match_syntax("/") {
    Node::new_div(lhs, self.parse_multiplication()).peephole()
  } else {
    lhs
  }
}

///|
fn Parser::parse_unary(self : Parser) -> Node raise ParseError {
  if self._lexer.match_syntax("-") {
    Node::new_minus(self.parse_unary()).peephole()
  } else {
    self.parse_primary()
  }
}

///|
fn Parser::parse_primary(self : Parser) -> Node raise ParseError {
  if self._lexer.is_number() {
    self.parse_integer_literal()
  } else if self._lexer.match_syntax("(") {
    self.require(self.parse_expression(), ")")
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
fn Parser::parse_integer_literal(self : Parser) -> Node raise ParseError {
  Node::new_constant(self._lexer.parse_number()).peephole()
}

///|
fn Parser::is_keyword(id : String) -> Bool {
  id == "int" || id == "return"
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
fn Lexer::parse_number(self : Lexer) -> Type raise ParseError {
  let snum = self.parse_number_string()
  if snum.length() > 1 {
    match snum.get_char(0) {
      Some('0') =>
        raise ParseError::Msg(
          "Syntax error: integer values cannot start with '0'",
        )
      _ => ()
    }
  }
  let val = @strconv.parse_int64(snum.to_string_view(), base=10) catch {
    _ => raise ParseError::Msg("Syntax error, expected integer literal")
  }
  TypeInteger::constant(val)
}

///|
fn Lexer::parse_number_string(self : Lexer) -> String {
  let start = self._position
  while self.is_number() {
    self._position += 1
  }
  let end = self._position
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
    Some(ch) => "=;[]<>(){}+-/*!".contains_char(ch)
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
