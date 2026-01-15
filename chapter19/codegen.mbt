///|
pub enum Phase {
  Parse
  Opto
  TypeCheck
  InstructionSelection
  Schedule
  LocalSched
  RegAlloc
} derive(Eq, Show)

///|
pub enum CallingConv {
  Win64
  SystemV
} derive(Eq, Show)

///|
pub struct CodeGen {
  // Matches refs/simple intent: drive a compilation pipeline across phases.
  mut _phase : Phase?

  // Compilation source code
  _src : String
  _arg : Type
  mut _calling_conv : CallingConv?

  // Start and stop; end points of the generated IR
  mut _start : Node
  mut _stop : Node

  // Parser object
  mut _parser : Parser
}

///|
pub fn CodeGen::new(src : String, arg? : Type = type_integer_bot) -> CodeGen {
  let p = Parser::new_with_arg(src, arg)
  {
    _phase: None,
    _src: src,
    _arg: arg,
    _calling_conv: None,
    _start: start.val,
    _stop: p._stop,
    _parser: p,
  }
}

///|
pub fn CodeGen::parse(
  self : CodeGen,
  show? : Bool = false,
) -> CodeGen raise ParseError {
  self._phase = Some(Parse)
  self._stop = self._parser.parse(show~)
  self._start = start.val
  self
}

///|
pub fn CodeGen::opto(self : CodeGen) -> CodeGen raise ParseError {
  self._phase = Some(Opto)
  // Reuse the existing chapter pipeline: IterPeeps + error checking + CFG build.
  self._stop = self._stop.iterate()
  self
}

///|
pub fn CodeGen::type_check(self : CodeGen) -> CodeGen raise ParseError {
  self._phase = Some(TypeCheck)
  match self._stop.walk_err() {
    Some(err) => raise ParseError::Msg(err)
    None => ()
  }
  self
}

///|
pub fn CodeGen::inst_select(
  self : CodeGen,
  _cpu : String,
  calling_conv : String,
) -> CodeGen {
  self._phase = Some(InstructionSelection)
  self._calling_conv = if calling_conv == "SystemV" {
    Some(CallingConv::SystemV)
  } else if calling_conv == "Win64" {
    Some(CallingConv::Win64)
  } else {
    None
  }
  // TODO(chapter19): machine ports + instruction selection.
  self
}

///|
pub fn CodeGen::gcm(self : CodeGen, _show? : Bool = false) -> CodeGen {
  self._phase = Some(Schedule)
  // The existing chapter implementation performs scheduling inside Node::iterate.
  // Keep this as a no-op placeholder for now (refs/simple has an explicit phase).
  self
}

///|
pub fn CodeGen::local_sched(self : CodeGen) -> CodeGen {
  self._phase = Some(LocalSched)
  // TODO(chapter19): list scheduler; refs/simple uses ListScheduler.sched(this).
  self
}

///|
pub fn CodeGen::print(self : CodeGen) -> String {
  self._stop.print()
}
