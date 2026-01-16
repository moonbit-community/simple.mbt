///|
test "chapter20: regalloc dump" {
  let code = CodeGen::new("return (arg+1)+(arg+2);")
  ignore(
    code
    .parse()
    .opto()
    .type_check()
    .inst_select("x86_64_v2", "SystemV")
    .gcm()
    .local_sched()
    .reg_alloc(),
  )
  inspect(
    code.reg_alloc_dump(),
    content="shli -> v0\naddi -> v1",
  )
}
