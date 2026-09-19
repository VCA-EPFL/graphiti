import pathlib

REDUCE = """  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module,
    ExprLow.build_module', toString]
  simp only [drenv]
  dsimp
  dsimp [Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts, Module.mapInputPorts, reduceAssocListfind?]
  simp (disch := decide) only [AssocList.bijectivePortRenaming_invert]
  dsimp [Module.product]
  dsimp only [reduceModuleconnect'2]
  dsimp only [reduceEraseAll]
  dsimp; dsimp -failIfUnchanged [reduceAssocListfind?]
  unfold Module.connect''
  dsimp [Module.liftL, Module.liftR, drcomponents]
  rfl"""

# tag, envG, lowered, env, T, netlist, spec, spec_refines, doc, subs=[(node, impl, env_lemma, refines)]
BLOCKS = [
  ("bus", "benvG", "BusReg.busLowered", "BusReg.benv", "BusReg.busT", "BusReg.busNetlist",
   "BusReg.busSpec", "BusReg.reg_refines",
   "the three-bit Gray-pointer register, its three flip-flops expanded to gates",
   [("dff", "Dff.dffNetlist", "BusReg.benv_dff", "Dff.dff_refines")]),
  ("st", "senvG", "StReg.stLowered", "StReg.senv", "StReg.stT", "StReg.stNetlist",
   "StReg.stSpec", "StReg.reg_refines",
   "the write domain's seven-bit state register, its flip-flops expanded to gates",
   [("dff", "Dff.dffNetlist", "StReg.senv_dff", "Dff.dff_refines")]),
  ("stR", "senvRG", "StRegR.stLowered", "StRegR.senv", "StRegR.stT", "StRegR.stNetlist",
   "StRegR.stSpec", "StRegR.reg_refines",
   "the read domain's seven-bit state register, its flip-flops expanded to gates",
   [("dff", "Dff.dffNetlist", "StRegR.senv_dff", "Dff.dff_refines")]),
  ("mem", "menvG", "Mem.memLowered", "Mem.menv", "Mem.memT", "Mem.memNetlist",
   "Mem.memSpec", "Mem.mem_refines",
   "the four-entry register file, its cells expanded to gates",
   [("cell", "EnReg.enNetlist", "Mem.menv_cell", "EnReg.en_refines")]),
  ("bank", "kenvG", "Bank.bankLowered", "Bank.kenv", "Bank.bankT", "Bank.bankNetlist",
   "Bank.bankSpec", "Bank.bank_refines",
   "**the write domain's whole state as gates**: state register, Gray pointer and register file",
   [("streg", "stNetlistG", "Bank.kenv_streg", "stG_refines"),
    ("busreg", "busNetlistG", "Bank.kenv_busreg", "busG_refines"),
    ("memory", "memNetlistG", "Bank.kenv_memory", "memG_refines")]),
  ("bankR", "kenvRG", "BankR.bankLowered", "BankR.kenv", "BankR.bankT", "BankR.bankNetlist",
   "BankR.bankSpec", "BankR.bank_refines",
   "**the read domain's whole state as gates**: state register and Gray pointer",
   [("streg", "stRNetlistG", "BankR.kenv_streg", "stRG_refines"),
    ("busreg", "busNetlistG", "BankR.kenv_busreg", "busG_refines")]),
]

L = []
def e(s=""): L.append(s)

for tag, envG, lowered, env, T, netlist, spec, spec_ref, doc, subs in BLOCKS:
    NG = f"{tag}NetlistG"
    e(f"/-! ### {doc[0].upper() + doc[1:]} -/")
    e()
    expr = env
    for n, impl, _, _ in reversed(subs):
        expr = f'AssocList.cons "{n}" ⟨_, {impl}⟩\n    ({expr})'
    e(f"def {envG} : AssocList String (TModule1 String) :=")
    e(f"  {expr}")
    e()
    e(f"def {NG} := [e| {lowered}, {envG}.find? ]")
    e()
    for n, impl, _, _ in subs:
        e(f'theorem {envG}_{n} : {envG}.find? "{n}" = .some ⟨_, {impl}⟩ := rfl')
    e()
    hyps = " ".join(f'(h{k} : t ≠ "{n}")' for k, (n, _, _, _) in enumerate(subs))
    e(f"theorem {envG}_find_ne (t : String) {hyps} :")
    e(f"    {envG}.find? t = {env}.find? t := by")
    for k, (n, _, _, _) in enumerate(subs):
        e(f'  have e{k} : ("{n}" == t) = false := beq_eq_false_iff_ne.mpr (Ne.symm h{k})')
    e(f"  simp [{envG}, AssocList.find?, " + ", ".join(f"e{k}" for k in range(len(subs))) + "]")
    e()
    e(f"theorem wf_{envG} : ExprLow.wf {envG}.find? {lowered} := by rfl")
    e(f"theorem wf_{tag}env : ExprLow.wf {env}.find? {lowered} := by rfl")
    e()
    e(f"seal {env} in")
    e(f"theorem {tag}Netlist_sigma :")
    e(f"    (⟨{T}, {netlist}⟩ : Σ T, StringModule T) =")
    e(f"      ExprLow.build_module {env}.find? {lowered} := by")
    e(REDUCE)
    e()
    e(f"/-- **{doc[0].upper() + doc[1:]}.** -/")
    e(f"theorem {tag}G_refines : {NG} ⊑ {spec} := by")
    e(f"  refine Module.refines_transitive _ ?_ {spec_ref}")
    e(f"  refine Module.refines_transitive _ ?_ (Module.refines_eq' {tag}Netlist_sigma.symm)")
    e(f"  apply ExprLow.refines_env _ wf_{envG} wf_{tag}env")
    e("  intro i t")
    for k, (n, _, envlem, ref) in enumerate(subs):
        e(f'  by_cases h{k} : t = "{n}"')
        e(f"  · subst h{k}")
        e(f"    exact ExprLow.refines_base_of_refines i _ {envG}_{n} {envlem} {ref}")
    e(f"  · exact ExprLow.refines_base_of_eq i t ({envG}_find_ne t " +
      " ".join(f"h{k}" for k in range(len(subs))) + ")")
    e()

path = pathlib.Path("Graphiti/Projects/AsyncFifo/GateRegs.lean")
src = path.read_text()
marker = "-- HEADER_END (everything below is generated by gen/gen_gateregs.py)\n"
head = src.split(marker)[0]
path.write_text(head + marker + "\n" + "\n".join(L) + "\nend Graphiti.AsyncFifo.GateRegs\n")
print(f"wrote {path} ({len(head.splitlines()) + len(L)} lines)")
