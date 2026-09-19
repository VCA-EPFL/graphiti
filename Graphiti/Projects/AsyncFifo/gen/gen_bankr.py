#!/usr/bin/env python3
"""Generator for the proof part of `BankR.lean` (the read domain's register bank).

Run from the project root:  python3 Graphiti/Projects/AsyncFifo/gen/gen_bankr.py

`gen_bank.py` at the read domain's records and without the register file: two registers, three
output ports.
"""

import pathlib

NODES = [("stF", ["in"]), ("crF", ["in"]), ("stR", ["clk", "d", "clrn", "qh"]),
         ("clkF", ["in"]), ("unpN", ["d"]), ("emptyA", ["q"]),
         ("grR", ["clk", "d", "clrn", "qh"])]
NAMES = [f"{n}_{p}" for n, ps in NODES for p in ps]
PORTS_OF = dict(NODES)
# what the state register has reported; the fork in front of the `st` port reads it, not the
# register's own record, so the invariant says nothing about `stR_qh`
IGNORED = {"stR_qh"}
WFNAMES = [n for n in NAMES if n not in IGNORED]

INPUTS = [("clk", "sp.1", "clkF_in", "e_clk"),
          ("d", "sp.2.1", "unpN_d", "e_d"),
          ("clrn", "sp.2.2.1", "crF_in", "e_crn")]
SPEC_STATE = {"clk": "(v, sp.2)", "d": "(sp.1, v, sp.2.2)", "clrn": "(sp.1, sp.2.1, v, sp.2.2.2)"}
# the two registers that record what they reported: the block's record *is* theirs
EQS = [("e_grh", "grR_qh", "s.2.2.2.2.2")]
# the two ports that leave through an adapter, which keeps no record of its own
HISTS = [("h_st", "s.2.2.2.1", "stF_in"), ("h_empty", "s.2.2.2.2.1", "emptyA_q.map (·.empty)")]
HELD = {"clkF_in", "unpN_d", "crF_in", "grR_qh"}
STATE_TY = ("List Bool × List (RNext 2) × List Bool × List (RSt 2) × List Bool × "
            "List (BitVec 3)")
BOOL_TY = {"stF_in": "List (RSt 2)", "stR_d": "List (RSt 2)", "emptyA_q": "List (RSt 2)",
           "grR_d": "List (BitVec 3)",
           "unpN_d": "List (RNext 2)", "stR_qh": "List (RSt 2)",
           "grR_qh": "List (BitVec 3)"}

# ('pre', src) | ('map', f, src) | ('blk', kind, [args])
FIELD = {
    "stR_clk": ("pre", "clkF_in"), "stR_clrn": ("pre", "crF_in"),
    "stR_d": ("map", "stOf", "unpN_d"),
    "grR_clk": ("pre", "clkF_in"), "grR_clrn": ("pre", "crF_in"),
    "grR_d": ("map", "gnextOf", "unpN_d"),
    "stF_in": ("blk", "StRegR.stOut", ["stR_clk", "stR_d", "stR_clrn"]),
    "emptyA_q": ("pre", "stF_in"),
}

def rhs_of(n):
    k = FIELD[n]
    if k[0] == "pre":
        return k[1]
    if k[0] == "map":
        return f"{k[1]} {k[2]}"
    return k[1] + " " + " ".join(k[2])

MENTIONS = {n: [] for n in NAMES}
for n in WFNAMES:
    if n in HELD:
        continue
    k = FIELD[n]
    srcs = [k[1]] if k[0] == "pre" else ([k[2]] if k[0] == "map" else k[2])
    for src in srcs:
        MENTIONS[src].append(n)

CONNS = [("stR_clk", "clkF"), ("grR_clk", "clkF"),
         ("stR_clrn", "crF"), ("grR_clrn", "crF"),
         ("stR_d", "unpN"), ("grR_d", "unpN"), ("stF_in", "stR"), ("emptyA_q", "stF")]

# the four output ports: name, type, the stream the specification bounds it by, the proof
OUTS = [("st", "List (RSt 2)", "StRegR.stOut sp.1 (stOf sp.2.1) sp.2.2.1", "stF_in", "st"),
        ("empty", "List Bool", "(StRegR.stOut sp.1 (stOf sp.2.1) sp.2.2.1).map (·.empty)",
         "emptyA_q", "empty"),
        ("gray", "List (BitVec 3)", "BusReg.busOut sp.1 (gnextOf sp.2.1) sp.2.2.1", "grR", "gray")]
# the spec state after each output, and where its record lives
OUT_STATE = {
  "st":    "(sp.1, sp.2.1, sp.2.2.1, v, sp.2.2.2.2)",
  "empty": "(sp.1, sp.2.1, sp.2.2.1, sp.2.2.2.1, v, sp.2.2.2.2.2)",
  "gray":  "(sp.1, sp.2.1, sp.2.2.1, sp.2.2.2.1, sp.2.2.2.2.1, v)"}
OUT_HIST = {"st": "sp.2.2.2.1", "empty": "sp.2.2.2.2.1", "gray": "sp.2.2.2.2.2"}

L = []
def emit(s=""):
    L.append(s)

def ty_of(n):
    return BOOL_TY.get(n, "List Bool")

def destructure(prefix=""):
    parts = []
    for node, ps in NODES:
        fs = [prefix + f"{node}_{p}" for p in ps]
        parts.append(fs[0] if len(ps) == 1 else "⟨" + ", ".join(fs) + "⟩")
    return "⟨" + ", ".join(parts) + "⟩"

def projections(v):
    out = []
    for k, (node, ps) in enumerate(NODES):
        base = v + ".2" * k + ("" if k == len(NODES) - 1 else ".1")
        if len(ps) == 1:
            out.append(base)
        else:
            for j in range(len(ps)):
                out.append(base + ".2" * j + (".1" if j < len(ps) - 1 else ""))
    return out

def wf_call(subst=None, state="sp"):
    def arg(f):
        return ("(" + subst[1] + ")") if subst and f == subst[0] else f
    return " ".join(arg(f) for f in WFNAMES) + " " + state

def update_fields(changed, growth):
    out = [(changed, "List.prefix_rfl")]
    for f in MENTIONS[changed]:
        k = FIELD[f]
        if k[0] == "pre":
            out.append((f, f"Hψ.w_{f}.trans {growth}"))
        elif k[0] == "map":
            out.append((f, f"Hψ.w_{f}.trans ({k[1]}_mono {growth})"))
        else:
            pf = " ".join((growth if a == changed else "List.prefix_rfl") for a in k[2])
            mono = {"StRegR.stOut": "StRegR.stOut_mono"}[k[1]]
            out.append((f, f"Hψ.w_{f}.trans ({mono} {pf})"))
    return out

emit('''/-! ### The specification -/

/-- The bank as a single block: the state register, the Gray pointer register and the `empty`
bit, over the fields of the next-state bus. -/
@[drcomponents]
def bankSpec : StringModule (List Bool × List (RNext 2) × List Bool × List (RSt 2) ×
    List Bool × List (BitVec 3)) :=
  { inputs := [ (↑"clk", ⟨List Bool, fun s v s' => s.1 ⊏ v ∧ s' = (v, s.2)⟩)
              , (↑"d", ⟨List (RNext 2), fun s v s' => s.2.1 ⊏ v ∧ s' = (s.1, v, s.2.2)⟩)
              , (↑"clrn", ⟨List Bool, fun s v s' => s.2.2.1 ⊏ v ∧
                  s' = (s.1, s.2.1, v, s.2.2.2)⟩)
              ].toAssocList
    outputs := [ (↑"st", ⟨List (RSt 2), fun s v s' => s.2.2.2.1 <+: v ∧
                    v <+: StRegR.stOut s.1 (stOf s.2.1) s.2.2.1 ∧
                    s' = (s.1, s.2.1, s.2.2.1, v, s.2.2.2.2)⟩)
               , (↑"empty", ⟨List Bool, fun s v s' => s.2.2.2.2.1 <+: v ∧
                    v <+: (StRegR.stOut s.1 (stOf s.2.1) s.2.2.1).map (·.empty) ∧
                    s' = (s.1, s.2.1, s.2.2.1, s.2.2.2.1, v, s.2.2.2.2.2)⟩)
               , (↑"gray", ⟨List (BitVec 3), fun s v s' => s.2.2.2.2.2 <+: v ∧
                    v <+: BusReg.busOut s.1 (gnextOf s.2.1) s.2.2.1 ∧
                    s' = (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, v)⟩)
               ].toAssocList
    internals := []
    init_state := fun s => s = ([], [], [], [], [], []) }

instance : MatchInterface bankNetlist bankSpec := by
  dsimp [bankNetlist, bankSpec]
  solve_match_interface

/-! ### The invariant -/
''')

emit("structure Wf " + " ".join(f"({n} : {ty_of(n)})" for n in WFNAMES) +
     f" (s : {STATE_TY}) : Prop where")
for port, field, node, eqname in INPUTS:
    emit(f"  {eqname} : {node} = {field.replace('sp', 's')}")
for eqname, node, field in EQS:
    emit(f"  {eqname} : {node} = {field}")
for hname, field, stream in HISTS:
    emit(f"  {hname} : {field} <+: {stream}")
for n in WFNAMES:
    if n in HELD:
        continue
    emit(f"  w_{n} : {n} <+: {rhs_of(n)}")
emit()
proj = dict(zip(NAMES, projections("i")))
emit(f"def ψ (i : bankT) (s : {STATE_TY}) : Prop :=")
emit("  Wf " + " ".join(proj[f] for f in WFNAMES) + " s")
emit()
nfields = len([n for n in WFNAMES if n not in HELD])
emit("theorem Wf.init : Wf " + " ".join(["[]"] * len(WFNAMES)) +
     " ([], [], [], [], [], []) :=")
emit("  ⟨rfl, rfl, rfl, rfl, " +
     ", ".join(["List.nil_prefix"] * (nfields + len(HISTS))) + "⟩")
emit()
emit("section SpecRules")
emit(f"variable (sp : {STATE_TY})")
emit()
for port, field, node, eqname in INPUTS:
    ty = ty_of(node)
    emit(f'theorem spec_in_{port} (v : {ty}) (h : {field} ⊏ v) :')
    emit(f'    (bankSpec.inputs.getIO ↑"{port}").2 sp v {SPEC_STATE[port]} := by')
    emit( "  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩")
    emit()
for name, ty, stream, _, port in OUTS:
    emit(f'theorem spec_out_{port} (v : {ty}) (h1 : {OUT_HIST[port]} <+: v)')
    emit(f'    (h2 : v <+: {stream}) :')
    emit(f'    (bankSpec.outputs.getIO ↑"{port}").2 sp v {OUT_STATE[port]} := by')
    emit( "  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h1, h2, rfl⟩")
    emit()
emit("end SpecRules")
emit()
emit("section Cases")
emit("variable " + " ".join(f"{{{n} : {ty_of(n)}}}" for n in WFNAMES) + f" {{sp : {STATE_TY}}}")
emit("  (Hψ : Wf " + wf_call() + ")")
emit("include Hψ")
emit()

def emit_wf(upd, port=None, extra=None):
    extra = extra or {}
    lines = []
    for p, f, n, e in INPUTS:
        lines.append(f"          {e} := " + ("rfl" if p == port else f"Hψ.{e}"))
    for e, n, f in EQS:
        lines.append(f"          {e} := " + extra.get(e, f"Hψ.{e}"))
    for hn, f, st in HISTS:
        lines.append(f"          {hn} := " + extra.get(hn, f"Hψ.{hn}"))
    for n in WFNAMES:
        if n in HELD:
            continue
        lines.append(f"          w_{n} := " + upd.get(n, f"Hψ.w_{n}"))
    lines[0] = "  exact {" + lines[0][9:]
    lines[-1] += " }"
    for l in lines:
        emit(l)

for port, field, node, eqname in INPUTS:
    emit(f"theorem in_{port} (v : {ty_of(node)}) (h : {node} ⊏ v) :")
    emit("    Wf " + wf_call((node, "v"), SPEC_STATE[port]) + " := by")
    emit(f"  have hm : {node} <+: v := h.isPrefix")
    emit_wf(dict(update_fields(node, "hm")), port)
    emit()

BLOCKS = {"stR": "StRegR.stOut", "grR": "BusReg.busOut"}
for k, (tgt, src) in enumerate(CONNS):
    kind = FIELD[tgt]
    if src in BLOCKS:
        emit(f"theorem int_{k} {{out : {ty_of(tgt)}}} (_h : {tgt} ⊏ out) (hout : out <+: {rhs_of(tgt)}) :")
        emit("    Wf " + wf_call((tgt, "out")) + " := by")
        upd = dict(update_fields(tgt, "(_h.isPrefix)"))
        upd[tgt] = "hout"
    else:
        newval = rhs_of(tgt) if kind[0] == "map" else f"{src}_{PORTS_OF[src][0]}"
        emit(f"theorem int_{k} (_h : {tgt} ⊏ {newval}) :")
        emit("    Wf " + wf_call((tgt, newval)) + " := by")
        upd = dict(update_fields(tgt, f"Hψ.w_{tgt}"))
    extra = {}
    if tgt == "stF_in":
        extra["h_st"] = "Hψ.h_st.trans (_h.isPrefix)"
        extra["h_empty"] = "Hψ.h_empty"
    if tgt == "emptyA_q":
        extra["h_empty"] = "Hψ.h_empty.trans (Hψ.w_emptyA_q.map _)"
    emit_wf(upd, extra=extra)
    emit()

emit("/-- Each block sees prefixes of the bank's own inputs. -/")
emit("theorem out_st : stF_in <+: StRegR.stOut sp.1 (stOf sp.2.1) sp.2.2.1 :=")
emit("  Hψ.w_stF_in.trans (StRegR.stOut_mono (Hψ.w_stR_clk.trans (Hψ.e_clk ▸ List.prefix_rfl))")
emit("    (Hψ.w_stR_d.trans (stOf_mono (Hψ.e_d ▸ List.prefix_rfl)))")
emit("    (Hψ.w_stR_clrn.trans (Hψ.e_crn ▸ List.prefix_rfl)))")
emit()
emit("theorem out_empty : emptyA_q.map (·.empty) <+: (StRegR.stOut sp.1 (stOf sp.2.1) sp.2.2.1).map (·.empty) :=")
emit("  (Hψ.w_emptyA_q.trans (out_st Hψ)).map _")
emit()
emit("theorem out_gray {v : List (BitVec 3)} (h : v <+: BusReg.busOut grR_clk grR_d grR_clrn) :")
emit("    v <+: BusReg.busOut sp.1 (gnextOf sp.2.1) sp.2.2.1 :=")
emit("  h.trans (BusReg.busOut_mono (Hψ.w_grR_clk.trans (Hψ.e_clk ▸ List.prefix_rfl))")
emit("    (Hψ.w_grR_d.trans (gnextOf_mono (Hψ.e_d ▸ List.prefix_rfl)))")
emit("    (Hψ.w_grR_clrn.trans (Hψ.e_crn ▸ List.prefix_rfl)))")
emit()
emit("/-! What it has reported it has reported: two ports leave through an adapter, which keeps")
emit("no record, so the block keeps it; the third leaves through a register that keeps its own,")
emit("and the block's record is that one. -/")
emit()
emit("theorem out_st_wf : Wf " + wf_call(None,
  "(sp.1, sp.2.1, sp.2.2.1, stF_in, sp.2.2.2.2)") + " := by")
emit_wf({}, extra={"h_st": "List.prefix_rfl"})
emit()
emit("theorem out_empty_wf : Wf " + wf_call(None,
  "(sp.1, sp.2.1, sp.2.2.1, sp.2.2.2.1, emptyA_q.map (·.empty), sp.2.2.2.2.2)") + " := by")
emit_wf({}, extra={"h_empty": "List.prefix_rfl"})
emit()
emit("theorem out_gray_wf {v : List (BitVec 3)} : Wf " + wf_call(("grR_qh", "v"),
  "(sp.1, sp.2.1, sp.2.2.1, sp.2.2.2.1, sp.2.2.2.2.1, v)") + " := by")
emit_wf({}, extra={"e_grh": "rfl"})
emit()
emit("end Cases")
emit()

DES_I, DES_M, DES_C = destructure(""), destructure("m_"), destructure("c_")
emit("/-! ### The refinement -/")
emit()
for k, (tgt, src) in enumerate(CONNS):
    blk = src in BLOCKS
    emit(f"theorem int_case_{k} (s : {STATE_TY}) (i mid : bankT) (Hψ : ψ i s)")
    emit(f"    (Hrule : (bankNetlist.internals.getD {k} (fun _ _ => False)) i mid) :")
    emit( "    ∃ s', existSR bankSpec.internals s s' ∧ ψ mid s' := by")
    emit(f"  obtain {DES_I} := i")
    emit(f"  obtain {DES_M} := mid")
    emit( "  dsimp only [ψ] at Hψ ⊢")
    emit( "  have H := Hrule.1 rfl")
    emit( "  clear Hrule")
    emit(f"  obtain ⟨{DES_C}, out, Hrule⟩ := H")
    emit( "  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule")
    emit( "  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)")
    emit(f"  exact ⟨s, existSR_reflexive, int_{k} Hψ ‹_›" + (" ‹_›⟩" if blk else "⟩"))
    emit()
emit("theorem bankNetlist_internals_eq : bankNetlist.internals = [" +
     ", ".join(f"bankNetlist.internals.getD {k} (fun _ _ => False)" for k in range(len(CONNS))) +
     "] := rfl")
emit()
emit("theorem refines_ψ : bankNetlist ⊑_{ψ} bankSpec := by")
emit("  intro i s Hψ")
emit("  constructor")
emit("  · intro ident mid_i v Hrule")
emit(f"    obtain {DES_I} := i")
emit("    dsimp only [ψ] at Hψ")
emit(f"    obtain {DES_M} := mid_i")
emit("    case_transition Hcontains : Module.inputs bankNetlist, ident, (PortMap.getIO_not_contained_false' Hrule)")
emit("    dsimp only [bankNetlist] at Hcontains")
emit("    simp at Hcontains")
emit("    rcases Hcontains with " + " | ".join(["h"] * len(INPUTS)))
emit("    all_goals subst h")
emit("    all_goals rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule")
emit("    all_goals dsimp only at Hrule")
emit("    all_goals simp only [Prod.mk.injEq, and_assoc] at Hrule")
emit("    all_goals repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)")
emit("    all_goals first")
for port, field, node, eqname in INPUTS:
    emit(f"      | exact ⟨_, _, spec_in_{port} s _ (by rw [← Hψ.{eqname}]; assumption), "
         f"existSR_reflexive, in_{port} Hψ _ ‹_›⟩")
emit("  · intro ident mid_i v Hrule")
emit(f"    obtain {DES_I} := i")
emit("    dsimp only [ψ] at Hψ")
emit(f"    obtain {DES_M} := mid_i")
emit("    case_transition Hcontains : Module.outputs bankNetlist, ident, (PortMap.getIO_not_contained_false' Hrule)")
emit("    dsimp only [bankNetlist] at Hcontains")
emit("    simp at Hcontains")
emit("    rcases Hcontains with " + " | ".join(["h"] * len(OUTS)))
emit("    all_goals subst h")
emit("    all_goals rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule")
emit("    all_goals dsimp only at Hrule")
emit("    all_goals simp only [Prod.mk.injEq, and_assoc] at Hrule")
emit("    all_goals repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)")
emit("    all_goals first")
emit("      | exact ⟨s, _, existSR_reflexive, spec_out_st s _ Hψ.h_st (out_st Hψ), out_st_wf Hψ⟩")
emit("      | exact ⟨s, _, existSR_reflexive, spec_out_empty s _ Hψ.h_empty (out_empty Hψ),")
emit("          out_empty_wf Hψ⟩")
emit("      | exact ⟨s, _, existSR_reflexive, spec_out_gray s _ (Hψ.e_grh ▸ ‹_›)")
emit("          (out_gray Hψ ‹_›), out_gray_wf Hψ⟩")
emit("  · intro rule mid_i Hin Hrule")
emit("    rw [bankNetlist_internals_eq] at Hin")
emit("    simp only [List.mem_cons, List.not_mem_nil, or_false] at Hin")
emit("    rcases Hin with " + " | ".join(["h"] * len(CONNS)))
for k in range(len(CONNS)):
    emit(f"    · subst h; exact int_case_{k} s i mid_i Hψ Hrule")
emit()
emit("theorem refines_initial : Module.refines_initial bankNetlist bankSpec ψ := by")
emit("  intro i hi")
emit(f"  obtain {DES_I} := i")
emit("  dsimp only [bankNetlist] at hi")
emit("  simp only [Prod.mk.injEq, and_assoc] at hi")
emit("  obtain ⟨" + ", ".join(["rfl"] * len(NAMES)) + "⟩ := hi")
emit("  exact ⟨([], [], [], [], [], []), rfl, Wf.init⟩")
emit()
emit("/-- **The two registers refine the read domain's register bank.** -/")
emit("theorem bank_refines : bankNetlist ⊑ bankSpec :=")
emit("  ⟨inferInstance, ψ, refines_ψ, refines_initial⟩")
emit()
emit("end Graphiti.AsyncFifo.BankR")

path = pathlib.Path("Graphiti/Projects/AsyncFifo/BankR.lean")
src = path.read_text()
marker = "-- HEADER_END (everything below is generated by gen/gen_bankr.py)\n"
head = src.split(marker)[0]
path.write_text(head + marker + "\n" + "\n".join(L) + "\n")
print(f"wrote {path} ({len(head.splitlines()) + len(L)} lines)")
