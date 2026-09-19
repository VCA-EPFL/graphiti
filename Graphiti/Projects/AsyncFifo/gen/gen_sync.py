#!/usr/bin/env python3
"""Generator for the proof part of `Bank.lean` (the write domain's register bank).

Run from the project root:  python3 Graphiti/Projects/AsyncFifo/gen/gen_bank.py

Same shape as the other netlists; what is new is that the bank has four output ports, so there
are four `out_*` lemmas and the output case of the refinement splits four ways.
"""

import pathlib

NODES = [("crF", ["in"]), ("s2", ["clk", "d", "clrn", "qh"]), ("clkF", ["in"]),
         ("s1", ["clk", "d", "clrn", "qh"])]
NAMES = [f"{n}_{p}" for n, ps in NODES for p in ps]
PORTS_OF = dict(NODES)
# `s1_qh` is what the first stage has reported; nothing in the block reads it back, so the
# invariant says nothing about it.
IGNORED = {"s1_qh"}
WFNAMES = [n for n in NAMES if n not in IGNORED]

INPUTS = [("clk", "sp.1", "clkF_in", "e_clk"),
          ("d", "sp.2.1", "s1_d", "e_d"),
          ("clrn", "sp.2.2.1", "crF_in", "e_crn")]
SPEC_STATE = {"clk": "(v, sp.2)", "d": "(sp.1, v, sp.2.2)", "clrn": "(sp.1, sp.2.1, v, sp.2.2.2)"}
# the second stage's report *is* the block's report
EQS = [("e_qh", "s2_qh", "s.2.2.2")]
HELD = {"clkF_in", "s1_d", "crF_in", "s2_qh"}
STATE_TY = "List Bool × List (BitVec 3) × List Bool × List (BitVec 3)"
BOOL_TY = {"s1_d": "List (BitVec 3)", "s2_d": "List (BitVec 3)",
           "s1_qh": "List (BitVec 3)", "s2_qh": "List (BitVec 3)"}

FIELD = {
    "s1_clk": ("pre", "clkF_in"), "s1_clrn": ("pre", "crF_in"),
    "s2_clk": ("pre", "clkF_in"), "s2_clrn": ("pre", "crF_in"),
    "s2_d": ("blk", "busOut", ["s1_clk", "s1_d", "s1_clrn"]),
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

CONNS = [("s1_clk", "clkF"), ("s2_clk", "clkF"), ("s1_clrn", "crF"), ("s2_clrn", "crF"),
         ("s2_d", "s1")]

OUTS = [("q", "List (BitVec 3)", "syncGateOut sp.1 sp.2.1 sp.2.2.1", "s2", "q")]

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
        else:
            pf = " ".join((growth if a == changed else "List.prefix_rfl") for a in k[2])
            out.append((f, f"Hψ.w_{f}.trans (busOut_mono {pf})"))
    return out

emit('''/-! ### The specification -/

/-- The synchroniser as a single block. -/
@[drcomponents]
def syncSpec : StringModule (List Bool × List (BitVec 3) × List Bool × List (BitVec 3)) :=
  { inputs := [ (↑"clk", ⟨List Bool, fun s v s' => s.1 ⊏ v ∧ s' = (v, s.2)⟩)
              , (↑"d", ⟨List (BitVec 3), fun s v s' => s.2.1 ⊏ v ∧ s' = (s.1, v, s.2.2)⟩)
              , (↑"clrn", ⟨List Bool, fun s v s' => s.2.2.1 ⊏ v ∧ s' = (s.1, s.2.1, v, s.2.2.2)⟩)
              ].toAssocList
    outputs := [ (↑"q", ⟨List (BitVec 3), fun s v s' => s.2.2.2 <+: v ∧
                    v <+: syncGateOut s.1 s.2.1 s.2.2.1 ∧ s' = (s.1, s.2.1, s.2.2.1, v)⟩) ].toAssocList
    internals := []
    init_state := fun s => s = ([], [], [], []) }

instance : MatchInterface syncNetlist syncSpec := by
  dsimp [syncNetlist, syncSpec]
  solve_match_interface

/-! ### The invariant -/
''')

emit("structure Wf " + " ".join(f"({n} : {ty_of(n)})" for n in WFNAMES) +
     f" (s : {STATE_TY}) : Prop where")
for port, field, node, eqname in INPUTS:
    emit(f"  {eqname} : {node} = {field.replace('sp', 's')}")
for eqname, node, field in EQS:
    emit(f"  {eqname} : {node} = {field}")
for n in WFNAMES:
    if n in HELD:
        continue
    emit(f"  w_{n} : {n} <+: {rhs_of(n)}")
emit()
proj = dict(zip(NAMES, projections("i")))
emit(f"def ψ (i : syncT) (s : {STATE_TY}) : Prop :=")
emit("  Wf " + " ".join(proj[f] for f in WFNAMES) + " s")
emit()
nfields = len([n for n in WFNAMES if n not in HELD])
emit("theorem Wf.init : Wf " + " ".join(["[]"] * len(WFNAMES)) + " ([], [], [], []) :=")
emit("  ⟨rfl, rfl, rfl, rfl, " + ", ".join(["List.nil_prefix"] * nfields) + "⟩")
emit()
emit("section SpecRules")
emit(f"variable (sp : {STATE_TY})")
emit()
for port, field, node, eqname in INPUTS:
    emit(f'theorem spec_in_{port} (v : {ty_of(node)}) (h : {field} ⊏ v) :')
    emit(f'    (syncSpec.inputs.getIO ↑"{port}").2 sp v {SPEC_STATE[port]} := by')
    emit( "  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩")
    emit()
for name, ty, stream, _, port in OUTS:
    emit(f'theorem spec_out_{port} (v : {ty}) (h1 : sp.2.2.2 <+: v) (h2 : v <+: {stream}) :')
    emit(f'    (syncSpec.outputs.getIO ↑"{port}").2 sp v (sp.1, sp.2.1, sp.2.2.1, v) := by')
    emit( "  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h1, h2, rfl⟩")
    emit()
emit("end SpecRules")
emit()
emit("section Cases")
emit("variable " + " ".join(f"{{{n} : {ty_of(n)}}}" for n in WFNAMES) + f" {{sp : {STATE_TY}}}")
emit("  (Hψ : Wf " + wf_call() + ")")
emit("include Hψ")
emit()

def emit_wf(upd, port=None, eqs=None):
    lines = []
    for p, f, n, e in INPUTS:
        lines.append(f"          {e} := " + ("rfl" if p == port else f"Hψ.{e}"))
    for e, n, f in EQS:
        lines.append(f"          {e} := " + ((eqs or {}).get(e, f"Hψ.{e}")))
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

for k, (tgt, src) in enumerate(CONNS):
    kind = FIELD[tgt]
    if kind[0] == "blk":
        emit(f"theorem int_{k} {{out : {ty_of(tgt)}}} (_h : {tgt} ⊏ out) (hout : out <+: {rhs_of(tgt)}) :")
        emit("    Wf " + wf_call((tgt, "out")) + " := by")
        upd = dict(update_fields(tgt, "(_h.isPrefix)"))
        upd[tgt] = "hout"
    else:
        newval = f"{src}_{PORTS_OF[src][0]}"
        emit(f"theorem int_{k} (_h : {tgt} ⊏ {newval}) :")
        emit("    Wf " + wf_call((tgt, newval)) + " := by")
        upd = dict(update_fields(tgt, f"Hψ.w_{tgt}"))
    emit_wf(upd)
    emit()

emit("/-- The second stage sees a prefix of the first stage's output, over prefixes of the")
emit("block's own clock and clear. -/")
emit("theorem out_q {v : List (BitVec 3)} (h : v <+: busOut s2_clk s2_d s2_clrn) :")
emit("    v <+: syncGateOut sp.1 sp.2.1 sp.2.2.1 :=")
emit("  h.trans (busOut_mono (Hψ.w_s2_clk.trans (Hψ.e_clk ▸ List.prefix_rfl))")
emit("    (Hψ.w_s2_d.trans (busOut_mono (Hψ.w_s1_clk.trans (Hψ.e_clk ▸ List.prefix_rfl))")
emit("      (Hψ.e_d ▸ List.prefix_rfl) (Hψ.w_s1_clrn.trans (Hψ.e_crn ▸ List.prefix_rfl))))")
emit("    (Hψ.w_s2_clrn.trans (Hψ.e_crn ▸ List.prefix_rfl)))")
emit()
emit()
emit("/-- What it has reported it has reported: the second stage records it. -/")
emit("theorem out_wf {v : List (BitVec 3)} :")
emit("    Wf " + wf_call(("s2_qh", "v"), "(sp.1, sp.2.1, sp.2.2.1, v)") + " := by")
emit_wf({}, eqs={"e_qh": "rfl"})
emit()
emit("end Cases")
emit()

DES_I, DES_M, DES_C = destructure(""), destructure("m_"), destructure("c_")
emit("/-! ### The refinement -/")
emit()
for k, (tgt, src) in enumerate(CONNS):
    blk = FIELD[tgt][0] == "blk"
    emit(f"theorem int_case_{k} (s : {STATE_TY}) (i mid : syncT) (Hψ : ψ i s)")
    emit(f"    (Hrule : (syncNetlist.internals.getD {k} (fun _ _ => False)) i mid) :")
    emit( "    ∃ s', existSR syncSpec.internals s s' ∧ ψ mid s' := by")
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
emit("theorem syncNetlist_internals_eq : syncNetlist.internals = [" +
     ", ".join(f"syncNetlist.internals.getD {k} (fun _ _ => False)" for k in range(len(CONNS))) +
     "] := rfl")
emit()
emit("theorem refines_ψ : syncNetlist ⊑_{ψ} syncSpec := by")
emit("  intro i s Hψ")
emit("  constructor")
emit("  · intro ident mid_i v Hrule")
emit(f"    obtain {DES_I} := i")
emit("    dsimp only [ψ] at Hψ")
emit(f"    obtain {DES_M} := mid_i")
emit("    case_transition Hcontains : Module.inputs syncNetlist, ident, (PortMap.getIO_not_contained_false' Hrule)")
emit("    dsimp only [syncNetlist] at Hcontains")
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
emit("    case_transition Hcontains : Module.outputs syncNetlist, ident, (PortMap.getIO_not_contained_false' Hrule)")
emit("    dsimp only [syncNetlist] at Hcontains")
emit("    simp at Hcontains")
emit("    subst Hcontains")
emit("    rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule")
emit("    dsimp only at Hrule")
emit("    simp only [Prod.mk.injEq, and_assoc] at Hrule")
emit("    repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)")
emit("    exact ⟨s, _, existSR_reflexive, spec_out_q s _ (Hψ.e_qh ▸ ‹_›) (out_q Hψ ‹_›), out_wf Hψ⟩")
emit("  · intro rule mid_i Hin Hrule")
emit("    rw [syncNetlist_internals_eq] at Hin")
emit("    simp only [List.mem_cons, List.not_mem_nil, or_false] at Hin")
emit("    rcases Hin with " + " | ".join(["h"] * len(CONNS)))
for k in range(len(CONNS)):
    emit(f"    · subst h; exact int_case_{k} s i mid_i Hψ Hrule")
emit()
emit("theorem refines_initial : Module.refines_initial syncNetlist syncSpec ψ := by")
emit("  intro i hi")
emit(f"  obtain {DES_I} := i")
emit("  dsimp only [syncNetlist] at hi")
emit("  simp only [Prod.mk.injEq, and_assoc] at hi")
emit("  obtain ⟨" + ", ".join(["rfl"] * len(NAMES)) + "⟩ := hi")
emit("  exact ⟨([], [], [], []), rfl, Wf.init⟩")
emit()
emit("/-- **The two registers refine the synchroniser's netlist block.** -/")
emit("theorem sync_refines : syncNetlist ⊑ syncSpec :=")
emit("  ⟨inferInstance, ψ, refines_ψ, refines_initial⟩")
emit()
emit("end Graphiti.AsyncFifo.Sync")

path = pathlib.Path("Graphiti/Projects/AsyncFifo/Sync.lean")
src2 = path.read_text()
marker = "-- HEADER_END (everything below is generated by gen/gen_sync.py)\n"
head2 = src2.split(marker)[0]
path.write_text(head2 + marker + "\n" + "\n".join(L) + "\n")
print(f"wrote {path} ({len(head2.splitlines()) + len(L)} lines)")
