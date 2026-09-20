#!/usr/bin/env python3
"""Generator for the proof part of `EnReg.lean` (a memory cell: flip-flop plus multiplexer).

Run from the project root:  python3 Graphiti/Projects/AsyncFifo/gen/gen_enreg.py

The same three pieces as `gen_dff.py`, over a different netlist: the structural invariant `Wf`
(each node holds a prefix of what drives it), `wf_sim` (one induction on the instant turns that
into the values of the run), and one lemma per rule.
"""

import pathlib

F, G1, G2, G3 = ["in"], ["a"], ["a", "b"], ["a", "b", "c"]
CUT = ["in", "r1", "r2", "r3", "r4"]

# The nodes in the order the lowered state tuple presents them, with their port names.
NODES = [("n2", G3), ("enf", F), ("n5f", F), ("qg", G2), ("qf", F), ("t1", G2), ("crf", F),
         ("n5", G2), ("n6", G3), ("n4", G3), ("n4f", F), ("n3", G3), ("n1", G2), ("n3f", F),
         ("dataf", F), ("t2", G2), ("clkf", F), ("n2f", F), ("cut", CUT), ("mx", G2), ("nen", G1)]

def fields_of(node, ports):
    return [f"{node}_{p}" for p in ports]

NAMES = [f for node, ps in NODES for f in fields_of(node, ps)]

INPUTS = [("clk", "sp.1", "clkf_in", "e_clk"),
          ("en", "sp.2.1", "enf_in", "e_en"),
          ("data", "sp.2.2.1", "dataf_in", "e_data"),
          ("clrn", "sp.2.2.2", "crf_in", "e_crn")]
SPEC_STATE = {"clk": "(v, sp.2)", "en": "(sp.1, v, sp.2.2)",
              "data": "(sp.1, sp.2.1, v, sp.2.2.2)", "clrn": "(sp.1, sp.2.1, sp.2.2.1, v)"}
HELD = {"clkf_in": "clk", "enf_in": "en", "dataf_in": "data", "crf_in": "crn"}
STATE_TY = "List Bool × List Bool × List Bool × List Bool"

# One stream per wire carries that wire's value: the wire's single consumer.
#   representative, the automaton field it holds, the gate driving it, its stored inputs
REPS = [
    ("n2_a",   "n1",  "gateOut nand2",  ["n1_a", "n1_b"]),
    ("n2f_in", "n2",  "gate3Out nand3", ["n2_a", "n2_b", "n2_c"]),
    ("n3f_in", "n3",  "gate3Out nand3", ["n3_a", "n3_b", "n3_c"]),
    ("n4f_in", "n4",  "gate3Out nand3", ["n4_a", "n4_b", "n4_c"]),
    ("n5f_in", "n5",  "gateOut nand2",  ["n5_a", "n5_b"]),
    ("n5_b",   "n6",  "gate3Out nand3", ["n6_a", "n6_b", "n6_c"]),
    ("qf_in",  "q",   "gateOut and2",   ["qg_a", "qg_b"]),
    ("t2_a",   "nen", "gate1Out not",   ["nen_a"]),
    ("mx_a",   "t1",  "gateOut and2",   ["t1_a", "t1_b"]),
    ("mx_b",   "t2",  "gateOut and2",   ["t2_a", "t2_b"]),
    ("n4_b",   "m",   "gateOut or2",    ["mx_a", "mx_b"]),
]
GATE_OF = {rep: (g, args) for rep, _, g, args in REPS}
REP_IDX = {rep: i for i, (rep, _, _, _) in enumerate(REPS)}

SRC = {
    "n1_a": "n4f_in", "n1_b": "n2f_in",
    "n2_b": "clkf_in", "n2_c": "crf_in",
    "n3_a": "n2f_in", "n3_b": "clkf_in", "n3_c": "n4f_in",
    "n4_a": "n3f_in", "n4_c": "crf_in",
    "n5_a": "n2f_in",
    "n6_a": "n5f_in", "n6_b": "n3f_in", "n6_c": "crf_in",
    "qg_a": "n5f_in", "qg_b": "crf_in",
    "nen_a": "enf_in", "t1_a": "enf_in", "t1_b": "dataf_in", "t2_b": "qf_in",
    "cut_in": "qf_in", "cut_r1": "clkf_in", "cut_r2": "enf_in", "cut_r3": "dataf_in",
    "cut_r4": "crf_in",
}

# The connections, in the order `enLowered` lists them: (target stream, source node).
CONNS = [("n2_b", "clkf"), ("n3_b", "clkf"), ("cut_r1", "clkf"),
         ("n2_c", "crf"), ("n4_c", "crf"), ("n6_c", "crf"), ("qg_b", "crf"), ("cut_r4", "crf"),
         ("nen_a", "enf"), ("t1_a", "enf"), ("cut_r2", "enf"),
         ("t1_b", "dataf"), ("cut_r3", "dataf"),
         ("t2_a", "nen"), ("t2_b", "qf"), ("cut_in", "qf"),
         ("mx_a", "t1"), ("mx_b", "t2"), ("n4_b", "mx"),
         ("n1_a", "n4f"), ("n1_b", "n2f"), ("n2_a", "n1"), ("n2f_in", "n2"),
         ("n3_a", "n2f"), ("n3_c", "n4f"), ("n3f_in", "n3"), ("n4_a", "n3f"), ("n4f_in", "n4"),
         ("n5_a", "n2f"), ("n5_b", "n6"), ("n5f_in", "n5"), ("n6_a", "n5f"), ("n6_b", "n3f"),
         ("qg_a", "n5f"), ("qf_in", "qg")]

PORTS_OF = dict(NODES)

def gate_expr(rep):
    g, args = GATE_OF[rep]
    return f"{g} " + " ".join(args)

def rhs_of(name):
    if name in GATE_OF:
        return gate_expr(name)
    return SRC[name]

def mono_of(rep):
    g, args = GATE_OF[rep]
    lem = ("gate3Out_mono" if g.startswith("gate3") else
           "gate1Out_mono" if g.startswith("gate1") else "gateOut_mono")
    return lem, args

MENTIONS = {n: [] for n in NAMES}
for rep, _, _, args in REPS:
    for a in args:
        MENTIONS[a].append(rep)
for n, s in SRC.items():
    MENTIONS[s].append(n)

L = []
def emit(s=""):
    L.append(s)

def destructure(prefix=""):
    parts = []
    for node, ps in NODES:
        fs = fields_of(node, ps)
        parts.append(prefix + fs[0] if len(ps) == 1 else
                     "⟨" + ", ".join(prefix + f for f in fs) + "⟩")
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

def psi_args(subst=None):
    return " ".join((("(" + subst[1] + ")") if subst and f == subst[0] else f) for f in NAMES)

def update_fields(changed, growth):
    out = [(changed, "List.prefix_rfl")]
    for f in MENTIONS[changed]:
        if f in GATE_OF:
            mono, args = mono_of(f)
            pf = " ".join((growth if a == changed else "List.prefix_rfl") for a in args)
            out.append((f, f"Hψ.w_{f}.trans ({mono} _ {pf})"))
        else:
            out.append((f, f"Hψ.w_{f}.trans {growth}"))
    return out

emit('''/-! ### The specification -/

/-- The cell as a single block: it stores its four inputs, and its output is a prefix of the
stream the automaton gives. -/
@[drcomponents]
def enSpec : StringModule (List Bool × List Bool × List Bool × List Bool) :=
  { inputs := [ (↑"clk", ⟨List Bool, fun s v s' => s.1 ⊏ v ∧ s' = (v, s.2)⟩)
              , (↑"en", ⟨List Bool, fun s v s' => s.2.1 ⊏ v ∧ s' = (s.1, v, s.2.2)⟩)
              , (↑"data", ⟨List Bool, fun s v s' => s.2.2.1 ⊏ v ∧ s' = (s.1, s.2.1, v, s.2.2.2)⟩)
              , (↑"clrn", ⟨List Bool, fun s v s' => s.2.2.2 ⊏ v ∧ s' = (s.1, s.2.1, s.2.2.1, v)⟩)
              ].toAssocList
    outputs := [ (↑"q", ⟨List Bool, fun s v s' => s' = s ∧ v <+: enOut s.1 s.2.1 s.2.2.1 s.2.2.2⟩)
               ].toAssocList
    internals := []
    init_state := fun s => s = ([], [], [], []) }

instance : MatchInterface enNetlist enSpec := by
  dsimp [enNetlist, enSpec]
  solve_match_interface

/-! ### The invariant -/
''')

emit("structure Wf (" + " ".join(NAMES) + f" : List Bool) (s : {STATE_TY}) : Prop where")
for port, field, node, eqname in INPUTS:
    emit(f"  {eqname} : {node} = {field.replace('sp', 's')}")
for n in NAMES:
    if n in HELD:
        continue
    emit(f"  w_{n} : {n} <+: {rhs_of(n)}")
emit()
emit(f"def ψ (i : enT) (s : {STATE_TY}) : Prop :=")
emit("  Wf " + " ".join(projections("i")) + " s")
emit()
nprefix = len([n for n in NAMES if n not in HELD])
emit("theorem Wf.init : Wf " + " ".join(["[]"] * len(NAMES)) + " ([], [], [], []) :=")
emit("  ⟨rfl, rfl, rfl, rfl, " + ", ".join(["List.nil_prefix"] * nprefix) + "⟩")
emit()
emit("section SpecRules")
emit(f"variable (sp : {STATE_TY})")
emit()
for port, field, node, eqname in INPUTS:
    emit(f'theorem spec_in_{port} (v : List Bool) (h : {field} ⊏ v) :')
    emit(f'    (enSpec.inputs.getIO ↑"{port}").2 sp v {SPEC_STATE[port]} := by')
    emit( "  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩")
    emit()
emit('theorem spec_out_q (v : List Bool) (h : v <+: enOut sp.1 sp.2.1 sp.2.2.1 sp.2.2.2) :')
emit('    (enSpec.outputs.getIO ↑"q").2 sp v sp := by')
emit( "  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨rfl, h⟩")
emit("end SpecRules")
emit()
emit("section Cases")
emit("variable {" + " ".join(NAMES) + f" : List Bool}} {{sp : {STATE_TY}}}")
emit("  (Hψ : Wf " + " ".join(NAMES) + " sp)")
emit("include Hψ")
emit()

def emit_wf(upd, port=None):
    lines = []
    for p, f, n, e in INPUTS:
        lines.append(f"          {e} := " + ("rfl" if p == port else f"Hψ.{e}"))
    for n in NAMES:
        if n in HELD:
            continue
        lines.append(f"          w_{n} := " + upd.get(n, f"Hψ.w_{n}"))
    lines[0] = "  exact {" + lines[0][9:]
    lines[-1] += " }"
    for l in lines:
        emit(l)

for port, field, node, eqname in INPUTS:
    emit(f"theorem in_{port} (v : List Bool) (h : {node} ⊏ v) :")
    emit(f"    Wf {psi_args((node, 'v'))} {SPEC_STATE[port]} := by")
    emit(f"  have hm : {node} <+: v := h.isPrefix")
    emit_wf(dict(update_fields(node, "hm")), port)
    emit()

for k, (tgt, src) in enumerate(CONNS):
    newval = gate_expr(tgt) if tgt in GATE_OF else fields_of(src, PORTS_OF[src])[0]
    emit(f"theorem int_{k} (_h : {tgt} ⊏ {newval}) :")
    emit(f"    Wf {psi_args((tgt, newval))} sp := by")
    emit_wf(dict(update_fields(tgt, f"Hψ.w_{tgt}")))
    emit()

emit("""/-- **The nodes agree with the automaton.**  The cell's loop -- the multiplexer reading the
flip-flop it feeds -- is resolved here, by the same induction on the instant as the flip-flop's
own loops: the structural invariant says each node holds a prefix of what drives it, and that
is enough. -/""")
emit("theorem wf_sim : ∀ t,")
for idx, (rep, wire, _, _) in enumerate(REPS):
    end = " ∧" if idx < len(REPS) - 1 else " := by"
    emit(f"    (t < {rep}.length → {rep}.getD t false = (enRun sp.1 sp.2.1 sp.2.2.1 sp.2.2.2 t).{wire}){end}")
emit("  intro t")
emit("  induction t with")
emit("  | zero =>")
emit("    refine ⟨" + ", ".join(["fun hl => ?_"] * len(REPS)) + "⟩")
for rep, wire, g, args in REPS:
    zero = ("gate3Out_getD_zero" if g.startswith("gate3") else
            "gate1Out_getD_zero" if g.startswith("gate1") else "gateOut_getD_zero")
    emit(f"    · rw [Hψ.w_{rep}.getD_eq_left hl, {zero}]")
    emit( "      rfl")
emit("  | succ t ih =>")
emit("    refine ⟨" + ", ".join(["fun hl => ?_"] * len(REPS)) + "⟩")
for rep, wire, g, args in REPS:
    getd = ("gate3Out_getD" if g.startswith("gate3") else
            "gate1Out_getD" if g.startswith("gate1") else "gateOut_getD")
    lenlem = ("gate3Out_length" if g.startswith("gate3") else
              "gate1Out_length" if g.startswith("gate1") else "gateOut_length")
    holes = " ".join(["_"] * (len(args) + 1))
    emit(f"    · have l0 := Hψ.w_{rep}.length_le")
    emit(f"      simp only [{lenlem}] at l0")
    for a in args:
        if a not in GATE_OF:
            emit(f"      have l_{a} := Hψ.w_{a}.length_le")
    rws = [f"Hψ.w_{rep}.getD_eq_left hl", f"{getd} {holes} (by omega) (by omega)",
           "Nat.add_sub_cancel"]
    for a in args:
        if a in GATE_OF:
            j = REP_IDX[a]
            rws.append("ih" + ".2" * j + ("" if j == len(REPS) - 1 else ".1") + " (by omega)")
        else:
            rws.append(f"Hψ.w_{a}.getD_eq_left (by omega)")
            src = SRC[a]
            if src in HELD:
                rws.append("Hψ.e_" + {"clk": "clk", "en": "en", "data": "data",
                                      "crn": "crn"}[HELD[src]])
            else:
                j = REP_IDX[src]
                rws.append("ih" + ".2" * j + ("" if j == len(REPS) - 1 else ".1") + " (by omega)")
    emit("      rw [" + ", ".join(rws) + "]")
    emit("      rfl")
emit()
emit("""/-- What the block reports is a prefix of the specification's stream. -/""")
emit("theorem out_q :")
emit("    cut_in.take (min (min cut_r1.length cut_r2.length) (min cut_r3.length cut_r4.length) + 1)")
emit("      <+: enOut sp.1 sp.2.1 sp.2.2.1 sp.2.2.2 := by")
emit("  have h1 := Hψ.w_cut_r1.length_le")
emit("  have h2 := Hψ.w_cut_r2.length_le")
emit("  have h3 := Hψ.w_cut_r3.length_le")
emit("  have h4 := Hψ.w_cut_r4.length_le")
emit("  rw [Hψ.e_clk] at h1")
emit("  rw [Hψ.e_en] at h2")
emit("  rw [Hψ.e_data] at h3")
emit("  rw [Hψ.e_crn] at h4")
emit("  have h5 := Hψ.w_cut_in.length_le")
emit("  rw [prefix_iff_length_getD false]")
emit("  refine ⟨by simp only [List.length_take, enOut_length]; unfold enLen; omega, fun t ht => ?_⟩")
emit("  simp only [List.length_take] at ht")
emit("  rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega),")
emit("    ← List.getD_eq_getElem?_getD, enOut_getD _ _ _ _ (by unfold enLen; omega)]")
emit("  rw [Hψ.w_cut_in.getD_eq_left (by omega)]")
emit("  exact (wf_sim Hψ t).2.2.2.2.2.2.1 (by omega)")
emit()
emit("end Cases")
emit()

DES_I, DES_M, DES_C = destructure(""), destructure("m_"), destructure("c_")

emit("/-! ### The refinement -/")
emit()
for k in range(len(CONNS)):
    emit(f"theorem int_case_{k} (s : {STATE_TY}) (i mid : enT) (Hψ : ψ i s)")
    emit(f"    (Hrule : (enNetlist.internals.getD {k} (fun _ _ => False)) i mid) :")
    emit( "    ∃ s', existSR enSpec.internals s s' ∧ ψ mid s' := by")
    emit(f"  obtain {DES_I} := i")
    emit(f"  obtain {DES_M} := mid")
    emit( "  dsimp only [ψ] at Hψ ⊢")
    emit( "  have H := Hrule.1 rfl")
    emit( "  clear Hrule")
    emit(f"  obtain ⟨{DES_C}, out, Hrule⟩ := H")
    emit( "  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule")
    emit( "  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)")
    emit(f"  exact ⟨s, existSR_reflexive, int_{k} Hψ ‹_›⟩")
    emit()
emit("theorem enNetlist_internals_eq : enNetlist.internals = [" +
     ", ".join(f"enNetlist.internals.getD {k} (fun _ _ => False)" for k in range(len(CONNS))) +
     "] := rfl")
emit()
emit("theorem refines_ψ : enNetlist ⊑_{ψ} enSpec := by")
emit("  intro i s Hψ")
emit("  constructor")
emit("  · intro ident mid_i v Hrule")
emit(f"    obtain {DES_I} := i")
emit("    dsimp only [ψ] at Hψ")
emit(f"    obtain {DES_M} := mid_i")
emit("    case_transition Hcontains : Module.inputs enNetlist, ident, (PortMap.getIO_not_contained_false' Hrule)")
emit("    dsimp only [enNetlist] at Hcontains")
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
emit("    case_transition Hcontains : Module.outputs enNetlist, ident, (PortMap.getIO_not_contained_false' Hrule)")
emit("    dsimp only [enNetlist] at Hcontains")
emit("    simp at Hcontains")
emit("    subst Hcontains")
emit("    rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule")
emit("    dsimp only at Hrule")
emit("    simp only [Prod.mk.injEq, and_assoc] at Hrule")
emit("    repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)")
emit("    exact ⟨s, _, existSR_reflexive, spec_out_q s _ (out_q Hψ), Hψ⟩")
emit("  · intro rule mid_i Hin Hrule")
emit("    rw [enNetlist_internals_eq] at Hin")
emit("    simp only [List.mem_cons, List.not_mem_nil, or_false] at Hin")
emit("    rcases Hin with " + " | ".join(["h"] * len(CONNS)))
for k in range(len(CONNS)):
    emit(f"    · subst h; exact int_case_{k} s i mid_i Hψ Hrule")
emit()
emit("theorem refines_initial : Module.refines_initial enNetlist enSpec ψ := by")
emit("  intro i hi")
emit(f"  obtain {DES_I} := i")
emit("  dsimp only [enNetlist] at hi")
emit("  simp only [Prod.mk.injEq, and_assoc] at hi")
emit("  obtain ⟨" + ", ".join(["rfl"] * len(NAMES)) + "⟩ := hi")
emit("  exact ⟨([], [], [], []), rfl, Wf.init⟩")
emit()
emit("/-- **The cell's netlist refines the cell.** -/")
emit("theorem en_refines : enNetlist ⊑ enSpec :=")
emit("  ⟨inferInstance, ψ, refines_ψ, refines_initial⟩")
emit()
emit("end Graphiti.AsyncFifo.EnReg")

path = pathlib.Path("Graphiti/Projects/AsyncFifo/EnReg.lean")
src = path.read_text()
marker = "-- HEADER_END (everything below is generated by gen/gen_enreg.py)\n"
head = src.split(marker)[0]
path.write_text(head + marker + "\n" + "\n".join(L) + "\n")
print(f"wrote {path} ({len(head.splitlines()) + len(L)} lines)")
