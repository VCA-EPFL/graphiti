#!/usr/bin/env python3
"""Generator for the proof part of `ReadMux.lean` (the read port's netlist).

Run from the project root:  python3 Graphiti/Projects/AsyncFifo/gen/gen_readmux.py

`gen_mem.py`'s shape: a structural invariant `Wf` (each node holds a prefix of what drives it),
one lemma per rule, and a refinement built from them.  Nothing here has feedback, so the output
claim is monotonicity composed along the netlist.
"""

import pathlib

G1, G2, F, UN, CUT = ["a"], ["a", "b"], ["in"], ["st", "mem"], ["in", "r1", "r2"]

# The order the lowered expression lists the nodes: the reverse of `muxGraph.1.modules`.
NODES = [("o23", G2), ("outg", G2), ("s0", G2), ("s2", G2), ("s3", G2), ("fn1", F), ("na1", G1),
         ("unpRD", UN), ("g1", G2), ("fn0", F), ("fa0", F), ("g2", G2), ("na0", G1), ("fa1", F),
         ("o01", G2), ("g3", G2), ("cut", CUT), ("g0", G2), ("s1", G2)]

def fields_of(node, ports):
    return [f"{node}_{p}" for p in ports]

NAMES = [f for node, ps in NODES for f in fields_of(node, ps)]
PORTS_OF = dict(NODES)

INPUTS = [("st", "sp.1", "unpRD_st", "e_st"), ("mem", "sp.2.1", "unpRD_mem", "e_mem")]
SPEC_STATE = {"st": "(v, sp.2)", "mem": "(sp.1, v, sp.2.2)"}
HELD = {"unpRD_st", "unpRD_mem"}
STATE_TY = "List (RSt 2) × List (BitVec 2 → Bool) × List Bool"
TY = {"unpRD_st": "List (RSt 2)", "unpRD_mem": "List (BitVec 2 → Bool)"}

# ('pre', src) | ('adr', i) | ('ent', i) | ('g1', a) | ('and', a, b) | ('or', a, b)
FIELD = {
    "fa0_in": ("adr", 0), "fa1_in": ("adr", 1),
    "cut_r1": ("adr", 0), "cut_r2": ("ent", 0),
    "na0_a": ("pre", "fa0_in"), "na1_a": ("pre", "fa1_in"),
    "fn0_in": ("g1", "na0_a"), "fn1_in": ("g1", "na1_a"),
    "s0_a": ("pre", "fn0_in"), "s0_b": ("pre", "fn1_in"),
    "s1_a": ("pre", "fa0_in"), "s1_b": ("pre", "fn1_in"),
    "s2_a": ("pre", "fn0_in"), "s2_b": ("pre", "fa1_in"),
    "s3_a": ("pre", "fa0_in"), "s3_b": ("pre", "fa1_in"),
    "o01_a": ("and", "g0_a", "g0_b"), "o01_b": ("and", "g1_a", "g1_b"),
    "o23_a": ("and", "g2_a", "g2_b"), "o23_b": ("and", "g3_a", "g3_b"),
    "outg_a": ("or", "o01_a", "o01_b"), "outg_b": ("or", "o23_a", "o23_b"),
    "cut_in": ("or", "outg_a", "outg_b"),
}
for i in range(4):
    FIELD[f"g{i}_a"] = ("and", f"s{i}_a", f"s{i}_b")
    FIELD[f"g{i}_b"] = ("ent", i)

def rhs_of(n):
    k = FIELD[n]
    if k[0] == "pre":   return k[1]
    if k[0] == "adr":   return f"addrBit {k[1]} unpRD_st"
    if k[0] == "ent":   return f"entry {k[1]}#2 unpRD_mem"
    if k[0] == "g1":    return f"gate1Out not {k[1]}"
    if k[0] == "and":   return f"gateOut Bool.and {k[1]} {k[2]}"
    return f"gateOut Bool.or {k[1]} {k[2]}"

MENTIONS = {n: [] for n in NAMES}
for n in NAMES:
    if n in HELD:
        continue
    k = FIELD[n]
    if k[0] == "pre":   srcs = [k[1]]
    elif k[0] == "adr": srcs = ["unpRD_st"]
    elif k[0] == "ent": srcs = ["unpRD_mem"]
    elif k[0] == "g1":  srcs = [k[1]]
    else:               srcs = [k[1], k[2]]
    for src in srcs:
        MENTIONS[src].append(n)

# The connections in the order the graph declares them (= the order of the internal rules).
CONNS = [("fa0_in", "unpRD"), ("fa1_in", "unpRD"), ("cut_r1", "unpRD"), ("cut_r2", "unpRD"),
         ("na0_a", "fa0"), ("na1_a", "fa1"), ("fn0_in", "na0"), ("fn1_in", "na1"),
         ("s0_a", "fn0"), ("s0_b", "fn1"), ("s1_a", "fa0"), ("s1_b", "fn1"),
         ("s2_a", "fn0"), ("s2_b", "fa1"), ("s3_a", "fa0"), ("s3_b", "fa1"),
         ("g0_a", "s0"), ("g0_b", "unpRD"), ("g1_a", "s1"), ("g1_b", "unpRD"),
         ("g2_a", "s2"), ("g2_b", "unpRD"), ("g3_a", "s3"), ("g3_b", "unpRD"),
         ("o01_a", "g0"), ("o01_b", "g1"), ("o23_a", "g2"), ("o23_b", "g3"),
         ("outg_a", "o01"), ("outg_b", "o23"), ("cut_in", "outg")]

BOOLS = [n for n in NAMES if n not in TY]

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

def wf_call(subst=None, state="sp"):
    def arg(f):
        return ("(" + subst[1] + ")") if subst and f == subst[0] else f
    return " ".join(arg(f) for f in BOOLS) + " " + arg("unpRD_st") + " " + arg("unpRD_mem") + " " + state

def update_fields(changed, growth):
    out = [(changed, "List.prefix_rfl")]
    for f in MENTIONS[changed]:
        k = FIELD[f]
        if k[0] == "pre":
            out.append((f, f"Hψ.w_{f}.trans {growth}"))
        elif k[0] == "adr":
            out.append((f, f"Hψ.w_{f}.trans (addrBit_mono {growth})"))
        elif k[0] == "ent":
            out.append((f, f"Hψ.w_{f}.trans (entry_mono {growth})"))
        elif k[0] == "g1":
            out.append((f, f"Hψ.w_{f}.trans (gate1Out_mono _ {growth})"))
        else:
            pf = " ".join((growth if a == changed else "List.prefix_rfl") for a in k[1:])
            out.append((f, f"Hψ.w_{f}.trans (gateOut_mono _ {pf})"))
    return out

emit('''/-! ### The specification -/

/-- The read port as a single block: what the eleven gates compute, cut at the block's own
inputs. -/
@[drcomponents]
def readMuxSpec : StringModule (List (RSt 2) × List (BitVec 2 → Bool) × List Bool) :=
  { inputs := [ (↑"st", ⟨List (RSt 2), fun s v s' => s.1 ⊏ v ∧ s' = (v, s.2)⟩)
              , (↑"mem", ⟨List (BitVec 2 → Bool), fun s v s' => s.2.1 ⊏ v ∧
                  s' = (s.1, v, s.2.2)⟩) ].toAssocList
    outputs := [ (↑"q", ⟨List Bool, fun s v s' => s.2.2 <+: v ∧ v <+: muxOut s.1 s.2.1 ∧
                    s' = (s.1, s.2.1, v)⟩) ].toAssocList
    internals := []
    init_state := fun s => s = ([], [], []) }

instance : MatchInterface muxNetlist readMuxSpec := by
  dsimp [muxNetlist, readMuxSpec]
  solve_match_interface

/-! ### The invariant -/
''')

emit("structure Wf (" + " ".join(BOOLS) + " : List Bool)")
emit(f"    (unpRD_st : List (RSt 2)) (unpRD_mem : List (BitVec 2 → Bool))")
emit(f"    (s : {STATE_TY}) : Prop where")
for port, field, node, eqname in INPUTS:
    emit(f"  {eqname} : {node} = {field.replace('sp', 's')}")
for n in NAMES:
    if n in HELD:
        continue
    emit(f"  w_{n} : {n} <+: {rhs_of(n)}")
emit("  h_q : s.2.2 <+: cutOut cut_in cut_r1 cut_r2")
emit()
proj = dict(zip(NAMES, projections("i")))
emit(f"def ψ (i : muxT) (s : {STATE_TY}) : Prop :=")
emit("  Wf " + " ".join(proj[f] for f in BOOLS) + " " + proj["unpRD_st"] + " " + proj["unpRD_mem"] + " s")
emit()
nfields = len([n for n in NAMES if n not in HELD])
emit("theorem Wf.init : Wf " + " ".join(["[]"] * len(NAMES)) + " ([], [], []) :=")
emit("  ⟨rfl, rfl, " + ", ".join(["List.nil_prefix"] * (nfields + 1)) + "⟩")
emit()
emit("section SpecRules")
emit(f"variable (sp : {STATE_TY})")
emit()
for port, field, node, eqname in INPUTS:
    emit(f'theorem spec_in_{port} (v : {TY[node]}) (h : {field} ⊏ v) :')
    emit(f'    (readMuxSpec.inputs.getIO ↑"{port}").2 sp v {SPEC_STATE[port]} := by')
    emit( "  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩")
    emit()
emit('theorem spec_out_q (v : List Bool) (h1 : sp.2.2 <+: v) (h2 : v <+: muxOut sp.1 sp.2.1) :')
emit('    (readMuxSpec.outputs.getIO ↑"q").2 sp v (sp.1, sp.2.1, v) := by')
emit( "  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h1, h2, rfl⟩")
emit("end SpecRules")
emit()
emit("section Cases")
emit("variable {" + " ".join(BOOLS) + " : List Bool}")
emit(f"  {{unpRD_st : List (RSt 2)}} {{unpRD_mem : List (BitVec 2 → Bool)}} {{sp : {STATE_TY}}}")
emit("  (Hψ : Wf " + wf_call() + ")")
emit("include Hψ")
emit()

def emit_wf(upd, port=None, hq="Hψ.h_q"):
    lines = []
    for p, f, n, e in INPUTS:
        lines.append(f"          {e} := " + ("rfl" if p == port else f"Hψ.{e}"))
    for n in NAMES:
        if n in HELD:
            continue
        lines.append(f"          w_{n} := " + upd.get(n, f"Hψ.w_{n}"))
    lines.append(f"          h_q := {hq}")
    lines[0] = "  exact {" + lines[0][9:]
    lines[-1] += " }"
    for l in lines:
        emit(l)

for port, field, node, eqname in INPUTS:
    emit(f"theorem in_{port} (v : {TY[node]}) (h : {node} ⊏ v) :")
    emit("    Wf " + wf_call((node, "v"), SPEC_STATE[port]) + " := by")
    emit(f"  have hm : {node} <+: v := h.isPrefix")
    emit_wf(dict(update_fields(node, "hm")), port)
    emit()

CUTPOS = {"cut_in": 0, "cut_r1": 1, "cut_r2": 2}
for k, (tgt, src) in enumerate(CONNS):
    kind = FIELD[tgt]
    newval = rhs_of(tgt) if kind[0] != "pre" else fields_of(src, PORTS_OF[src])[0]
    emit(f"theorem int_{k} (_h : {tgt} ⊏ {newval}) :")
    emit("    Wf " + wf_call((tgt, newval)) + " := by")
    upd = dict(update_fields(tgt, f"Hψ.w_{tgt}"))
    if tgt in CUTPOS:
        args = " ".join(("(_h.isPrefix)" if j == CUTPOS[tgt] else "List.prefix_rfl") for j in range(3))
        emit_wf(upd, hq=f"Hψ.h_q.trans (cutOut_mono {args})")
    else:
        emit_wf(upd)
    emit()

emit('''/-- What the port reports is a prefix of what the netlist computes from the block's own
inputs: monotonicity, composed along the netlist. -/''')
emit("theorem out_q : cutOut cut_in cut_r1 cut_r2 <+: muxOut sp.1 sp.2.1 := by")
emit("  have ha0 : fa0_in <+: addrBit 0 sp.1 :=")
emit("    Hψ.w_fa0_in.trans (addrBit_mono (Hψ.e_st ▸ List.prefix_rfl))")
emit("  have ha1 : fa1_in <+: addrBit 1 sp.1 :=")
emit("    Hψ.w_fa1_in.trans (addrBit_mono (Hψ.e_st ▸ List.prefix_rfl))")
emit("  have hn0 : fn0_in <+: na 0 sp.1 :=")
emit("    Hψ.w_fn0_in.trans (gate1Out_mono _ (Hψ.w_na0_a.trans ha0))")
emit("  have hn1 : fn1_in <+: na 1 sp.1 :=")
emit("    Hψ.w_fn1_in.trans (gate1Out_mono _ (Hψ.w_na1_a.trans ha1))")
SELS = [("s0", "hn0", "hn1"), ("s1", "ha0", "hn1"), ("s2", "hn0", "ha1"), ("s3", "ha0", "ha1")]
for nm, x, y in SELS:
    emit(f"  have h{nm} : gateOut Bool.and {nm}_a {nm}_b <+: sel{nm[1]} sp.1 :=")
    emit(f"    gateOut_mono _ (Hψ.w_{nm}_a.trans {x}) (Hψ.w_{nm}_b.trans {y})")
for i in range(4):
    emit(f"  have hm{i} : g{i}_b <+: entry {i}#2 sp.2.1 :=")
    emit(f"    Hψ.w_g{i}_b.trans (entry_mono (Hψ.e_mem ▸ List.prefix_rfl))")
    emit(f"  have hg{i} : gateOut Bool.and g{i}_a g{i}_b <+: gd{i} sp.1 sp.2.1 :=")
    emit(f"    gateOut_mono _ (Hψ.w_g{i}_a.trans hs{i}) hm{i}")
emit("  have ho01 : gateOut Bool.or o01_a o01_b <+: or01 sp.1 sp.2.1 :=")
emit("    gateOut_mono _ (Hψ.w_o01_a.trans hg0) (Hψ.w_o01_b.trans hg1)")
emit("  have ho23 : gateOut Bool.or o23_a o23_b <+: or23 sp.1 sp.2.1 :=")
emit("    gateOut_mono _ (Hψ.w_o23_a.trans hg2) (Hψ.w_o23_b.trans hg3)")
emit("  have hw : gateOut Bool.or outg_a outg_b <+: muxWire sp.1 sp.2.1 :=")
emit("    gateOut_mono _ (Hψ.w_outg_a.trans ho01) (Hψ.w_outg_b.trans ho23)")
emit("  exact cutOut_mono (Hψ.w_cut_in.trans hw)")
emit("    (Hψ.w_cut_r1.trans (addrBit_mono (Hψ.e_st ▸ List.prefix_rfl)))")
emit("    (Hψ.w_cut_r2.trans (entry_mono (Hψ.e_mem ▸ List.prefix_rfl)))")
emit()
emit("/-- What it has reported it has reported: the report is the cut's, and the cut only grows. -/")
emit("theorem out_wf : Wf " + wf_call(None, "(sp.1, sp.2.1, cutOut cut_in cut_r1 cut_r2)") + " := by")
emit_wf({}, hq="List.prefix_rfl")
emit()
emit("end Cases")
emit()

DES_I, DES_M, DES_C = destructure(""), destructure("m_"), destructure("c_")

emit("/-! ### The refinement -/")
emit()
for k, (tgt, src) in enumerate(CONNS):
    emit(f"theorem int_case_{k} (s : {STATE_TY}) (i mid : muxT) (Hψ : ψ i s)")
    emit(f"    (Hrule : (muxNetlist.internals.getD {k} (fun _ _ => False)) i mid) :")
    emit( "    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by")
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
emit("theorem muxNetlist_internals_eq : muxNetlist.internals = [" +
     ", ".join(f"muxNetlist.internals.getD {k} (fun _ _ => False)" for k in range(len(CONNS))) +
     "] := rfl")
emit()
emit("theorem refines_ψ : muxNetlist ⊑_{ψ} readMuxSpec := by")
emit("  intro i s Hψ")
emit("  constructor")
emit("  · intro ident mid_i v Hrule")
emit(f"    obtain {DES_I} := i")
emit("    dsimp only [ψ] at Hψ")
emit(f"    obtain {DES_M} := mid_i")
emit("    case_transition Hcontains : Module.inputs muxNetlist, ident, (PortMap.getIO_not_contained_false' Hrule)")
emit("    dsimp only [muxNetlist] at Hcontains")
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
emit("    case_transition Hcontains : Module.outputs muxNetlist, ident, (PortMap.getIO_not_contained_false' Hrule)")
emit("    dsimp only [muxNetlist] at Hcontains")
emit("    simp at Hcontains")
emit("    subst Hcontains")
emit("    rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule")
emit("    dsimp only at Hrule")
emit("    simp only [Prod.mk.injEq, and_assoc] at Hrule")
emit("    repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)")
emit("    exact ⟨s, _, existSR_reflexive, spec_out_q s _ Hψ.h_q (out_q Hψ), out_wf Hψ⟩")
emit("  · intro rule mid_i Hin Hrule")
emit("    rw [muxNetlist_internals_eq] at Hin")
emit("    simp only [List.mem_cons, List.not_mem_nil, or_false] at Hin")
emit("    rcases Hin with " + " | ".join(["h"] * len(CONNS)))
for k in range(len(CONNS)):
    emit(f"    · subst h; exact int_case_{k} s i mid_i Hψ Hrule")
emit()
emit("theorem refines_initial : Module.refines_initial muxNetlist readMuxSpec ψ := by")
emit("  intro i hi")
emit(f"  obtain {DES_I} := i")
emit("  dsimp only [muxNetlist] at hi")
emit("  simp only [Prod.mk.injEq, and_assoc] at hi")
emit("  obtain ⟨" + ", ".join(["rfl"] * len(NAMES)) + "⟩ := hi")
emit("  exact ⟨([], [], []), rfl, Wf.init⟩")
emit()
emit("/-- **The eleven gates refine the read port.** -/")
emit("theorem mux_refines : muxNetlist ⊑ readMuxSpec :=")
emit("  ⟨inferInstance, ψ, refines_ψ, refines_initial⟩")
emit()
emit("end Graphiti.AsyncFifo.ReadMux")

path = pathlib.Path("Graphiti/Projects/AsyncFifo/ReadMux.lean")
src = path.read_text()
marker = "-- HEADER_END (everything below is generated by gen/gen_readmux.py)\n"
head = src.split(marker)[0]
path.write_text(head + marker + "\n" + "\n".join(L) + "\n")
print(f"wrote {path} ({len(head.splitlines()) + len(L)} lines)")
