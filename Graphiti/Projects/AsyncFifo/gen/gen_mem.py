#!/usr/bin/env python3
"""Generator for the proof part of `Mem.lean` (the register file's netlist).

Run from the project root:  python3 Graphiti/Projects/AsyncFifo/gen/gen_mem.py

The same three pieces as the other netlists: a structural invariant `Wf` (each node holds a
prefix of what drives it), one lemma per rule, and a refinement built from them.  This netlist
mixes gates (the decoder) with blocks (the cells), so the growth lemmas are `gateOut_mono`,
`gate1Out_mono` and `enOut_mono` side by side.  Nothing has feedback here, so there is no
induction: the output claim composes monotonicity along the netlist.
"""

import pathlib

G1, G2, F, CELL, PK, A = ["a"], ["a", "b"], ["in"], ["clk", "en", "data", "clrn"], \
    ["q0", "q1", "q2", "q3"], ["a"]

NODES = [("en2", G2), ("en3", G2), ("pk", PK), ("dec3", G2), ("c2", CELL), ("c3", CELL),
         ("a0F", F), ("crF", F), ("na0F", F), ("a1F", F), ("dataF", F), ("weF", F),
         ("na1", G1), ("en0", G2), ("c0", CELL), ("unpA", A), ("en1", G2), ("na0", G1),
         ("dec0", G2), ("clkF", F), ("dec2", G2), ("dec1", G2), ("na1F", F), ("c1", CELL)]

def fields_of(node, ports):
    return [f"{node}_{p}" for p in ports]

NAMES = [f for node, ps in NODES for f in fields_of(node, ps)]

INPUTS = [("clk", "sp.1", "clkF_in", "e_clk"),
          ("we", "sp.2.1", "weF_in", "e_we"),
          ("addr", "sp.2.2.1", "unpA_a", "e_addr"),
          ("data", "sp.2.2.2.1", "dataF_in", "e_data"),
          ("clrn", "sp.2.2.2.2.1", "crF_in", "e_crn")]
SPEC_STATE = {"clk": "(v, sp.2)", "we": "(sp.1, v, sp.2.2)",
              "addr": "(sp.1, sp.2.1, v, sp.2.2.2)",
              "data": "(sp.1, sp.2.1, sp.2.2.1, v, sp.2.2.2.2)",
              "clrn": "(sp.1, sp.2.1, sp.2.2.1, sp.2.2.2.1, v, sp.2.2.2.2.2)"}
HELD = {"clkF_in", "weF_in", "unpA_a", "dataF_in", "crF_in"}
STATE_TY = "List Bool × List Bool × List (BitVec 2) × List Bool × List Bool × List (BitVec 2 → Bool)"

# What `Wf` says about each stored stream:
#   ('pre', source) | ('bits', k) | ('g1', arg) | ('g2', a, b) | ('cell', clk, en, data, crn)
FIELD = {
    "a0F_in": ("bits", 0), "a1F_in": ("bits", 1),
    "na0_a": ("pre", "a0F_in"), "na1_a": ("pre", "a1F_in"),
    "na0F_in": ("g1", "na0_a"), "na1F_in": ("g1", "na1_a"),
    "dec0_a": ("pre", "na0F_in"), "dec0_b": ("pre", "na1F_in"),
    "dec1_a": ("pre", "a0F_in"), "dec1_b": ("pre", "na1F_in"),
    "dec2_a": ("pre", "na0F_in"), "dec2_b": ("pre", "a1F_in"),
    "dec3_a": ("pre", "a0F_in"), "dec3_b": ("pre", "a1F_in"),
}
for i in range(4):
    FIELD[f"en{i}_a"] = ("pre", "weF_in")
    FIELD[f"en{i}_b"] = ("g2", f"dec{i}_a", f"dec{i}_b")
    FIELD[f"c{i}_clk"] = ("pre", "clkF_in")
    FIELD[f"c{i}_en"] = ("g2", f"en{i}_a", f"en{i}_b")
    FIELD[f"c{i}_data"] = ("pre", "dataF_in")
    FIELD[f"c{i}_clrn"] = ("pre", "crF_in")
    FIELD[f"pk_q{i}"] = ("cell", f"c{i}_clk", f"c{i}_en", f"c{i}_data", f"c{i}_clrn")

def rhs_of(n):
    k = FIELD[n]
    if k[0] == "pre":
        return k[1]
    if k[0] == "bits":
        return f"bitsA {k[1]} unpA_a"
    if k[0] == "g1":
        return f"gate1Out not {k[1]}"
    if k[0] == "g2":
        return f"gateOut and2 {k[1]} {k[2]}"
    return "enOut " + " ".join(k[1:])

MENTIONS = {n: [] for n in NAMES}
for n in NAMES:
    if n in HELD:
        continue
    k = FIELD[n]
    srcs = [k[1]] if k[0] == "pre" else ([] if k[0] == "bits" else list(k[1:]))
    if k[0] == "bits":
        srcs = ["unpA_a"]
    for src in srcs:
        MENTIONS[src].append(n)

# The connections in the order `memLowered` lists them: (target, source node).
CONNS = ([("a0F_in", "unpA"), ("a1F_in", "unpA"),
          ("na0_a", "a0F"), ("dec1_a", "a0F"), ("dec3_a", "a0F"),
          ("na1_a", "a1F"), ("dec2_b", "a1F"), ("dec3_b", "a1F"),
          ("na0F_in", "na0"), ("dec0_a", "na0F"), ("dec2_a", "na0F"),
          ("na1F_in", "na1"), ("dec0_b", "na1F"), ("dec1_b", "na1F")] +
         [(f"en{i}_a", "weF") for i in range(4)] +
         [(f"en{i}_b", f"dec{i}") for i in range(4)] +
         [(f"c{i}_clk", "clkF") for i in range(4)] +
         [(f"c{i}_clrn", "crF") for i in range(4)] +
         [(f"c{i}_data", "dataF") for i in range(4)] +
         [(f"c{i}_en", f"en{i}") for i in range(4)] +
         [(f"pk_q{i}", f"c{i}") for i in range(4)])

PORTS_OF = dict(NODES)

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

BOOLS = [n for n in NAMES if n != "unpA_a"]

def wf_call(subst=None, state="sp"):
    def arg(f):
        return ("(" + subst[1] + ")") if subst and f == subst[0] else f
    return " ".join(arg(f) for f in BOOLS) + " " + arg("unpA_a") + " " + state

def update_fields(changed, growth):
    out = [(changed, "List.prefix_rfl")]
    for f in MENTIONS[changed]:
        k = FIELD[f]
        if k[0] == "pre":
            out.append((f, f"Hψ.w_{f}.trans {growth}"))
        elif k[0] == "bits":
            out.append((f, f"Hψ.w_{f}.trans (bitsA_mono {growth})"))
        elif k[0] == "g1":
            out.append((f, f"Hψ.w_{f}.trans (gate1Out_mono _ {growth})"))
        elif k[0] == "g2":
            pf = " ".join((growth if a == changed else "List.prefix_rfl") for a in k[1:])
            out.append((f, f"Hψ.w_{f}.trans (gateOut_mono _ {pf})"))
        else:
            pf = " ".join((growth if a == changed else "List.prefix_rfl") for a in k[1:])
            out.append((f, f"Hψ.w_{f}.trans (enOut_mono {pf})"))
    return out

emit('''/-! ### The specification -/

/-- The register file as a single block. -/
@[drcomponents]
def memSpec : StringModule (List Bool × List Bool × List (BitVec 2) × List Bool × List Bool ×
    List (BitVec 2 → Bool)) :=
  { inputs := [ (↑"clk", ⟨List Bool, fun s v s' => s.1 ⊏ v ∧ s' = (v, s.2)⟩)
              , (↑"we", ⟨List Bool, fun s v s' => s.2.1 ⊏ v ∧ s' = (s.1, v, s.2.2)⟩)
              , (↑"addr", ⟨List (BitVec 2), fun s v s' => s.2.2.1 ⊏ v ∧
                  s' = (s.1, s.2.1, v, s.2.2.2)⟩)
              , (↑"data", ⟨List Bool, fun s v s' => s.2.2.2.1 ⊏ v ∧
                  s' = (s.1, s.2.1, s.2.2.1, v, s.2.2.2.2)⟩)
              , (↑"clrn", ⟨List Bool, fun s v s' => s.2.2.2.2.1 ⊏ v ∧
                  s' = (s.1, s.2.1, s.2.2.1, s.2.2.2.1, v, s.2.2.2.2.2)⟩) ].toAssocList
    outputs := [ (↑"mem", ⟨List (BitVec 2 → Bool), fun s v s' => s.2.2.2.2.2 <+: v ∧
                    v <+: memOut s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2.1 ∧
                    s' = (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, v)⟩) ].toAssocList
    internals := []
    init_state := fun s => s = ([], [], [], [], [], []) }

instance : MatchInterface memNetlist memSpec := by
  dsimp [memNetlist, memSpec]
  solve_match_interface

/-! ### The invariant -/
''')

emit("structure Wf (" + " ".join(BOOLS) + " : List Bool)")
emit(f"    (unpA_a : List (BitVec 2)) (s : {STATE_TY}) : Prop where")
for port, field, node, eqname in INPUTS:
    emit(f"  {eqname} : {node} = {field.replace('sp', 's')}")
for n in NAMES:
    if n in HELD:
        continue
    emit(f"  w_{n} : {n} <+: {rhs_of(n)}")
emit("  h_mem : s.2.2.2.2.2 <+: packMemOut pk_q0 pk_q1 pk_q2 pk_q3")
emit()
proj = dict(zip(NAMES, projections("i")))
emit(f"def ψ (i : memT) (s : {STATE_TY}) : Prop :=")
emit("  Wf " + " ".join(proj[f] for f in BOOLS) + " " + proj["unpA_a"] + " s")
emit()
nfields = len([n for n in NAMES if n not in HELD])
emit("theorem Wf.init : Wf " + " ".join(["[]"] * len(NAMES)) + " ([], [], [], [], [], []) :=")
emit("  ⟨rfl, rfl, rfl, rfl, rfl, " + ", ".join(["List.nil_prefix"] * (nfields + 1)) + "⟩")
emit()
emit("section SpecRules")
emit(f"variable (sp : {STATE_TY})")
emit()
for port, field, node, eqname in INPUTS:
    ty = "List (BitVec 2)" if port == "addr" else "List Bool"
    emit(f'theorem spec_in_{port} (v : {ty}) (h : {field} ⊏ v) :')
    emit(f'    (memSpec.inputs.getIO ↑"{port}").2 sp v {SPEC_STATE[port]} := by')
    emit( "  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩")
    emit()
emit('theorem spec_out_mem (v : List (BitVec 2 → Bool)) (h1 : sp.2.2.2.2.2 <+: v)')
emit('    (h2 : v <+: memOut sp.1 sp.2.1 sp.2.2.1 sp.2.2.2.1 sp.2.2.2.2.1) :')
emit('    (memSpec.outputs.getIO ↑"mem").2 sp v')
emit('      (sp.1, sp.2.1, sp.2.2.1, sp.2.2.2.1, sp.2.2.2.2.1, v) := by')
emit( "  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h1, h2, rfl⟩")
emit("end SpecRules")
emit()
emit("section Cases")
emit("variable {" + " ".join(BOOLS) + " : List Bool}")
emit(f"  {{unpA_a : List (BitVec 2)}} {{sp : {STATE_TY}}}")
emit("  (Hψ : Wf " + wf_call() + ")")
emit("include Hψ")
emit()

def emit_wf(upd, port=None, hm="Hψ.h_mem"):
    lines = []
    for p, f, n, e in INPUTS:
        lines.append(f"          {e} := " + ("rfl" if p == port else f"Hψ.{e}"))
    for n in NAMES:
        if n in HELD:
            continue
        lines.append(f"          w_{n} := " + upd.get(n, f"Hψ.w_{n}"))
    lines.append(f"          h_mem := {hm}")
    lines[0] = "  exact {" + lines[0][9:]
    lines[-1] += " }"
    for l in lines:
        emit(l)

for port, field, node, eqname in INPUTS:
    ty = "List (BitVec 2)" if port == "addr" else "List Bool"
    emit(f"theorem in_{port} (v : {ty}) (h : {node} ⊏ v) :")
    emit("    Wf " + wf_call((node, "v"), SPEC_STATE[port]) + " := by")
    emit(f"  have hm : {node} <+: v := h.isPrefix")
    emit_wf(dict(update_fields(node, "hm")), port)
    emit()

for k, (tgt, src) in enumerate(CONNS):
    kind = FIELD[tgt]
    if src.startswith("c") and src[1:].isdigit():          # a cell's output
        emit(f"theorem int_{k} {{out : List Bool}} (_h : {tgt} ⊏ out) (hout : out <+: {rhs_of(tgt)}) :")
        emit("    Wf " + wf_call((tgt, "out")) + " := by")
        upd = dict(update_fields(tgt, "(_h.isPrefix)"))
        upd[tgt] = "hout"
    else:
        newval = rhs_of(tgt) if kind[0] in ("g1", "g2", "bits") else \
            fields_of(src, PORTS_OF[src])[0]
        emit(f"theorem int_{k} (_h : {tgt} ⊏ {newval}) :")
        emit("    Wf " + wf_call((tgt, newval)) + " := by")
        upd = dict(update_fields(tgt, f"Hψ.w_{tgt}"))
    if tgt.startswith("pk_q"):
        j = int(tgt[4:])
        args = " ".join(("(_h.isPrefix)" if m == j else "List.prefix_rfl") for m in range(4))
        emit_wf(upd, hm=f"Hψ.h_mem.trans (packMemOut_mono {args})")
    else:
        emit_wf(upd)
    emit()

emit("""/-- What the file reports is a prefix of the specification's stream: every cell sees prefixes
of the block's inputs, and the decoder in front of it a prefix of the address. -/""")
emit("theorem out_mem : packMemOut pk_q0 pk_q1 pk_q2 pk_q3 <+:")
emit("    memOut sp.1 sp.2.1 sp.2.2.1 sp.2.2.2.1 sp.2.2.2.2.1 := by")
emit("  have hclk : ∀ x : List Bool, x <+: clkF_in → x <+: sp.1 := fun x h => h.trans (Hψ.e_clk ▸ List.prefix_rfl)")
emit("  have hwe : ∀ x : List Bool, x <+: weF_in → x <+: sp.2.1 := fun x h => h.trans (Hψ.e_we ▸ List.prefix_rfl)")
emit("  have hdata : ∀ x : List Bool, x <+: dataF_in → x <+: sp.2.2.2.1 := fun x h => h.trans (Hψ.e_data ▸ List.prefix_rfl)")
emit("  have hcrn : ∀ x : List Bool, x <+: crF_in → x <+: sp.2.2.2.2.1 := fun x h => h.trans (Hψ.e_crn ▸ List.prefix_rfl)")
emit("  have ha0 : a0F_in <+: bitsA 0 sp.2.2.1 := Hψ.w_a0F_in.trans (bitsA_mono (Hψ.e_addr ▸ List.prefix_rfl))")
emit("  have ha1 : a1F_in <+: bitsA 1 sp.2.2.1 := Hψ.w_a1F_in.trans (bitsA_mono (Hψ.e_addr ▸ List.prefix_rfl))")
emit("  have hn0 : na0F_in <+: gate1Out not (bitsA 0 sp.2.2.1) :=")
emit("    Hψ.w_na0F_in.trans (gate1Out_mono _ (Hψ.w_na0_a.trans ha0))")
emit("  have hn1 : na1F_in <+: gate1Out not (bitsA 1 sp.2.2.1) :=")
emit("    Hψ.w_na1F_in.trans (gate1Out_mono _ (Hψ.w_na1_a.trans ha1))")
# each decoder's two inputs, in the order the entry inverts them
DEC = {0: ("hn0", "hn1"), 1: ("ha0", "hn1"), 2: ("hn0", "ha1"), 3: ("ha0", "ha1")}
for i in range(4):
    x, y = DEC[i]
    emit(f"  have hd{i} : gateOut and2 dec{i}_a dec{i}_b <+: W_dec {i} sp.2.2.1 :=")
    emit(f"    gateOut_mono _ (Hψ.w_dec{i}_a.trans {x}) (Hψ.w_dec{i}_b.trans {y})")
    emit(f"  have he{i} : gateOut and2 en{i}_a en{i}_b <+: W_en {i} sp.2.1 sp.2.2.1 :=")
    emit(f"    gateOut_mono _ (hwe _ Hψ.w_en{i}_a) (Hψ.w_en{i}_b.trans hd{i})")
emit("  refine packMemOut_prefix ?_ ?_ ?_ ?_")
for i in range(4):
    emit(f"  · exact Hψ.w_pk_q{i}.trans (enOut_mono (hclk _ Hψ.w_c{i}_clk) (Hψ.w_c{i}_en.trans he{i})")
    emit(f"      (hdata _ Hψ.w_c{i}_data) (hcrn _ Hψ.w_c{i}_clrn))")
emit()
emit("/-- What it has reported it has reported: the report is the packer's, and the packer's")
emit("inputs only grow. -/")
emit("theorem out_wf : Wf " + wf_call(None,
  "(sp.1, sp.2.1, sp.2.2.1, sp.2.2.2.1, sp.2.2.2.2.1, packMemOut pk_q0 pk_q1 pk_q2 pk_q3)") + " := by")
emit_wf({}, hm="List.prefix_rfl")
emit()
emit("end Cases")
emit()

DES_I, DES_M, DES_C = destructure(""), destructure("m_"), destructure("c_")

emit("/-! ### The refinement -/")
emit()
for k, (tgt, src) in enumerate(CONNS):
    cell = src.startswith("c") and src[1:].isdigit()
    emit(f"theorem int_case_{k} (s : {STATE_TY}) (i mid : memT) (Hψ : ψ i s)")
    emit(f"    (Hrule : (memNetlist.internals.getD {k} (fun _ _ => False)) i mid) :")
    emit( "    ∃ s', existSR memSpec.internals s s' ∧ ψ mid s' := by")
    emit(f"  obtain {DES_I} := i")
    emit(f"  obtain {DES_M} := mid")
    emit( "  dsimp only [ψ] at Hψ ⊢")
    emit( "  have H := Hrule.1 rfl")
    emit( "  clear Hrule")
    emit(f"  obtain ⟨{DES_C}, out, Hrule⟩ := H")
    emit( "  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule")
    emit( "  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)")
    emit(f"  exact ⟨s, existSR_reflexive, int_{k} Hψ ‹_›" + (" ‹_›⟩" if cell else "⟩"))
    emit()
emit("theorem memNetlist_internals_eq : memNetlist.internals = [" +
     ", ".join(f"memNetlist.internals.getD {k} (fun _ _ => False)" for k in range(len(CONNS))) +
     "] := rfl")
emit()
emit("theorem refines_ψ : memNetlist ⊑_{ψ} memSpec := by")
emit("  intro i s Hψ")
emit("  constructor")
emit("  · intro ident mid_i v Hrule")
emit(f"    obtain {DES_I} := i")
emit("    dsimp only [ψ] at Hψ")
emit(f"    obtain {DES_M} := mid_i")
emit("    case_transition Hcontains : Module.inputs memNetlist, ident, (PortMap.getIO_not_contained_false' Hrule)")
emit("    dsimp only [memNetlist] at Hcontains")
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
emit("    case_transition Hcontains : Module.outputs memNetlist, ident, (PortMap.getIO_not_contained_false' Hrule)")
emit("    dsimp only [memNetlist] at Hcontains")
emit("    simp at Hcontains")
emit("    subst Hcontains")
emit("    rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule")
emit("    dsimp only at Hrule")
emit("    simp only [Prod.mk.injEq, and_assoc] at Hrule")
emit("    repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)")
emit("    exact ⟨s, _, existSR_reflexive, spec_out_mem s _ Hψ.h_mem (out_mem Hψ), out_wf Hψ⟩")
emit("  · intro rule mid_i Hin Hrule")
emit("    rw [memNetlist_internals_eq] at Hin")
emit("    simp only [List.mem_cons, List.not_mem_nil, or_false] at Hin")
emit("    rcases Hin with " + " | ".join(["h"] * len(CONNS)))
for k in range(len(CONNS)):
    emit(f"    · subst h; exact int_case_{k} s i mid_i Hψ Hrule")
emit()
emit("theorem refines_initial : Module.refines_initial memNetlist memSpec ψ := by")
emit("  intro i hi")
emit(f"  obtain {DES_I} := i")
emit("  dsimp only [memNetlist] at hi")
emit("  simp only [Prod.mk.injEq, and_assoc] at hi")
emit("  obtain ⟨" + ", ".join(["rfl"] * len(NAMES)) + "⟩ := hi")
emit("  exact ⟨([], [], [], [], [], []), rfl, Wf.init⟩")
emit()
emit("/-- **The decoder and the four cells refine the register file.** -/")
emit("theorem mem_refines : memNetlist ⊑ memSpec :=")
emit("  ⟨inferInstance, ψ, refines_ψ, refines_initial⟩")
emit()
emit("end Graphiti.AsyncFifo.Mem")

path = pathlib.Path("Graphiti/Projects/AsyncFifo/Mem.lean")
src = path.read_text()
marker = "-- HEADER_END (everything below is generated by gen/gen_mem.py)\n"
head = src.split(marker)[0]
path.write_text(head + marker + "\n" + "\n".join(L) + "\n")
print(f"wrote {path} ({len(head.splitlines()) + len(L)} lines)")
