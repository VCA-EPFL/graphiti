#!/usr/bin/env python3
"""Generator for the proof part of `Dff.lean` (the flip-flop with async clear).

Run from the project root:  python3 Graphiti/Projects/AsyncFifo/gen/gen_dff.py
It rewrites everything in `Dff.lean` after the `HEADER_END` marker line.

The invariant is Kobler's: a *structural* one (`Wf`), saying only that each node holds a prefix
of what drives it.  Nothing in it mentions the automaton or a horizon, so it survives a growth
of the block's inputs with no work at all.  The correspondence with the automaton (`wf_sim`) is
then derived from it by induction on the instant, once, where it is needed: at the output.
"""

import pathlib

# The nodes in the order the lowered state tuple presents them, with their arity.
NODES = [("n2", 3), ("n5f", 1), ("df", 1), ("qf", 2), ("crf", 1), ("n6", 3), ("n5", 2),
         ("n4", 3), ("n4f", 1), ("n3", 3), ("n1", 2), ("n3f", 1), ("clkf", 1), ("n2f", 1),
         ("cut", 4)]
PORTS = {1: ["in"], 2: ["a", "b"], 3: ["a", "b", "c"], 4: ["in", "r1", "r2", "r3"]}

def fields_of(node, arity):
    return [f"{node}_{p}" for p in PORTS[arity]]

NAMES = [f for node, ar in NODES for f in fields_of(node, ar)]

# The three streams that are the block's inputs, held exactly.
INPUTS = [("clk", "sp.1", "clkf_in", "e_clk"),
          ("d", "sp.2.1", "df_in", "e_d"),
          ("clrn", "sp.2.2", "crf_in", "e_crn")]
SPEC_STATE = {"clk": "(v, sp.2)", "d": "(sp.1, v, sp.2.2)", "clrn": "(sp.1, sp.2.1, v)"}

# One stream per wire carries that wire's value: the wire's single consumer.  Every other
# stream that reads the wire is a prefix of this one.
#   representative, wire, the gate that drives it, its stored inputs
REPS = [
    ("n2_a",   "n1",  "gateOut nand2",  ["n1_a", "n1_b"]),
    ("n2f_in", "n2",  "gate3Out nand3", ["n2_a", "n2_b", "n2_c"]),
    ("n3f_in", "n3",  "gate3Out nand3", ["n3_a", "n3_b", "n3_c"]),
    ("n4f_in", "n4",  "gate3Out nand3", ["n4_a", "n4_b", "n4_c"]),
    ("n5f_in", "n5",  "gateOut nand2",  ["n5_a", "n5_b"]),
    ("n5_b",   "n6",  "gate3Out nand3", ["n6_a", "n6_b", "n6_c"]),
    ("cut_in", "q",   "gateOut and2",   ["qf_a", "qf_b"]),
]
REP_OF = {wire: rep for rep, wire, _, _ in REPS}
WIRE_OF = {rep: wire for rep, wire, _, _ in REPS}
GATE_OF = {rep: (g, args) for rep, _, g, args in REPS}

# Every other stream: the stream it is a prefix of.
SRC = {
    "n1_a": "n4f_in", "n1_b": "n2f_in",
    "n2_b": "clkf_in", "n2_c": "crf_in",
    "n3_a": "n2f_in", "n3_b": "clkf_in", "n3_c": "n4f_in",
    "n4_a": "n3f_in", "n4_b": "df_in", "n4_c": "crf_in",
    "n5_a": "n2f_in",
    "n6_a": "n5f_in", "n6_b": "n3f_in", "n6_c": "crf_in",
    "qf_a": "n5f_in", "qf_b": "crf_in",
    "cut_r1": "clkf_in", "cut_r2": "df_in", "cut_r3": "crf_in",
}
HELD = {"clkf_in": "clk", "df_in": "d", "crf_in": "crn"}   # the block's own inputs

# The connections, in the order `dffLowered` lists them: (target stream, what now drives it).
CONNS = [
    ("n2_b", "clkf_in"), ("n3_b", "clkf_in"), ("cut_r1", "clkf_in"),
    ("n4_b", "df_in"), ("cut_r2", "df_in"),
    ("n2_c", "crf_in"), ("n4_c", "crf_in"), ("n6_c", "crf_in"), ("qf_b", "crf_in"),
    ("cut_r3", "crf_in"),
    ("n1_a", "n4f_in"), ("n1_b", "n2f_in"),
    ("n2_a", "GATE"), ("n2f_in", "GATE"),
    ("n3_a", "n2f_in"), ("n3_c", "n4f_in"),
    ("n3f_in", "GATE"), ("n4_a", "n3f_in"), ("n4f_in", "GATE"),
    ("n5_a", "n2f_in"), ("n5_b", "GATE"), ("n5f_in", "GATE"),
    ("n6_a", "n5f_in"), ("n6_b", "n3f_in"), ("qf_a", "n5f_in"), ("cut_in", "GATE"),
]

def gate_expr(rep):
    g, args = GATE_OF[rep]
    return f"{g} " + " ".join(args)

def rhs_of(name):
    """What `Wf` says this stream is a prefix of."""
    if name in GATE_OF:
        return gate_expr(name)
    return SRC[name]

def mono_of(rep):
    """The monotonicity lemma for the gate driving `rep`."""
    g, args = GATE_OF[rep]
    return ("gateOut_mono" if g.startswith("gateOut") else "gate3Out_mono"), args

# Which Wf fields mention a given stream on the right.
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
    for node, arity in NODES:
        fs = fields_of(node, arity)
        parts.append(prefix + fs[0] if arity == 1 else
                     "⟨" + ", ".join(prefix + f for f in fs) + "⟩")
    return "⟨" + ", ".join(parts) + "⟩"

def projections(v):
    out = []
    for k, (node, arity) in enumerate(NODES):
        base = v + ".2" * k + ("" if k == len(NODES) - 1 else ".1")
        if arity == 1:
            out.append(base)
        else:
            for j in range(arity):
                out.append(base + ".2" * j + (".1" if j < arity - 1 else ""))
    return out

def psi_args(subst=None):
    return " ".join((("(" + subst[1] + ")") if subst and f == subst[0] else f) for f in NAMES)

emit('''/-! ### The wires as the run of a six-bit automaton -/

/-- The value of the six gate outputs at one instant. -/
structure DffSt where
  n1 : Bool
  n2 : Bool
  n3 : Bool
  n4 : Bool
  n5 : Bool
  n6 : Bool
deriving DecidableEq, Repr

instance : Inhabited DffSt := ⟨⟨false, false, false, false, false, false⟩⟩

/-- Every gate recomputes from the values of the previous instant: one tick of delay each.
The input is `(clk, d, clrn)`. -/
def dffStep (s : DffSt) (i : Bool × Bool × Bool) : DffSt :=
  ⟨nand2 s.n4 s.n2, nand3 s.n1 i.1 i.2.2, nand3 s.n2 i.1 s.n4,
   nand3 s.n3 i.2.1 i.2.2, nand2 s.n2 s.n6, nand3 s.n5 s.n3 i.2.2⟩

/-- Every wire of a netlist of these gates is low before anything has propagated. -/
def DffSt.init : DffSt := ⟨false, false, false, false, false, false⟩

def dffInp (clk d crn : List Bool) (t : Nat) : Bool × Bool × Bool :=
  (clk.getD t false, d.getD t false, crn.getD t false)

def dffRun (clk d crn : List Bool) (t : Nat) : DffSt :=
  run dffStep DffSt.init (dffInp clk d crn) t

/-- How far the block's inputs are known. -/
def dffLen (clk d crn : List Bool) : Nat := min (min clk.length d.length) crn.length

theorem dffLen_le_clk (clk d crn : List Bool) : dffLen clk d crn ≤ clk.length := by
  unfold dffLen; omega

theorem dffLen_le_d (clk d crn : List Bool) : dffLen clk d crn ≤ d.length := by
  unfold dffLen; omega

theorem dffLen_le_crn (clk d crn : List Bool) : dffLen clk d crn ≤ crn.length := by
  unfold dffLen; omega

theorem dffRun_congr {clk clk' d d' crn crn' : List Bool} (hc : clk <+: clk') (hd : d <+: d')
    (hr : crn <+: crn') {t : Nat} (ht : t ≤ dffLen clk d crn) :
    dffRun clk d crn t = dffRun clk' d' crn' t := by
  refine run_congr _ _ (fun u hu => ?_) t ht
  unfold dffLen at hu
  unfold dffInp
  rw [hc.getD_eq_left (by omega), hd.getD_eq_left (by omega), hr.getD_eq_left (by omega)]

/-- The flip-flop's output at one instant: the wire `n5` one instant earlier, gated by the
clear.  The gate costs one instant of clock-to-q and buys a defined output from instant `0`
(see the header). -/
def qAt (clk d crn : List Bool) (t : Nat) : Bool :=
  match t with
  | 0 => false
  | t + 1 => and2 (dffRun clk d crn t).n5 (crn.getD t false)

/-- What the block reports: the output wire, as far as its inputs are known plus the one
instant a Moore block may report. -/
def dffOut (clk d crn : List Bool) : List Bool :=
  timeline (qAt clk d crn) (dffLen clk d crn + 1)

@[simp] theorem dffOut_length (clk d crn : List Bool) :
    (dffOut clk d crn).length = dffLen clk d crn + 1 := timeline_length _ _

theorem dffOut_getD (clk d crn : List Bool) {t : Nat} (ht : t < dffLen clk d crn + 1) :
    (dffOut clk d crn).getD t false = qAt clk d crn t := timeline_getD _ ht _

theorem dffOut_mono {clk clk' d d' crn crn' : List Bool} (hc : clk <+: clk') (hd : d <+: d')
    (hr : crn <+: crn') : dffOut clk d crn <+: dffOut clk' d' crn' := by
  have := hc.length_le; have := hd.length_le; have := hr.length_le
  apply timeline_mono (by unfold dffLen; omega)
  intro t ht
  match t with
  | 0 => rfl
  | u + 1 =>
    simp only [dffLen] at ht
    show and2 _ _ = and2 _ _
    rw [dffRun_congr hc hd hr (by unfold dffLen; omega), hr.getD_eq_left (by omega)]

/-! ### The specification -/

/-- The flip-flop as a single block: it stores its three inputs, and its output is a prefix of
the stream the automaton gives.  `DffTiming.lean` proves the register contract from this. -/
@[drcomponents]
def dffSpec : StringModule (List Bool × List Bool × List Bool) :=
  { inputs := [ (↑"clk", ⟨List Bool, fun s v s' => s.1 ⊏ v ∧ s' = (v, s.2)⟩)
              , (↑"d", ⟨List Bool, fun s v s' => s.2.1 ⊏ v ∧ s' = (s.1, v, s.2.2)⟩)
              , (↑"clrn", ⟨List Bool, fun s v s' => s.2.2 ⊏ v ∧ s' = (s.1, s.2.1, v)⟩) ].toAssocList
    outputs := [ (↑"q", ⟨List Bool, fun s v s' => s' = s ∧ v <+: dffOut s.1 s.2.1 s.2.2⟩) ].toAssocList
    internals := []
    init_state := fun s => s = ([], [], []) }

instance : MatchInterface dffNetlist dffSpec := by
  dsimp [dffNetlist, dffSpec]
  solve_match_interface

/-! ### The invariant

Every node holds a prefix of what drives it, and the three nodes fed by the block's inputs hold
exactly what the specification stores.  That is all: no instant, no horizon, no automaton -- so
a growth of the inputs costs one `trans` per field. -/
''')

emit("structure Wf (" + " ".join(NAMES) +
     " : List Bool) (s : List Bool × List Bool × List Bool) : Prop where")
for port, field, node, eqname in INPUTS:
    emit(f"  {eqname} : {node} = {field.replace('sp', 's')}")
for n in NAMES:
    if n in HELD:
        continue
    emit(f"  w_{n} : {n} <+: {rhs_of(n)}")
emit()
emit("def ψ (i : dffT) (s : List Bool × List Bool × List Bool) : Prop :=")
emit("  Wf " + " ".join(projections("i")) + " s")
emit()
nfields = len([n for n in NAMES if n not in HELD])
emit("theorem Wf.init : Wf " + " ".join(["[]"] * len(NAMES)) + " ([], [], []) :=")
emit("  ⟨rfl, rfl, rfl, " + ", ".join(["List.nil_prefix"] * nfields) + "⟩")
emit()

emit("section SpecRules")
emit("variable (sp : List Bool × List Bool × List Bool)")
emit()
for port, field, node, eqname in INPUTS:
    emit(f'theorem spec_in_{port} (v : List Bool) (h : {field} ⊏ v) :')
    emit(f'    (dffSpec.inputs.getIO ↑"{port}").2 sp v {SPEC_STATE[port]} := by')
    emit( "  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩")
    emit()
emit('theorem spec_out_q (v : List Bool) (h : v <+: dffOut sp.1 sp.2.1 sp.2.2) :')
emit('    (dffSpec.outputs.getIO ↑"q").2 sp v sp := by')
emit( "  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨rfl, h⟩")
emit("end SpecRules")
emit()
emit("section Cases")
emit("variable {" + " ".join(NAMES) + " : List Bool} {sp : List Bool × List Bool × List Bool}")
emit("  (Hψ : Wf " + " ".join(NAMES) + " sp)")
emit("include Hψ")
emit()

def update_fields(changed, growth, newval):
    """The `Wf` fields that change when `changed` is replaced by `newval`.
    `growth` proves `changed <+: newval`."""
    out = [(changed, "List.prefix_rfl")]
    for f in MENTIONS[changed]:
        if f in GATE_OF:
            mono, args = mono_of(f)
            pf = " ".join((growth if a == changed else "List.prefix_rfl") for a in args)
            out.append((f, f"Hψ.w_{f}.trans ({mono} _ {pf})"))
        else:
            out.append((f, f"Hψ.w_{f}.trans {growth}"))
    return out

# The three input rules.
for port, field, node, eqname in INPUTS:
    emit(f"theorem in_{port} (v : List Bool) (h : {node} ⊏ v) :")
    emit(f"    Wf {psi_args((node, 'v'))} {SPEC_STATE[port]} := by")
    emit(f"  have hm : {node} <+: v := h.isPrefix")
    lines = []
    for p, f, n, e in INPUTS:
        lines.append(f"          {e} := " + ("rfl" if p == port else f"Hψ.{e}"))
    upd = dict(update_fields(node, "hm", "v"))
    for n in NAMES:
        if n in HELD:
            continue
        lines.append(f"          w_{n} := " + upd.get(n, f"Hψ.w_{n}"))
    lines[0] = "  exact {" + lines[0][9:]
    lines[-1] += " }"
    for l in lines:
        emit(l)
    emit()

# The internal rules.
for k, (tgt, src) in enumerate(CONNS):
    newval = gate_expr(tgt) if src == "GATE" else src
    emit(f"theorem int_{k} (_h : {tgt} ⊏ {newval}) :")
    emit(f"    Wf {psi_args((tgt, newval))} sp := by")
    upd = dict(update_fields(tgt, f"Hψ.w_{tgt}", newval))
    lines = []
    for p, f, n, e in INPUTS:
        lines.append(f"          {e} := Hψ.{e}")
    for n in NAMES:
        if n in HELD:
            continue
        lines.append(f"          w_{n} := " + upd.get(n, f"Hψ.w_{n}"))
    lines[0] = "  exact {" + lines[0][9:]
    lines[-1] += " }"
    for l in lines:
        emit(l)
    emit()

emit("""/-- **The nodes agree with the automaton.**  This is where the netlist's feedback is
resolved: the structural invariant says only that each node holds a prefix of what drives it,
and one induction on the instant turns that into the values of the run.  Nothing here needs a
horizon -- a node only ever holds values its own inputs justify. -/""")
emit("theorem wf_sim : ∀ t,")
for idx, (rep, wire, _, _) in enumerate(REPS):
    rhs = (f"(dffRun sp.1 sp.2.1 sp.2.2 t).{wire}" if wire != "q"
           else "qAt sp.1 sp.2.1 sp.2.2 t")
    end = " ∧" if idx < len(REPS) - 1 else " := by"
    emit(f"    (t < {rep}.length → {rep}.getD t false = {rhs}){end}")
emit("  intro t")
emit("  induction t with")
emit("  | zero =>")
emit("    refine ⟨" + ", ".join(["fun hl => ?_"] * len(REPS)) + "⟩")
for rep, wire, g, args in REPS:
    zero = "gateOut_getD_zero" if g.startswith("gateOut") else "gate3Out_getD_zero"
    emit(f"    · rw [Hψ.w_{rep}.getD_eq_left hl, {zero}]")
    emit( "      rfl")
emit("  | succ t ih =>")
emit("    refine ⟨" + ", ".join(["fun hl => ?_"] * len(REPS)) + "⟩")
for idx, (rep, wire, g, args) in enumerate(REPS):
    getd = "gateOut_getD" if g.startswith("gateOut") else "gate3Out_getD"
    holes = " ".join(["_"] * (len(args) + 1))
    emit(f"    · have l0 := Hψ.w_{rep}.length_le")
    emit(f"      simp only [{'gateOut_length' if g.startswith('gateOut') else 'gate3Out_length'}] at l0")
    for a in args:
        if a not in GATE_OF:
            emit(f"      have l_{a} := Hψ.w_{a}.length_le")
    rws = [f"Hψ.w_{rep}.getD_eq_left hl", f"{getd} {holes} (by omega) (by omega)",
           "Nat.add_sub_cancel"]
    for a in args:
        if a in GATE_OF:                      # the driving wire's own representative
            j = [r for r, _, _, _ in REPS].index(a)
            rws.append("ih" + ".2" * j + ("" if j == len(REPS) - 1 else ".1") + " (by omega)")
        else:
            rws.append(f"Hψ.w_{a}.getD_eq_left (by omega)")
            src = SRC[a]
            if src in HELD:
                rws.append("Hψ.e_" + {"clk": "clk", "d": "d", "crn": "crn"}[HELD[src]])
            else:
                j = [r for r, _, _, _ in REPS].index(src)
                rws.append("ih" + ".2" * j + ("" if j == len(REPS) - 1 else ".1") + " (by omega)")
    emit("      rw [" + ", ".join(rws) + "]")
    emit("      rfl")
emit()
emit("""/-- What the block reports is a prefix of what the specification says: the values agree
by `wf_sim`, and the length is what `cut3` allows. -/""")
emit("theorem out_q :")
emit("    cut_in.take (min (min cut_r1.length cut_r2.length) cut_r3.length + 1) <+:")
emit("      dffOut sp.1 sp.2.1 sp.2.2 := by")
emit("  have h1 := Hψ.w_cut_r1.length_le")
emit("  have h2 := Hψ.w_cut_r2.length_le")
emit("  have h3 := Hψ.w_cut_r3.length_le")
emit("  rw [Hψ.e_clk] at h1")
emit("  rw [Hψ.e_d] at h2")
emit("  rw [Hψ.e_crn] at h3")
emit("  rw [prefix_iff_length_getD false]")
emit("  refine ⟨by simp only [List.length_take, dffOut_length]; unfold dffLen; omega, fun t ht => ?_⟩")
emit("  simp only [List.length_take] at ht")
emit("  rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega),")
emit("    ← List.getD_eq_getElem?_getD, dffOut_getD _ _ _ (by unfold dffLen; omega)]")
emit("  exact (wf_sim Hψ t).2.2.2.2.2.2 (by omega)")
emit()
emit("end Cases")
emit()

DES_I, DES_M, DES_C = destructure(""), destructure("m_"), destructure("c_")

emit("""/-! ### The refinement

One lemma per internal rule: a single tactic block over all of them would have to carry the
whole state through `subst`, which is what made the write domain's netlist blow up. -/
""")
for k in range(len(CONNS)):
    emit(f"theorem int_case_{k} (s : List Bool × List Bool × List Bool) (i mid : dffT) (Hψ : ψ i s)")
    emit(f"    (Hrule : (dffNetlist.internals.getD {k} (fun _ _ => False)) i mid) :")
    emit( "    ∃ s', existSR dffSpec.internals s s' ∧ ψ mid s' := by")
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

emit("theorem dffNetlist_internals_eq : dffNetlist.internals = [" +
     ", ".join(f"dffNetlist.internals.getD {k} (fun _ _ => False)" for k in range(len(CONNS))) +
     "] := rfl")
emit()
emit("theorem refines_ψ : dffNetlist ⊑_{ψ} dffSpec := by")
emit("  intro i s Hψ")
emit("  constructor")
emit("  · intro ident mid_i v Hrule")
emit(f"    obtain {DES_I} := i")
emit("    dsimp only [ψ] at Hψ")
emit(f"    obtain {DES_M} := mid_i")
emit("    case_transition Hcontains : Module.inputs dffNetlist, ident, (PortMap.getIO_not_contained_false' Hrule)")
emit("    dsimp only [dffNetlist] at Hcontains")
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
emit("    case_transition Hcontains : Module.outputs dffNetlist, ident, (PortMap.getIO_not_contained_false' Hrule)")
emit("    dsimp only [dffNetlist] at Hcontains")
emit("    simp at Hcontains")
emit("    subst Hcontains")
emit("    rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule")
emit("    dsimp only at Hrule")
emit("    simp only [Prod.mk.injEq, and_assoc] at Hrule")
emit("    repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)")
emit("    exact ⟨s, _, existSR_reflexive, spec_out_q s _ (out_q Hψ), Hψ⟩")
emit("  · intro rule mid_i Hin Hrule")
emit("    rw [dffNetlist_internals_eq] at Hin")
emit("    simp only [List.mem_cons, List.not_mem_nil, or_false] at Hin")
emit("    rcases Hin with " + " | ".join(["h"] * len(CONNS)))
for k in range(len(CONNS)):
    emit(f"    · subst h; exact int_case_{k} s i mid_i Hψ Hrule")
emit()
emit("theorem refines_initial : Module.refines_initial dffNetlist dffSpec ψ := by")
emit("  intro i hi")
emit(f"  obtain {DES_I} := i")
emit("  dsimp only [dffNetlist] at hi")
emit("  simp only [Prod.mk.injEq, and_assoc] at hi")
emit("  obtain ⟨" + ", ".join(["rfl"] * len(NAMES)) + "⟩ := hi")
emit("  exact ⟨([], [], []), rfl, Wf.init⟩")
emit()
emit("/-- **The netlist refines the flip-flop block.** -/")
emit("theorem dff_refines : dffNetlist ⊑ dffSpec :=")
emit("  ⟨inferInstance, ψ, refines_ψ, refines_initial⟩")
emit()
emit("end Graphiti.AsyncFifo.Dff")

path = pathlib.Path("Graphiti/Projects/AsyncFifo/Dff.lean")
src = path.read_text()
marker = "-- HEADER_END (everything below is generated by gen/gen_dff.py)\n"
head = src.split(marker)[0]
path.write_text(head + marker + "\n" + "\n".join(L) + "\n")
print(f"wrote {path} ({len(head.splitlines()) + len(L)} lines)")
