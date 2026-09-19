#!/usr/bin/env python3
"""Generator for the proof part of `GateSync.lean`: the synchroniser stage as three settling
flip-flops.

Run from the project root:  python3 Graphiti/Projects/AsyncFifo/gen/gen_syncstage.py

Same shape as `gen_busreg.py` --- a structural invariant `Wf` (each node holds a prefix of what
drives it), one lemma per rule, and a refinement built from them.  What differs is the primitive:
a `settlingDffO` takes the oracle's two bits as well as clock and data, so the growth lemma is
`settleOut1_mono` on four streams, and the bus reaches it through a wire (`wireOf`).
"""

import pathlib

FF = ["clk", "d", "osel", "ojunk"]

# The order the lowered expression lists the nodes (= the order of `stageT`'s components).
NODES = [("pk", ["b0", "b1", "b2"]), ("unpB", ["d"]), ("clkF", ["in"]), ("unpO", ["orc"]),
         ("ff0", FF), ("ff1", FF), ("ff2", FF)]

NAMES = [f"{n}_{p}" for n, ps in NODES for p in ps]
TY = {"unpB_d": "List (BitVec 3)", "unpO_orc": "List (Orc 2)"}
BOOLS = [n for n in NAMES if n not in TY]
HELD = {"clkF_in", "unpB_d", "unpO_orc"}

STATE_TY = "List Bool × List (BitVec 3) × List (Orc 2) × List (BitVec 3)"
SPEC = "Timed.syncReg (n := 2) lat su stl"
NETLIST = "stageNetlist lat su stl"

INPUTS = [("clk", "sp.1", "clkF_in", "e_clk"),
          ("d", "sp.2.1", "unpB_d", "e_d"),
          ("orc", "sp.2.2.1", "unpO_orc", "e_orc")]
IN_TY = {"clk": "List Bool", "d": "List (BitVec 3)", "orc": "List (Orc 2)"}
SPEC_STATE = {"clk": "(v, sp.2)", "d": "(sp.1, v, sp.2.2)",
              "orc": "(sp.1, sp.2.1, v, sp.2.2.2)"}

# What `Wf` says about each stored stream: ('pre', src) copies, the rest are projections of a
# held input, and 'settle' is the flip-flop's own output.
FIELD = {}
for i in range(3):
    FIELD[f"ff{i}_clk"] = ("pre", "clkF_in")
    FIELD[f"ff{i}_d"] = ("bits", i)
    FIELD[f"ff{i}_osel"] = ("sel", i)
    FIELD[f"ff{i}_ojunk"] = ("junk", i)
    FIELD[f"pk_b{i}"] = ("settle", [f"ff{i}_clk", f"ff{i}_d", f"ff{i}_osel", f"ff{i}_ojunk"])

def rhs(n):
    k = FIELD[n]
    if k[0] == "pre":    return k[1]
    if k[0] == "bits":   return f"bitsOf {k[1]} (wireOf lat unpB_d)"
    if k[0] == "sel":    return f"selBit {k[1]} unpO_orc"
    if k[0] == "junk":   return f"junkBit {k[1]} unpO_orc"
    return "settleOut1 su stl " + " ".join(k[1])

SRCS = {"pre": lambda k: [k[1]], "bits": lambda k: ["unpB_d"], "sel": lambda k: ["unpO_orc"],
        "junk": lambda k: ["unpO_orc"], "settle": lambda k: k[1]}

MENTIONS = {n: [] for n in NAMES}
for n in NAMES:
    if n in HELD:
        continue
    for src in SRCS[FIELD[n][0]](FIELD[n]):
        MENTIONS[src].append(n)

# The connections in the order the graph declares them (= the order of the internal rules).
CONNS = ([(f"ff{i}_clk", "clkF_in") for i in range(3)] +
         [(f"ff{i}_d", f"bitsOf {i} (wireOf lat unpB_d)") for i in range(3)] +
         [(f"ff{i}_osel", f"selBit {i} unpO_orc") for i in range(3)] +
         [(f"ff{i}_ojunk", f"junkBit {i} unpO_orc") for i in range(3)] +
         [(f"pk_b{i}", rhs(f"pk_b{i}")) for i in range(3)])

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
    return ("lat su stl " + " ".join(arg(f) for f in BOOLS) + " " +
            arg("unpB_d") + " " + arg("unpO_orc") + " " + state)

def update_fields(changed, growth):
    out = []
    for f in MENTIONS[changed]:
        k = FIELD[f]
        if k[0] == "pre":
            out.append((f, f"Hψ.w_{f}.trans {growth}"))
        elif k[0] == "bits":
            out.append((f, f"Hψ.w_{f}.trans (bitsOf_mono (wireOf_mono {growth}))"))
        elif k[0] == "sel":
            out.append((f, f"Hψ.w_{f}.trans (selBit_mono {growth})"))
        elif k[0] == "junk":
            out.append((f, f"Hψ.w_{f}.trans (junkBit_mono {growth})"))
        else:
            args = " ".join((growth if a == changed else "List.prefix_rfl") for a in k[1])
            out.append((f, f"Hψ.w_{f}.trans (settleOut1_mono {args})"))
    return out

L = []
def emit(s=""):
    L.append(s)

emit("instance instMatch (lat su stl : Nat) : MatchInterface (" + NETLIST + ") (" + SPEC + ") := by")
emit("  dsimp [stageNetlist, Timed.syncReg]")
emit("  solve_match_interface")
emit()
emit("/-! ### The invariant")
emit()
emit("Each node holds a prefix of what drives it, and the packer's bits are prefixes of what")
emit("their flip-flops settle to.  `h_q` is what the stage has already reported. -/")
emit()
emit("structure Wf (lat su stl : Nat) (" + " ".join(BOOLS) + " : List Bool)")
emit(f"    (unpB_d : {TY['unpB_d']}) (unpO_orc : {TY['unpO_orc']})")
emit(f"    (s : {STATE_TY}) : Prop where")
for port, fld, node, eqname in INPUTS:
    emit(f"  {eqname} : {node} = {fld.replace('sp', 's')}")
for n in NAMES:
    if n in HELD:
        continue
    emit(f"  w_{n} : {n} <+: {rhs(n)}")
emit("  h_q : s.2.2.2 <+: pack3Out pk_b0 pk_b1 pk_b2")
emit()
proj = dict(zip(NAMES, projections("i")))
emit(f"def ψ (lat su stl : Nat) (i : stageT) (s : {STATE_TY}) : Prop :=")
emit("  Wf lat su stl " + " ".join(proj[f] for f in BOOLS) + " " +
     proj["unpB_d"] + " " + proj["unpO_orc"] + " s")
emit()
NF = len([n for n in NAMES if n not in HELD])
emit("theorem Wf.init (lat su stl : Nat) : Wf lat su stl " + " ".join(["[]"] * len(NAMES)) +
     " ([], [], [], []) :=")
emit("  ⟨rfl, rfl, rfl, " + ", ".join(["List.nil_prefix"] * (NF + 1)) + "⟩")
emit()
emit("section SpecRules")
emit(f"variable (lat su stl : Nat) (sp : {STATE_TY})")
emit()
for port, fld, node, eqname in INPUTS:
    emit(f'theorem spec_in_{port} (v : {IN_TY[port]}) (h : {fld} ⊏ v) :')
    emit(f'    (({SPEC}).inputs.getIO ↑"{port}").2 sp v {SPEC_STATE[port]} := by')
    emit( "  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩")
    emit()
emit('theorem spec_out_q (v : List (BitVec 3)) (h1 : sp.2.2.2 <+: v)')
emit('    (h2 : v <+: syncOut lat su stl sp.1 sp.2.1 sp.2.2.1) :')
emit(f'    (({SPEC}).outputs.getIO ↑"q").2 sp v (sp.1, sp.2.1, sp.2.2.1, v) := by')
emit( "  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h1, h2, rfl⟩")
emit("end SpecRules")
emit()
emit("section Cases")
emit("variable {lat su stl : Nat} {" + " ".join(BOOLS) + " : List Bool}")
emit(f"  {{unpB_d : {TY['unpB_d']}}} {{unpO_orc : {TY['unpO_orc']}}} {{sp : {STATE_TY}}}")
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

for port, fld, node, eqname in INPUTS:
    emit(f"theorem in_{port} (v : {IN_TY[port]}) (h : {node} ⊏ v) :")
    emit("    Wf " + wf_call((node, "v"), SPEC_STATE[port]) + " := by")
    emit(f"  have hm : {node} <+: v := h.isPrefix")
    emit_wf(dict(update_fields(node, "hm")), port)
    emit()

for k, (tgt, newval) in enumerate(CONNS):
    emit(f"theorem int_{k} (_h : {tgt} ⊏ {newval}) :")
    emit("    Wf " + wf_call((tgt, newval)) + " := by")
    upd = dict(update_fields(tgt, f"Hψ.w_{tgt}"))
    upd[tgt] = "List.prefix_rfl"
    if tgt.startswith("pk_b"):
        i = int(tgt[4:])
        args = " ".join(("(_h.isPrefix)" if j == i else "List.prefix_rfl") for j in range(3))
        emit_wf(upd, hq=f"Hψ.h_q.trans (pack3Out_mono {args})")
    else:
        emit_wf(upd)
    emit()

emit("/-- What the stage reports is a prefix of what `syncReg` promises.  `syncOut_pack` is the")
emit("theorem that makes this go through: the bus-level stream *is* the three bits packed, so")
emit("the claim reduces to monotonicity of one bit, three times. -/")
emit("theorem out_q : pack3Out pk_b0 pk_b1 pk_b2 <+: syncOut lat su stl sp.1 sp.2.1 sp.2.2.1 := by")
emit("  rw [syncOut_pack]")
emit("  refine pack3Out_mono ?_ ?_ ?_")
for i in range(3):
    emit(f"  · exact Hψ.w_pk_b{i}.trans (settleOut1_mono")
    emit(f"      (Hψ.w_ff{i}_clk.trans (Hψ.e_clk ▸ List.prefix_rfl))")
    emit(f"      (Hψ.w_ff{i}_d.trans (bitsOf_mono (wireOf_mono (Hψ.e_d ▸ List.prefix_rfl))))")
    emit(f"      (Hψ.w_ff{i}_osel.trans (selBit_mono (Hψ.e_orc ▸ List.prefix_rfl)))")
    emit(f"      (Hψ.w_ff{i}_ojunk.trans (junkBit_mono (Hψ.e_orc ▸ List.prefix_rfl))))")
emit()
emit("/-- What it has reported it has reported: the report is the packer's, and the packer's")
emit("inputs only grow. -/")
emit("theorem out_wf : Wf " +
     wf_call(None, "(sp.1, sp.2.1, sp.2.2.1, pack3Out pk_b0 pk_b1 pk_b2)") + " := by")
emit_wf({}, hq="List.prefix_rfl")
emit()
emit("end Cases")
emit()

DES_I, DES_M, DES_C = destructure(""), destructure("m_"), destructure("c_")
emit("/-! ### The refinement -/")
emit()
for k, (tgt, newval) in enumerate(CONNS):
    emit(f"theorem int_case_{k} (lat su stl : Nat) (s : {STATE_TY}) (i mid : stageT)")
    emit(f"    (Hψ : ψ lat su stl i s)")
    emit(f"    (Hrule : (({NETLIST}).internals.getD {k} (fun _ _ => False)) i mid) :")
    emit(f"    ∃ s', existSR ({SPEC}).internals s s' ∧ ψ lat su stl mid s' := by")
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
emit(f"theorem stageNetlist_internals_eq (lat su stl : Nat) : ({NETLIST}).internals = [" +
     ", ".join(f"({NETLIST}).internals.getD {k} (fun _ _ => False)" for k in range(len(CONNS))) +
     "] := rfl")
emit()
emit(f"theorem refines_ψ (lat su stl : Nat) : ({NETLIST}) ⊑_{{ψ lat su stl}} ({SPEC}) := by")
emit("  intro i s Hψ")
emit("  constructor")
emit("  · intro ident mid_i v Hrule")
emit(f"    obtain {DES_I} := i")
emit("    dsimp only [ψ] at Hψ")
emit(f"    obtain {DES_M} := mid_i")
emit(f"    case_transition Hcontains : Module.inputs ({NETLIST}), ident, (PortMap.getIO_not_contained_false' Hrule)")
emit("    dsimp only [stageNetlist] at Hcontains")
emit("    simp at Hcontains")
emit("    rcases Hcontains with " + " | ".join(["h"] * len(INPUTS)))
emit("    all_goals subst h")
emit("    all_goals rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule")
emit("    all_goals dsimp only at Hrule")
emit("    all_goals simp only [Prod.mk.injEq, and_assoc] at Hrule")
emit("    all_goals repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)")
emit("    all_goals first")
for port, fld, node, eqname in INPUTS:
    emit(f"      | exact ⟨_, _, spec_in_{port} lat su stl s _ (by rw [← Hψ.{eqname}]; assumption), "
         f"existSR_reflexive, in_{port} Hψ _ ‹_›⟩")
emit("  · intro ident mid_i v Hrule")
emit(f"    obtain {DES_I} := i")
emit("    dsimp only [ψ] at Hψ")
emit(f"    obtain {DES_M} := mid_i")
emit(f"    case_transition Hcontains : Module.outputs ({NETLIST}), ident, (PortMap.getIO_not_contained_false' Hrule)")
emit("    dsimp only [stageNetlist] at Hcontains")
emit("    simp at Hcontains")
emit("    subst Hcontains")
emit("    rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule")
emit("    dsimp only at Hrule")
emit("    simp only [Prod.mk.injEq, and_assoc] at Hrule")
emit("    repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)")
emit("    exact ⟨s, _, existSR_reflexive, spec_out_q lat su stl s _ Hψ.h_q (out_q Hψ), out_wf Hψ⟩")
emit("  · intro rule mid_i Hin Hrule")
emit("    rw [stageNetlist_internals_eq] at Hin")
emit("    simp only [List.mem_cons, List.not_mem_nil, or_false] at Hin")
emit("    rcases Hin with " + " | ".join(["h"] * len(CONNS)))
for k in range(len(CONNS)):
    emit(f"    · subst h; exact int_case_{k} lat su stl s i mid_i Hψ Hrule")
emit()
emit(f"theorem refines_initial (lat su stl : Nat) :")
emit(f"    Module.refines_initial ({NETLIST}) ({SPEC}) (ψ lat su stl) := by")
emit("  intro i hi")
emit(f"  obtain {DES_I} := i")
emit("  dsimp only [stageNetlist] at hi")
emit("  simp only [Prod.mk.injEq, and_assoc] at hi")
emit("  obtain ⟨" + ", ".join(["rfl"] * len(NAMES)) + "⟩ := hi")
emit("  exact ⟨([], [], [], []), rfl, Wf.init lat su stl⟩")
emit()
emit("/-- **The three settling flip-flops refine the synchroniser stage**, so `Timed.syncReg` is")
emit("no longer a primitive: it is three one-bit stages and a packer.")
emit("")
emit("What the chain *depends* on is the definition of `SyncStage.settlingDffO` --- its output is")
emit("`settleOut1`, the oracle-driven stream --- together with `SyncStage.syncOut_pack`.  That the")
emit("primitive is no stronger than a settling flip-flop is certified separately by")
emit("`SyncStage.settleOut1_settleOut` (it meets `Timed.SettleOut`) and by `SyncSettle.settle_orc`")
emit("(any three bits meeting `SettleOut` admit an oracle making them a `syncReg`).  Those two are")
emit("leaves of the development, not links in it: they justify the choice of primitive rather than")
emit("being consumed by this proof. -/")
emit("theorem stage_refines (lat su stl : Nat) : (" + NETLIST + ") ⊑ (" + SPEC + ") :=")
emit("  ⟨inferInstance, ψ lat su stl, refines_ψ lat su stl, refines_initial lat su stl⟩")
emit()
emit("end Graphiti.AsyncFifo.GateSync")

path = pathlib.Path("Graphiti/Projects/AsyncFifo/GateSync.lean")
src = path.read_text()
marker = "-- HEADER_END (everything below is generated by gen/gen_syncstage.py)\n"
head = src.split(marker)[0]
path.write_text(head + marker + "\n" + "\n".join(L) + "\n")
print(f"wrote {path} ({len(head.splitlines()) + len(L)} lines)")
