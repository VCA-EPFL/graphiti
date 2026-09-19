#!/usr/bin/env python3
"""Generator for the proof part of `BusReg.lean` and `StReg.lean`: a bank of flip-flops
holding a bus, one flip-flop per bit.

Run from the project root:  python3 Graphiti/Projects/AsyncFifo/gen/gen_busreg.py

Same shape as `gen_dff.py`: a structural invariant (`Wf`, each node holds a prefix of what
drives it), one lemma per rule, and a refinement built from them.  What a node is driven by is
now a *block* output rather than a gate, so the growth lemma is `dffOut_mono`.  The two
registers differ only in their width and in the bus they carry, so they share this table.
"""

import pathlib

FF = ["clk", "d", "clrn"]

CONFIGS = [
  dict(file="BusReg.lean", ns="BusReg", bits=3, bus="List (BitVec 3)", pack="pack3Out",
       T="busT", netlist="busNetlist", spec="busSpec", out="busOut", dflt="0#3",
       doc="three-bit register",
       nodes=[("pk", ["b0", "b1", "b2"]), ("unp", ["d"]), ("crF", ["in"]), ("clkF", ["in"]),
              ("ff0", FF), ("ff1", FF), ("ff2", FF)]),
  dict(file="StReg.lean", ns="StReg", bits=7, bus="List (WSt 2)", pack="packStOut",
       T="stT", netlist="stNetlist", spec="stSpec", out="stOut", dflt="default",
       doc="seven-bit state register",
       nodes=[("pk", [f"b{i}" for i in range(7)]), ("ff6", FF), ("unp", ["d"]), ("crF", ["in"]),
              ("ff5", FF), ("clkF", ["in"]), ("ff3", FF), ("ff4", FF), ("ff0", FF), ("ff1", FF),
              ("ff2", FF)]),
  dict(file="StRegR.lean", ns="StRegR", bits=7, bus="List (RSt 2)", pack="packStOut",
       T="stT", netlist="stNetlist", spec="stSpec", out="stOut", dflt="default",
       doc="seven-bit state register of the read domain",
       nodes=[("pk", [f"b{i}" for i in range(7)]), ("ff6", FF), ("unp", ["d"]), ("crF", ["in"]),
              ("ff5", FF), ("clkF", ["in"]), ("ff3", FF), ("ff4", FF), ("ff0", FF), ("ff1", FF),
              ("ff2", FF)]),
]

SPEC_STATE = {"clk": "(v, sp.2)", "d": "(sp.1, v, sp.2.2)", "clrn": "(sp.1, sp.2.1, v, sp.2.2.2)"}
INPUTS = [("clk", "sp.1", "clkF_in", "e_clk"),
          ("d", "sp.2.1", "unp_d", "e_d"),
          ("clrn", "sp.2.2.1", "crF_in", "e_crn")]
HELD = {"clkF_in", "unp_d", "crF_in"}


def generate(cfg):
    nodes, w = cfg["nodes"], cfg["bits"]
    names = [f"{n}_{p}" for n, ps in nodes for p in ps]
    bools = [n for n in names if n != "unp_d"]
    state_ty = f"List Bool × {cfg['bus']} × List Bool × {cfg['bus']}"

    # What `Wf` says about each stored stream.
    field = {}
    for i in range(w):
        field[f"ff{i}_clk"] = ("pre", "clkF_in", False)
        field[f"ff{i}_d"] = ("pre", "unp_d", True)
        field[f"ff{i}_clrn"] = ("pre", "crF_in", False)
        field[f"pk_b{i}"] = ("dff", [f"ff{i}_clk", f"ff{i}_d", f"ff{i}_clrn"])

    def rhs(name):
        k = field[name]
        if k[0] == "pre":
            return f"bitsOf {name[2]} {k[1]}" if k[2] else k[1]
        return "dffOut " + " ".join(k[1])

    mentions = {n: [] for n in names}
    for n in names:
        if n in HELD:
            continue
        k = field[n]
        for src in ([k[1]] if k[0] == "pre" else k[1]):
            mentions[src].append(n)

    # The connections in the order the lowered expression lists them.
    conns = ([(f"ff{i}_clk", "clkF_in", "copy") for i in range(w)] +
             [(f"ff{i}_clrn", "crF_in", "copy") for i in range(w)] +
             [(f"ff{i}_d", f"bitsOf {i} unp_d", "copy") for i in range(w)] +
             [(f"pk_b{i}", f"dffOut ff{i}_clk ff{i}_d ff{i}_clrn", "dff") for i in range(w)])

    def destructure(prefix=""):
        parts = []
        for node, ps in nodes:
            fs = [prefix + f"{node}_{p}" for p in ps]
            parts.append(fs[0] if len(ps) == 1 else "⟨" + ", ".join(fs) + "⟩")
        return "⟨" + ", ".join(parts) + "⟩"

    def projections(v):
        out = []
        for k, (node, ps) in enumerate(nodes):
            base = v + ".2" * k + ("" if k == len(nodes) - 1 else ".1")
            if len(ps) == 1:
                out.append(base)
            else:
                for j in range(len(ps)):
                    out.append(base + ".2" * j + (".1" if j < len(ps) - 1 else ""))
        return out

    def wf_call(subst=None, state="sp"):
        def arg(f):
            return ("(" + subst[1] + ")") if subst and f == subst[0] else f
        return " ".join(arg(f) for f in bools) + " " + arg("unp_d") + " " + state

    def update_fields(changed, growth):
        out = []
        for f in mentions[changed]:
            k = field[f]
            if k[0] == "pre":
                g = f"(bitsOf_mono {growth})" if k[2] else growth
                out.append((f, f"Hψ.w_{f}.trans {g}"))
            else:
                args = " ".join((growth if a == changed else "List.prefix_rfl") for a in k[1])
                out.append((f, f"Hψ.w_{f}.trans (dffOut_mono {args})"))
        return out

    L = []
    def emit(s=""):
        L.append(s)

    packed = " ".join(f"(dffOut clk (bitsOf {i} d) crn)" for i in range(w))
    emit("/-! ### The specification -/")
    emit()
    emit(f"/-- What the register reports: each bit of the bus through its own flip-flop. -/")
    emit(f"def {cfg['out']} (clk : List Bool) (d : {cfg['bus']}) (crn : List Bool) : {cfg['bus']} :=")
    emit(f"  {cfg['pack']} " + packed)
    emit()
    emit(f"theorem {cfg['out']}_mono {{clk clk' : List Bool}} {{d d' : {cfg['bus']}}}")
    emit( "    {crn crn' : List Bool} (hc : clk <+: clk') (hd : d <+: d') (hr : crn <+: crn') :")
    emit(f"    {cfg['out']} clk d crn <+: {cfg['out']} clk' d' crn' :=")
    emit(f"  {cfg['pack']}_mono " + " ".join(["(dffOut_mono hc (bitsOf_mono hd) hr)"] * w))
    emit()
    emit(f"/-- The {cfg['doc']} as a single block. -/")
    emit( "@[drcomponents]")
    emit(f"def {cfg['spec']} : StringModule ({state_ty}) :=")
    emit( "  { inputs := [ (↑\"clk\", ⟨List Bool, fun s v s' => s.1 ⊏ v ∧ s' = (v, s.2)⟩)")
    emit(f"              , (↑\"d\", ⟨{cfg['bus']}, fun s v s' => s.2.1 ⊏ v ∧ s' = (s.1, v, s.2.2)⟩)")
    emit( "              , (↑\"clrn\", ⟨List Bool, fun s v s' => s.2.2.1 ⊏ v ∧ s' = (s.1, s.2.1, v, s.2.2.2)⟩) ].toAssocList")
    emit(f"    outputs := [ (↑\"q\", ⟨{cfg['bus']}, fun s v s' => s.2.2.2 <+: v ∧")
    emit(f"                    v <+: {cfg['out']} s.1 s.2.1 s.2.2.1 ∧ s' = (s.1, s.2.1, s.2.2.1, v)⟩) ].toAssocList")
    emit( "    internals := []")
    emit( "    init_state := fun s => s = ([], [], [], []) }")
    emit()
    emit(f"instance : MatchInterface {cfg['netlist']} {cfg['spec']} := by")
    emit(f"  dsimp [{cfg['netlist']}, {cfg['spec']}]")
    emit( "  solve_match_interface")
    emit()
    emit("/-! ### The invariant -/")
    emit()
    emit("structure Wf (" + " ".join(bools) + " : List Bool)")
    emit(f"    (unp_d : {cfg['bus']}) (s : {state_ty}) : Prop where")
    for port, fld, node, eqname in INPUTS:
        emit(f"  {eqname} : {node} = {fld.replace('sp', 's')}")
    for n in names:
        if n in HELD:
            continue
        emit(f"  w_{n} : {n} <+: {rhs(n)}")
    emit(f"  h_q : s.2.2.2 <+: {cfg['pack']} " + " ".join(f"pk_b{i}" for i in range(w)))
    emit()
    proj = dict(zip(names, projections("i")))
    emit(f"def ψ (i : {cfg['T']}) (s : {state_ty}) : Prop :=")
    emit("  Wf " + " ".join(proj[f] for f in bools) + " " + proj["unp_d"] + " s")
    emit()
    nfields = len([n for n in names if n not in HELD])
    emit("theorem Wf.init : Wf " + " ".join(["[]"] * len(names)) + " ([], [], [], []) :=")
    emit("  ⟨rfl, rfl, rfl, " + ", ".join(["List.nil_prefix"] * (nfields + 1)) + "⟩")
    emit()
    emit("section SpecRules")
    emit(f"variable (sp : {state_ty})")
    emit()
    for port, fld, node, eqname in INPUTS:
        ty = cfg["bus"] if port == "d" else "List Bool"
        emit(f'theorem spec_in_{port} (v : {ty}) (h : {fld} ⊏ v) :')
        emit(f'    ({cfg["spec"]}.inputs.getIO ↑"{port}").2 sp v {SPEC_STATE[port]} := by')
        emit( "  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩")
        emit()
    emit(f'theorem spec_out_q (v : {cfg["bus"]}) (h1 : sp.2.2.2 <+: v)')
    emit(f'    (h2 : v <+: {cfg["out"]} sp.1 sp.2.1 sp.2.2.1) :')
    emit(f'    ({cfg["spec"]}.outputs.getIO ↑"q").2 sp v (sp.1, sp.2.1, sp.2.2.1, v) := by')
    emit( "  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h1, h2, rfl⟩")
    emit("end SpecRules")
    emit()
    emit("section Cases")
    emit("variable {" + " ".join(bools) + " : List Bool}")
    emit(f"  {{unp_d : {cfg['bus']}}} {{sp : {state_ty}}}")
    emit("  (Hψ : Wf " + wf_call() + ")")
    emit("include Hψ")
    emit()

    def emit_wf(upd, port=None, hq="Hψ.h_q"):
        lines = []
        for p, f, n, e in INPUTS:
            lines.append(f"          {e} := " + ("rfl" if p == port else f"Hψ.{e}"))
        for n in names:
            if n in HELD:
                continue
            lines.append(f"          w_{n} := " + upd.get(n, f"Hψ.w_{n}"))
        lines.append(f"          h_q := {hq}")
        lines[0] = "  exact {" + lines[0][9:]
        lines[-1] += " }"
        for l in lines:
            emit(l)

    for port, fld, node, eqname in INPUTS:
        ty = cfg["bus"] if port == "d" else "List Bool"
        emit(f"theorem in_{port} (v : {ty}) (h : {node} ⊏ v) :")
        emit("    Wf " + wf_call((node, "v"), SPEC_STATE[port]) + " := by")
        emit(f"  have hm : {node} <+: v := h.isPrefix")
        emit_wf(dict(update_fields(node, "hm")), port)
        emit()

    for k, (tgt, newval, kind) in enumerate(conns):
        if kind == "copy":
            emit(f"theorem int_{k} (_h : {tgt} ⊏ {newval}) :")
            growth, val = f"Hψ.w_{tgt}", newval
        else:
            emit(f"theorem int_{k} {{out : List Bool}} (_h : {tgt} ⊏ out) (hout : out <+: {newval}) :")
            growth, val = "(_h.isPrefix)", "out"
        emit("    Wf " + wf_call((tgt, val)) + " := by")
        upd = dict(update_fields(tgt, growth))
        upd[tgt] = "List.prefix_rfl" if kind == "copy" else "hout"
        if kind == "dff":
            i = int(tgt[4:])
            args = " ".join(("(_h.isPrefix)" if j == i else "List.prefix_rfl") for j in range(w))
            emit_wf(upd, hq=f"Hψ.h_q.trans ({cfg['pack']}_mono {args})")
        else:
            emit_wf(upd)
        emit()

    emit("/-- What the block reports is a prefix of the specification's stream: each bit is a prefix")
    emit("of its flip-flop's output, and the flip-flops see prefixes of the block's own inputs. -/")
    emit(f"theorem out_q : {cfg['pack']} " + " ".join(f"pk_b{i}" for i in range(w)) +
         f" <+: {cfg['out']} sp.1 sp.2.1 sp.2.2.1 := by")
    emit(f"  refine {cfg['pack']}_mono " + " ".join(["?_"] * w))
    for i in range(w):
        emit(f"  · exact Hψ.w_pk_b{i}.trans (dffOut_mono (Hψ.w_ff{i}_clk.trans (Hψ.e_clk ▸ List.prefix_rfl))")
        emit(f"      (Hψ.w_ff{i}_d.trans (bitsOf_mono (Hψ.e_d ▸ List.prefix_rfl)))")
        emit(f"      (Hψ.w_ff{i}_clrn.trans (Hψ.e_crn ▸ List.prefix_rfl)))")
    emit()
    emit("/-- What it has reported it has reported: the report is the packer's, and the packer's")
    emit("inputs only grow. -/")
    emit(f"theorem out_wf : Wf " + wf_call(None, f"(sp.1, sp.2.1, sp.2.2.1, {cfg['pack']} " +
         " ".join(f"pk_b{i}" for i in range(w)) + ")") + " := by")
    emit_wf({}, hq="List.prefix_rfl")
    emit()
    emit("end Cases")
    emit()

    DES_I, DES_M, DES_C = destructure(""), destructure("m_"), destructure("c_")
    emit("/-! ### The refinement -/")
    emit()
    for k, (tgt, newval, kind) in enumerate(conns):
        emit(f"theorem int_case_{k} (s : {state_ty}) (i mid : {cfg['T']}) (Hψ : ψ i s)")
        emit(f"    (Hrule : ({cfg['netlist']}.internals.getD {k} (fun _ _ => False)) i mid) :")
        emit(f"    ∃ s', existSR {cfg['spec']}.internals s s' ∧ ψ mid s' := by")
        emit(f"  obtain {DES_I} := i")
        emit(f"  obtain {DES_M} := mid")
        emit( "  dsimp only [ψ] at Hψ ⊢")
        emit( "  have H := Hrule.1 rfl")
        emit( "  clear Hrule")
        emit(f"  obtain ⟨{DES_C}, out, Hrule⟩ := H")
        emit( "  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule")
        emit( "  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)")
        emit(f"  exact ⟨s, existSR_reflexive, int_{k} Hψ ‹_›" + (" ‹_›⟩" if kind == "dff" else "⟩"))
        emit()
    emit(f"theorem {cfg['netlist']}_internals_eq : {cfg['netlist']}.internals = [" +
         ", ".join(f"{cfg['netlist']}.internals.getD {k} (fun _ _ => False)" for k in range(len(conns))) +
         "] := rfl")
    emit()
    emit(f"theorem refines_ψ : {cfg['netlist']} ⊑_{{ψ}} {cfg['spec']} := by")
    emit("  intro i s Hψ")
    emit("  constructor")
    emit("  · intro ident mid_i v Hrule")
    emit(f"    obtain {DES_I} := i")
    emit("    dsimp only [ψ] at Hψ")
    emit(f"    obtain {DES_M} := mid_i")
    emit(f"    case_transition Hcontains : Module.inputs {cfg['netlist']}, ident, (PortMap.getIO_not_contained_false' Hrule)")
    emit(f"    dsimp only [{cfg['netlist']}] at Hcontains")
    emit("    simp at Hcontains")
    emit("    rcases Hcontains with " + " | ".join(["h"] * len(INPUTS)))
    emit("    all_goals subst h")
    emit("    all_goals rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule")
    emit("    all_goals dsimp only at Hrule")
    emit("    all_goals simp only [Prod.mk.injEq, and_assoc] at Hrule")
    emit("    all_goals repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)")
    emit("    all_goals first")
    for port, fld, node, eqname in INPUTS:
        emit(f"      | exact ⟨_, _, spec_in_{port} s _ (by rw [← Hψ.{eqname}]; assumption), "
             f"existSR_reflexive, in_{port} Hψ _ ‹_›⟩")
    emit("  · intro ident mid_i v Hrule")
    emit(f"    obtain {DES_I} := i")
    emit("    dsimp only [ψ] at Hψ")
    emit(f"    obtain {DES_M} := mid_i")
    emit(f"    case_transition Hcontains : Module.outputs {cfg['netlist']}, ident, (PortMap.getIO_not_contained_false' Hrule)")
    emit(f"    dsimp only [{cfg['netlist']}] at Hcontains")
    emit("    simp at Hcontains")
    emit("    subst Hcontains")
    emit("    rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule")
    emit("    dsimp only at Hrule")
    emit("    simp only [Prod.mk.injEq, and_assoc] at Hrule")
    emit("    repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)")
    emit("    exact ⟨s, _, existSR_reflexive, spec_out_q s _ Hψ.h_q (out_q Hψ), out_wf Hψ⟩")
    emit("  · intro rule mid_i Hin Hrule")
    emit(f"    rw [{cfg['netlist']}_internals_eq] at Hin")
    emit("    simp only [List.mem_cons, List.not_mem_nil, or_false] at Hin")
    emit("    rcases Hin with " + " | ".join(["h"] * len(conns)))
    for k in range(len(conns)):
        emit(f"    · subst h; exact int_case_{k} s i mid_i Hψ Hrule")
    emit()
    emit(f"theorem refines_initial : Module.refines_initial {cfg['netlist']} {cfg['spec']} ψ := by")
    emit("  intro i hi")
    emit(f"  obtain {DES_I} := i")
    emit(f"  dsimp only [{cfg['netlist']}] at hi")
    emit("  simp only [Prod.mk.injEq, and_assoc] at hi")
    emit("  obtain ⟨" + ", ".join(["rfl"] * len(names)) + "⟩ := hi")
    emit("  exact ⟨([], [], [], []), rfl, Wf.init⟩")
    emit()
    emit(f"/-- **The {w} flip-flops refine a {cfg['doc']}.** -/")
    emit(f"theorem reg_refines : {cfg['netlist']} ⊑ {cfg['spec']} :=")
    emit("  ⟨inferInstance, ψ, refines_ψ, refines_initial⟩")
    emit()
    emit(f"end Graphiti.AsyncFifo.{cfg['ns']}")

    path = pathlib.Path("Graphiti/Projects/AsyncFifo") / cfg["file"]
    src = path.read_text()
    marker = "-- HEADER_END (everything below is generated by gen/gen_busreg.py)\n"
    head = src.split(marker)[0]
    path.write_text(head + marker + "\n" + "\n".join(L) + "\n")
    print(f"wrote {path} ({len(head.splitlines()) + len(L)} lines)")


for cfg in CONFIGS:
    generate(cfg)
