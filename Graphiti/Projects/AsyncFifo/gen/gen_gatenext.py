#!/usr/bin/env python3
"""Generate ../GateNext.lean: the next-state logic of the write domain (n = 2, 1-bit data) as a
netlist of unit-delay gates, and its refinement of `nextBlock Bool 0 8`.

Run from anywhere: `python3 Graphiti/Projects/AsyncFifo/gen/gen_gatenext.py`.

Proof-engineering rules followed by every generated proof: no `bv_decide` (its certificates are
checked by native code, which adds axioms; the finite identity is checked with `decide +kernel`),
and never hand `omega` a nested `min`
(it case-splits each one, so its time and memory double per `min`).  Stream lengths are
handled with `Nat.lt_min`, `min_le_iff_nat` and `min_mono` from `Gates.lean`.
"""
import os

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "..", "GateNext.lean")

# ---------------------------------------------------------------- netlist description
# node kinds: unpack, pack, gate2 (f), gate1 (f), fork2, fork3, fork4
# ports: gate2: a b / out ; gate1: a / out ; forkN: in / out1..outN
# unpack: st q1 / p0 p1 p2 fl q20 q21 q22 q10 q11 q12
# pack: p0 p1 p2 fl q0 q1 q2 g0 g1 g2 we a0 a1 dt / d

nodes = [  # (name, kind, f)   -- order = state order
  ("unp", "unpack", None),
  ("nfl", "gate1", "not"),
  ("ok", "gate2", "Bool.and"),
  ("fok", "fork3", None),
  ("fp0", "fork3", None),
  ("fp1", "fork3", None),
  ("xp0", "gate2", "Bool.xor"),
  ("cp0", "gate2", "Bool.and"),
  ("fc0", "fork2", None),
  ("xp1", "gate2", "Bool.xor"),
  ("cp1", "gate2", "Bool.and"),
  ("xp2", "gate2", "Bool.xor"),
  ("fpa", "fork3", None),   # fork of p0'
  ("fpb", "fork4", None),   # fork of p1'
  ("fpc", "fork4", None),   # fork of p2'
  ("xg0", "gate2", "Bool.xor"),
  ("xg1", "gate2", "Bool.xor"),
  ("fq2", "fork2", None),   # fork of q22
  ("xu1", "gate2", "Bool.xor"),
  ("fu1", "fork2", None),
  ("xu0", "gate2", "Bool.xor"),
  ("xe2", "gate2", "Bool.xor"),
  ("xe1", "gate2", "xnor"),
  ("xe0", "gate2", "xnor"),
  ("ae", "gate2", "Bool.and"),
  ("af", "gate2", "Bool.and"),
  ("pk", "pack", None),
]
kind_of = {n: k for n, k, _ in nodes}
f_of = {n: f for n, _, f in nodes}

# external inputs: (external name, consumer node, consumer port)
ext_in = [("st", "unp", "st"), ("inc", "ok", "a"), ("data", "pk", "dt"), ("q1", "unp", "q1")]
ext_out = ("pk", "d", "d")

# wires: (driver node, driver port, consumer node, consumer port)
wires = [
  ("unp", "fl", "nfl", "a"),
  ("nfl", "out", "ok", "b"),
  ("ok", "out", "fok", "in"),
  ("unp", "p0", "fp0", "in"),
  ("unp", "p1", "fp1", "in"),
  ("fp0", "out1", "xp0", "a"), ("fok", "out1", "xp0", "b"),
  ("fp0", "out2", "cp0", "a"), ("fok", "out2", "cp0", "b"),
  ("cp0", "out", "fc0", "in"),
  ("fp1", "out1", "xp1", "a"), ("fc0", "out1", "xp1", "b"),
  ("fp1", "out2", "cp1", "a"), ("fc0", "out2", "cp1", "b"),
  ("unp", "p2", "xp2", "a"), ("cp1", "out", "xp2", "b"),
  ("xp0", "out", "fpa", "in"), ("xp1", "out", "fpb", "in"), ("xp2", "out", "fpc", "in"),
  ("fpb", "out2", "xg0", "a"), ("fpa", "out2", "xg0", "b"),
  ("fpc", "out2", "xg1", "a"), ("fpb", "out3", "xg1", "b"),
  ("unp", "q22", "fq2", "in"),
  ("fq2", "out1", "xu1", "a"), ("unp", "q21", "xu1", "b"),
  ("xu1", "out", "fu1", "in"),
  ("fu1", "out1", "xu0", "a"), ("unp", "q20", "xu0", "b"),
  ("fpc", "out4", "xe2", "a"), ("fq2", "out2", "xe2", "b"),
  ("fpb", "out4", "xe1", "a"), ("fu1", "out2", "xe1", "b"),
  ("fpa", "out3", "xe0", "a"), ("xu0", "out", "xe0", "b"),
  ("xe2", "out", "ae", "a"), ("xe1", "out", "ae", "b"),
  ("ae", "out", "af", "a"), ("xe0", "out", "af", "b"),
  # packer inputs
  ("fpa", "out1", "pk", "p0"), ("fpb", "out1", "pk", "p1"), ("fpc", "out1", "pk", "p2"),
  ("af", "out", "pk", "fl"),
  ("unp", "q10", "pk", "q0"), ("unp", "q11", "pk", "q1"), ("unp", "q12", "pk", "q2"),
  ("xg0", "out", "pk", "g0"), ("xg1", "out", "pk", "g1"), ("fpc", "out3", "pk", "g2"),
  ("fok", "out3", "pk", "we"),
  ("fp0", "out3", "pk", "a0"), ("fp1", "out3", "pk", "a1"),
]

pack_ports = ["p0", "p1", "p2", "fl", "q0", "q1", "q2", "g0", "g1", "g2", "we", "a0", "a1", "dt"]
unpack_outs = {"p0": "fun x => x.ptr.getLsbD 0", "p1": "fun x => x.ptr.getLsbD 1", "p2": "fun x => x.ptr.getLsbD 2",
               "fl": "fun x => x.full",
               "q20": "fun x => x.q2.getLsbD 0", "q21": "fun x => x.q2.getLsbD 1", "q22": "fun x => x.q2.getLsbD 2"}
unpack_q1_outs = {"q10": "fun x => x.getLsbD 0", "q11": "fun x => x.getLsbD 1", "q12": "fun x => x.getLsbD 2"}
unpack_F = {"p0": "i.1.ptr.getLsbD 0", "p1": "i.1.ptr.getLsbD 1", "p2": "i.1.ptr.getLsbD 2", "fl": "i.1.full",
            "q20": "i.1.q2.getLsbD 0", "q21": "i.1.q2.getLsbD 1", "q22": "i.1.q2.getLsbD 2",
            "q10": "i.2.2.2.getLsbD 0", "q11": "i.2.2.2.getLsbD 1", "q12": "i.2.2.2.getLsbD 2"}

def ports_of(name):
    k = kind_of[name]
    if k == "unpack": return ["st", "q1"]
    if k == "pack": return pack_ports
    if k == "gate2": return ["a", "b"]
    if k == "gate1": return ["a"]
    return ["in"]

def stype(name, port):
    if name == "unp" and port == "st": return "List (Timed.WSt 2)"
    if name == "unp" and port == "q1": return "List (BitVec 3)"
    return "List Bool"

def var(name, port): return f"{name}_{port}"

# all stored streams in state order
streams = [(n, p) for n, _, _ in nodes for p in ports_of(n)]

# who drives each consumer port
driver = {(c, cp): (d, dp) for d, dp, c, cp in wires}
extdrv = {(c, cp): e for e, c, cp in ext_in}
assert len(driver) == len(wires), "a port is driven twice"

def fterm(f):
    return "(fun a b => a == b)" if f == "xnor" else f

def W_src(d, dp):
    """Name of the `W_` wire function of a node output, following forks to their source."""
    k = kind_of[d]
    if k in ("gate2", "gate1"): return f"W_{d}"
    if k == "unpack": return f"W_unp_{dp}"
    if k.startswith("fork"):
        return W_src(*driver[(d, "in")])
    raise Exception(d)

def W_of_input(c, cp):
    """`W` term (applied to `s`) feeding the consumer port (c, cp)."""
    if (c, cp) in extdrv:
        return {"st": "s.st", "inc": "s.inc", "data": "s.data", "q1": "s.q1"}[extdrv[(c, cp)]]
    d, dp = driver[(c, cp)]
    return f"{W_src(d, dp)} s"

def F_of_input(c, cp):
    if (c, cp) in extdrv:
        return {"inc": "F_inc", "data": "F_data"}[extdrv[(c, cp)]]
    d, dp = driver[(c, cp)]
    k = kind_of[d]
    if k in ("gate2", "gate1"): return f"F_{d}"
    if k == "unpack": return f"F_unp_{dp}"
    return F_of_input(d, "in")

def C_of_input(c, cp):
    if (c, cp) in extdrv:
        return {"inc": "C_inc s", "data": "C_data s"}[extdrv[(c, cp)]]
    d, dp = driver[(c, cp)]
    k = kind_of[d]
    if k in ("gate2", "gate1"): return f"C_{d} s"
    if k == "unpack": return f"C_unp_{dp} s"
    return C_of_input(d, "in")

def mono_of_input(c, cp):
    """term : W_of_input s <+: W_of_input s' given h1 h2 h3 h4"""
    if (c, cp) in extdrv:
        return {"st": "h1", "inc": "h2", "data": "h3", "q1": "h4"}[extdrv[(c, cp)]]
    d, dp = driver[(c, cp)]
    k = kind_of[d]
    if k in ("gate2", "gate1"): return f"(W_{d}_mono h1 h2 h3 h4)"
    if k == "unpack": return f"(W_unp_{dp}_mono h1 h2 h3 h4)"
    return mono_of_input(d, "in")

# depths
depth = {}
def depth_of_input(c, cp):
    if (c, cp) in extdrv: return (0, 0)
    d, dp = driver[(c, cp)]
    k = kind_of[d]
    if k == "unpack": return (0, 0)
    if k.startswith("fork"): return depth_of_input(d, "in")
    return depth[d]
for n, k, f in nodes:
    if k == "gate2":
        la, ha = depth_of_input(n, "a"); lb, hb = depth_of_input(n, "b")
        depth[n] = (min(la, lb) + 1, max(ha, hb) + 1)
    elif k == "gate1":
        la, ha = depth_of_input(n, "a"); depth[n] = (la + 1, ha + 1)
DMAX = max(depth_of_input("pk", p)[1] for p in pack_ports)
assert DMAX == 8, DMAX

def nested_min(terms):
    e = terms[-1]
    for t in reversed(terms[:-1]): e = f"min {t} ({e})"
    return e

def nested_min_mono(proofs):
    e = proofs[-1]
    for p in reversed(proofs[:-1]): e = f"min_mono {p} ({e})"
    return e

# ---------------------------------------------------------------- Lean text
out = []
def w(s=""): out.append(s)

w('''/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.Gates

/-!
# The next-state logic of the write domain as gates

This file is generated by `gen/gen_gatenext.py` from a netlist of 16 gates, 9 forks and two bus
adapters, for a FIFO of depth `2^2` with 1-bit data.  The netlist computes `wNext`: the
incremented pointer (half-adder chain gated by the write enable), its Gray encoding (two
XORs), the `full` flag (Gray decoding of the synchronised read pointer, MSB flip for the
`+ 2^n`, equality by XNORs and ANDs), the write command and the pass-through of the first
synchroniser stage.  `unpack2` splits the record bus of the state register into bits and
`pack2` assembles the record bus loaded by the register bank; both are wiring, without logic.

`gateNext_refines : gateNext ⊑ nextBlock Bool 0 8`: the netlist is a next-state block with
delay window `[0, 8]`.  The longest path (write enable → carries → equality → `full`) has
eight gates, and some bits pass straight through.
-/

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace Graphiti.AsyncFifo.GateNext

open Graphiti.AsyncFifo Graphiti.AsyncFifo.Timed Graphiti.AsyncFifo.Gates Gray
open Batteries (AssocList)

/-! ### Bus adapters -/

/-- The state register's record bus and the synchroniser's bus, split into bits. -/
@[drcomponents]
def unpack2 : StringModule (List (WSt 2) × List (BitVec 3)) :=
  { inputs := [ (↑"st", ⟨List (WSt 2), fun s v s' => s.1 ⊏ v ∧ s' = (v, s.2)⟩)
              , (↑"q1", ⟨List (BitVec 3), fun s v s' => s.2 ⊏ v ∧ s' = (s.1, v)⟩) ].toAssocList
    outputs := [''')
first = True
for p, fn in list(unpack_outs.items()):
    w(f'''               {"" if first else ","} (↑"{p}", ⟨List Bool, fun s v s' => s' = s ∧ v = List.map ({fn}) s.1⟩)''')
    first = False
for p, fn in unpack_q1_outs.items():
    w(f'''               , (↑"{p}", ⟨List Bool, fun s v s' => s' = s ∧ v = List.map ({fn}) s.2⟩)''')
w('''               ].toAssocList
    internals := []
    init_state := fun s => s = ([], []) }


/-- Stored inputs of the packer: the fourteen bit streams of the next-state bus. -/
structure PackSt where''')
for p in pack_ports: w(f"  {p} : List Bool")
w()
w("def packLen (s : PackSt) : Nat :=")
w("  " + nested_min([f"s.{p}.length" for p in pack_ports]))
w('''
/-- The record bus assembled from its bits, reported one instant short of where the bits reach.

That instant is the block's reporting policy: it keeps the block inside the horizon its
*inputs* justify, which is what `CombOut`'s length clause asks for and what makes that contract
monotone.  Each bit of the bus is at least one gate deep from at least one input, so the gates
run one instant ahead; `W_pack_length` checks that dropping one is enough.  Reporting less than
one computes is always sound. -/
def pack2Out (s : PackSt) : List (WNext Bool 2) :=
  timeline (fun t => ⟨⟨bv3 (s.p0.getD t false) (s.p1.getD t false) (s.p2.getD t false), s.fl.getD t false,
      bv3 (s.q0.getD t false) (s.q1.getD t false) (s.q2.getD t false)⟩,
    bv3 (s.g0.getD t false) (s.g1.getD t false) (s.g2.getD t false), s.we.getD t false,
    bv2 (s.a0.getD t false) (s.a1.getD t false), s.dt.getD t false⟩) (packLen s - 1)

@[simp] theorem pack2Out_length (s : PackSt) : (pack2Out s).length = packLen s - 1 := timeline_length _ _

theorem pack2Out_getD (s : PackSt) {t : Nat} (ht : t < packLen s - 1) :
    (pack2Out s).getD t default = ⟨⟨bv3 (s.p0.getD t false) (s.p1.getD t false) (s.p2.getD t false), s.fl.getD t false,
      bv3 (s.q0.getD t false) (s.q1.getD t false) (s.q2.getD t false)⟩,
    bv3 (s.g0.getD t false) (s.g1.getD t false) (s.g2.getD t false), s.we.getD t false,
    bv2 (s.a0.getD t false) (s.a1.getD t false), s.dt.getD t false⟩ := timeline_getD _ ht _

theorem pack2Out_mono {s s' : PackSt} ''' + " ".join(f"(h{p} : s.{p} <+: s'.{p})" for p in pack_ports) + ''' :
    pack2Out s <+: pack2Out s' := by
  apply timeline_mono (Nat.sub_le_sub_right (''' + nested_min_mono([f"h{p}.length_le" for p in pack_ports]) + ''') 1)
  intro t ht
  have ht2 : t < packLen s := Nat.lt_of_lt_of_le ht (Nat.sub_le _ _)
  simp only [packLen, Nat.lt_min] at ht2
  obtain ⟨''' + ", ".join(f"t_{p}" for p in pack_ports) + '''⟩ := ht2
  rw [''' + ", ".join(f"h{p}.getD_eq_left t_{p}" for p in pack_ports) + ''']

/-- `pack2Out_mono` stated field by field: callers then unify their wires with the fields
syntactically, instead of unfolding a wire to compare it with a projection. -/
theorem pack2Out_mono' {''' + " ".join(f"{p} {p}'" for p in pack_ports) + ''' : List Bool}
    ''' + " ".join(f"(h{p} : {p} <+: {p}')" for p in pack_ports) + ''' :
    pack2Out ⟨''' + ", ".join(pack_ports) + '''⟩ <+: pack2Out ⟨''' + ", ".join(f"{p}'" for p in pack_ports) + '''⟩ :=
  pack2Out_mono ''' + " ".join(f"h{p}" for p in pack_ports) + '''

@[drcomponents]
def pack2 : StringModule PackSt :=
  { inputs := [''')
first = True
for p in pack_ports:
    w(f'''              {"" if first else ","} (↑"{p}", ⟨List Bool, fun s v s' => s.{p} ⊏ v ∧ s' = {{ s with {p} := v }}⟩)''')
    first = False
w('''              ].toAssocList
    outputs := [ (↑"d", ⟨List (WNext Bool 2), fun s v s' => s' = s ∧ v = pack2Out s⟩) ].toAssocList
    internals := []
    init_state := fun s => s = ⟨''' + ", ".join("[]" for _ in pack_ports) + '''⟩ }

/-! ### The netlist -/
''')
types = {}
for n, k, f in nodes:
    if k == "unpack": types[n] = ("unpack2", "unpack2")
    elif k == "pack": types[n] = ("pack2", "pack2")
    elif k == "gate1": types[n] = (f"g1_{f.replace('.', '_')}", f"gate1 {fterm(f)}")
    elif k == "gate2": types[n] = (f"g2_{f.replace('.', '_')}", f"gate2 {fterm(f)}")
    elif k == "fork2": types[n] = ("fork2", "fork2 Bool")
    else: types[n] = (k, k)
env_entries = {}
for n in types: env_entries[types[n][0]] = types[n][1]

def iport(node, port): return f'⟨.internal "{node}", "{port}"⟩'
def tport(name): return f'⟨.top, "{name}"⟩'

def base_text(n):
    k = kind_of[n]
    ins = []
    for p in ports_of(n):
        if (n, p) in extdrv: ins.append((p, tport(extdrv[(n, p)])))
        else: ins.append((p, iport(n, p)))
    outs = []
    if k == "unpack": op = list(unpack_outs) + list(unpack_q1_outs)
    elif k == "pack": op = ["d"]
    elif k in ("gate2", "gate1"): op = ["out"]
    else: op = [f"out{i+1}" for i in range(int(k[-1]))]
    for p in op:
        if (n, p) == (ext_out[0], ext_out[1]): outs.append((p, tport(ext_out[2])))
        else: outs.append((p, iport(n, p)))
    def al(lst):
        s = ".nil"
        for p, q in reversed(lst):
            s = f"(.cons {tport(p)} {q} {s})"
        return s
    return f'.base {{ input := {al(ins)}, output := {al(outs)} }} "{types[n][0]}"'

w("@[drunfold_defs]")
w("def gateNextExpr : ExprLow String String :=")
prod = f"({base_text(nodes[-1][0])})"
for n, _, _ in reversed(nodes[:-1]):
    prod = f"(.product ({base_text(n)}) {prod})"
expr = prod
for d, dp, c, cp in reversed(wires):
    expr = f"(.connect {{ output := {iport(d, dp)}, input := {iport(c, cp)} }} {expr})"
w("  " + expr)
w()
w("def genv : AssocList String (TModule1 String) :=")
w("  [" + ", ".join(f'("{t}", ⟨_, {m}⟩)' for t, m in env_entries.items()) + "].toAssocList")
w()
for t, m in env_entries.items():
    w(f'@[drenv] theorem genv_{t} : genv.find? "{t}" = .some ⟨_, {m}⟩ := rfl')
w()
w("/-- The state of the netlist: the stored inputs of every node, in netlist order. -/")
w("abbrev gateNextT : Type :=")
tys = []
for n, _, _ in nodes:
    ps = ports_of(n)
    if kind_of[n] == "pack": tys.append("PackSt")
    elif len(ps) == 1: tys.append(stype(n, ps[0]))
    else: tys.append("(" + " × ".join(stype(n, p) for p in ps) + ")")
w("  " + " × ".join(tys))
w('''
seal genv in
def_module gateNextT' : Type :=
  [T| gateNextExpr, genv.find? ]
reduction_by
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type,
         ExprLow.build_module, ExprLow.build_module', toString]
  simp only [drenv]
  dsimp

theorem gateNextT_eq : gateNextT' = gateNextT := rfl

set_option maxHeartbeats 4000000 in
seal genv in
def_module gateNext : StringModule gateNextT :=
  [e| gateNextExpr, genv.find? ]

/-! ### The wires as functions of the block's inputs -/

/-- Primary inputs at one instant, as `nextDep` produces them. -/
abbrev Inp := WSt 2 × Bool × Bool × BitVec 3

def F_inc : Inp → Bool := fun i => i.2.1
def F_data : Inp → Bool := fun i => i.2.2.1''')
for p, e in unpack_F.items():
    w(f"def F_unp_{p} : Inp → Bool := fun i => {e}")
for n, k, f in nodes:
    if k == "gate2":
        w(f"def F_{n} : Inp → Bool := fun i => {fterm(f)} ({F_of_input(n,'a')} i) ({F_of_input(n,'b')} i)")
    elif k == "gate1":
        w(f"def F_{n} : Inp → Bool := fun i => {fterm(f)} ({F_of_input(n,'a')} i)")
w()
for p, fn in unpack_outs.items():
    w(f"def W_unp_{p} (s : NextSt Bool 2) : List Bool := List.map ({fn}) s.st")
for p, fn in unpack_q1_outs.items():
    w(f"def W_unp_{p} (s : NextSt Bool 2) : List Bool := List.map ({fn}) s.q1")
for n, k, f in nodes:
    if k == "gate2":
        w(f"def W_{n} (s : NextSt Bool 2) : List Bool := gateOut {fterm(f)} ({W_of_input(n,'a')}) ({W_of_input(n,'b')})")
    elif k == "gate1":
        w(f"def W_{n} (s : NextSt Bool 2) : List Bool := gate1Out {fterm(f)} ({W_of_input(n,'a')})")
w()
w("/-- The packer's stored inputs when every wire carries its full stream. -/")
w("def Wpk (s : NextSt Bool 2) : PackSt := ⟨" + ", ".join(W_of_input("pk", p) for p in pack_ports) + "⟩")
w("def W_pack (s : NextSt Bool 2) : List (WNext Bool 2) := pack2Out (Wpk s)")
w()
w("/-! ### Monotonicity of the wires in the inputs -/")
w()
w("variable {s s' : NextSt Bool 2}")
w()
for p in list(unpack_outs):
    w(f"theorem W_unp_{p}_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.data <+: s'.data) (h4 : s.q1 <+: s'.q1) :")
    w(f"    W_unp_{p} s <+: W_unp_{p} s' := h1.map _")
for p in list(unpack_q1_outs):
    w(f"theorem W_unp_{p}_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.data <+: s'.data) (h4 : s.q1 <+: s'.q1) :")
    w(f"    W_unp_{p} s <+: W_unp_{p} s' := h4.map _")
for n, k, f in nodes:
    if k == "gate2":
        w(f"theorem W_{n}_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.data <+: s'.data) (h4 : s.q1 <+: s'.q1) :")
        w(f"    W_{n} s <+: W_{n} s' := gateOut_mono _ {mono_of_input(n,'a')} {mono_of_input(n,'b')}")
    elif k == "gate1":
        w(f"theorem W_{n}_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.data <+: s'.data) (h4 : s.q1 <+: s'.q1) :")
        w(f"    W_{n} s <+: W_{n} s' := gate1Out_mono _ {mono_of_input(n,'a')}")
w()
w("/-! ### Combinational contracts of the wires -/")
w()
w("variable (s : NextSt Bool 2)")
w()
w("theorem C_inc : Comb 0 0 F_inc (nextDep Bool s) s.inc := Comb.input (fun t _ => rfl)")
w("theorem C_data : Comb 0 0 F_data (nextDep Bool s) s.data := Comb.input (fun t _ => rfl)")
for p in list(unpack_outs) + list(unpack_q1_outs):
    w(f"theorem C_unp_{p} : Comb 0 0 F_unp_{p} (nextDep Bool s) (W_unp_{p} s) :=")
    w(f"  Comb.input (fun t ht => by unfold W_unp_{p} at ht ⊢; rw [getD_map_lt _ _ (by simpa using ht)]; rfl)")
for n, k, f in nodes:
    if k == "gate2":
        lo, hi = depth[n]
        w(f"theorem C_{n} : Comb {lo} {hi} F_{n} (nextDep Bool s) (W_{n} s) :=")
        w(f"  Comb.gate2 {fterm(f)} ({C_of_input(n,'a')}) ({C_of_input(n,'b')})")
    elif k == "gate1":
        lo, hi = depth[n]
        w(f"theorem C_{n} : Comb {lo} {hi} F_{n} (nextDep Bool s) (W_{n} s) :=")
        w(f"  Comb.gate1 {fterm(f)} ({C_of_input(n,'a')})")
w()
def F_pk(p): return F_of_input("pk", p)
# The identity between the netlist and `wNext` is a finite check over 12 input bits.  It is
# checked by the kernel (`decide +kernel`), one lemma per field of the record, so that it rests
# on no axiom beyond Lean's own: `bv_decide` would add axioms trusting natively compiled code.
comps = [("st_ptr", "st.ptr", lambda I: f"bv3 ({F_pk('p0')} {I}) ({F_pk('p1')} {I}) ({F_pk('p2')} {I})"),
         ("st_full", "st.full", lambda I: f"{F_pk('fl')} {I}"),
         ("st_q2", "st.q2", lambda I: f"bv3 ({F_pk('q0')} {I}) ({F_pk('q1')} {I}) ({F_pk('q2')} {I})"),
         ("gnext", "gnext", lambda I: f"bv3 ({F_pk('g0')} {I}) ({F_pk('g1')} {I}) ({F_pk('g2')} {I})"),
         ("we", "we", lambda I: f"{F_pk('we')} {I}"),
         ("addr", "addr", lambda I: f"bv2 ({F_pk('a0')} {I}) ({F_pk('a1')} {I})"),
         ("data", "data", lambda I: f"{F_pk('dt')} {I}")]
def rec(i):
    return ("(⟨⟨" + comps[0][2](i) + ", " + comps[1][2](i) + ", " + comps[2][2](i) + "⟩, " +
            ", ".join(c[2](i) for c in comps[3:]) + "⟩ : WNext Bool 2)")
Io = "((⟨BitVec.ofNat 3 a, full, BitVec.ofNat 3 b⟩ : WSt 2), inc, data, BitVec.ofNat 3 c)"
Iv = "((⟨ptr, full, q2⟩ : WSt 2), inc, data, q1)"
w("/-! ### The netlist computes the next-state function")
w("")
w("One field of the record at a time, for all 4096 values of the input bits, checked by the kernel. -/")
w()
for nm, proj, lhs in comps:
    w(f"theorem identity_{nm} : ∀ a, a < 2 ^ 3 → ∀ b, b < 2 ^ 3 → ∀ c, c < 2 ^ 3 → ∀ full inc data : Bool,")
    w(f"    {lhs(Io)} = (nextFun Bool {Io}).{proj} := by decide +kernel")
    w()
w("theorem pack_identity' (ptr q2 q1 : BitVec 3) (full inc data : Bool) :")
w("    " + rec(Iv) + " = nextFun Bool " + Iv + " := by")
w("  have e : ∀ x : BitVec 3, BitVec.ofNat 3 x.toNat = x := fun x => by simp")
for nm, proj, lhs in comps:
    w(f"  have h_{nm} := identity_{nm} ptr.toNat ptr.isLt q2.toNat q2.isLt q1.toNat q1.isLt full inc data")
    w(f"  rw [e ptr, e q2, e q1] at h_{nm}")
proj_rec = ("⟨⟨(nextFun Bool I).st.ptr, (nextFun Bool I).st.full, (nextFun Bool I).st.q2⟩, (nextFun Bool I).gnext, "
            "(nextFun Bool I).we, (nextFun Bool I).addr, (nextFun Bool I).data⟩").replace("I", Iv)
w(f"  rw [show nextFun Bool {Iv} = {proj_rec} from rfl]")
w("  rw [" + ", ".join(f"h_{nm}" for nm, _, _ in comps) + "]")
w()
w("theorem pack_identity (i : Inp) : " + rec("i") + " = nextFun Bool i := by")
w("  obtain ⟨⟨ptr, full, q2⟩, inc, data, q1⟩ := i")
w("  exact pack_identity' ptr q2 q1 full inc data")
w()
allW = [f"W_unp_{p}" for p in unpack_F] + [f"W_{n}" for n, k, _ in nodes if k in ("gate2", "gate1")]
w("/-- The packer's output is no longer than the block's inputs.  Each bound is a disjunction over")
w("the leaves of the length tree, closed by the leaf that is the input itself. -/")
w("theorem W_pack_length : (W_pack s).length ≤ nextLen Bool s := by")
w("  simp only [W_pack, pack2Out_length, nextLen, Nat.le_min]")
w("  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩")
w("  all_goals rw [Nat.sub_le_iff_le_add]")
w("  all_goals simp only [packLen, Wpk, " + ", ".join(allW) +
  ", gateOut_length, gate1Out_length, gate3Out_length, List.length_map, Nat.add_le_add_iff_right," +
  " min_le_iff_nat, Nat.le_refl, true_or, or_true, Nat.le_add_right]")
w()
w("/-- **The netlist satisfies the contract of the next-state block** with delay window `[0, 8]`. -/")
w("theorem W_pack_comb : CombOut (nextDep Bool s) (nextFun Bool) (nextLen Bool s) 0 8 (W_pack s) := by")
w("  refine ⟨W_pack_length s, fun t hdt ht hs => ?_⟩")
w("  have hst := Comb.stable_of_StableOn hs")
w("  simp only [W_pack, pack2Out_length] at ht")
w("  have htp : t < packLen (Wpk s) - 1 := ht")
w("  have ht : t < packLen (Wpk s) := Nat.lt_of_lt_of_le htp (Nat.sub_le _ _)")
w("  simp only [packLen, Wpk, Nat.lt_min] at ht")
w("  obtain ⟨" + ", ".join(f"t_{p}" for p in pack_ports) + "⟩ := ht")
w("  rw [W_pack, pack2Out_getD _ htp]")
w("  simp only [Wpk]")
seen = set()
for p in pack_ports:
    src = W_of_input("pk", p)
    if src in seen: continue   # `rw` already rewrote every occurrence of this wire
    seen.add(src)
    c = C_of_input("pk", p)
    w(f"  rw [({c}).weaken (Nat.zero_le _) (by decide) |>.2 t hdt t_{p} hst]")
w("  exact pack_identity _")
w()

# ------------------------------------------------ refinement
w("/-! ### Refinement of the next-state block -/")
w()
w("instance : MatchInterface gateNext (nextBlock Bool (n := 2) 0 8) := by")
w("  dsimp [gateNext, nextBlock]")
w("  solve_match_interface")
w()
params = " ".join(f"({var(n,p)} : {stype(n,p)})" for n, p in streams)
w("/-- The simulation relation: primary inputs agree, every stored stream is a prefix of the wire")
w("it is connected to, and the specification's output history is the packer's current output. -/")
w(f"structure Psi {params} (s : NextSt Bool 2) : Prop where")
w("  e_unp_st : unp_st = s.st")
w("  e_unp_q1 : unp_q1 = s.q1")
w("  e_ok_a : ok_a = s.inc")
w("  e_pk_dt : pk_dt = s.data")
for d, dp, c, cp in wires:
    w(f"  w_{c}_{cp} : {var(c,cp)} <+: {W_src(d,dp)} s")
w("  d_hist : s.d <+: pack2Out ⟨" + ", ".join(var("pk", p) for p in pack_ports) + "⟩")
w()
def proj_path(idx, total):
    if idx == total - 1: return ".2" * idx
    return ".2" * idx + ".1"
args = []
for k, (n, _, _) in enumerate(nodes):
    base = "i" + proj_path(k, len(nodes))
    ps = ports_of(n)
    if kind_of[n] == "pack":
        args += [f"{base}.{p}" for p in ps]
    elif len(ps) == 1:
        args.append(base)
    else:
        args.append(f"{base}.1"); args.append(f"{base}.2")
w("def ψ (i : gateNextT) (s : NextSt Bool 2) : Prop :=")
w("  Psi " + " ".join(args) + " s")
w()
allvars = [var(n, p) for n, p in streams]
w(f"theorem Psi.init : Psi {' '.join('[]' for _ in allvars)} ⟨[], [], [], [], []⟩ :=")
w("  ⟨rfl, rfl, rfl, rfl, " + ", ".join("List.nil_prefix" for _ in wires) + ", List.nil_prefix⟩")
w()
w("section SpecRules")
w("variable (sp : NextSt Bool 2)")
for port, ty, fld in [("st", "List (WSt 2)", "st"), ("inc", "List Bool", "inc"), ("data", "List Bool", "data"), ("q1", "List (BitVec 3)", "q1")]:
    w(f"theorem spec_in_{port} (v : {ty}) (h : sp.{fld} ⊏ v) :")
    w(f'    ((nextBlock Bool (n := 2) 0 8).inputs.getIO ↑"{port}").2 sp v {{ sp with {fld} := v }} := by')
    w("  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩")
w("theorem spec_out_d (v : List (WNext Bool 2)) (h1 : sp.d <+: v)")
w("    (h2 : CombOut (nextDep Bool sp) (nextFun Bool) (nextLen Bool sp) 0 8 v) :")
w('    ((nextBlock Bool (n := 2) 0 8).outputs.getIO ↑"d").2 sp v { sp with d := v } := by')
w("  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h1, h2, rfl⟩")
w("end SpecRules")
w()
w("section Cases")
w("variable {" + " ".join(allvars) + "} {sp : NextSt Bool 2}")
w(f"  (Hψ : Psi {' '.join(allvars)} sp)")
w("include Hψ")
w()
def psi_with(repl, spec):
    return "Psi " + " ".join(repl.get(v, v) for v in allvars) + f" {spec}"
for ext, c, cp, fld, monos in [("st", "unp", "st", "st", "(Hψ.e_unp_st ▸ h.isPrefix) List.prefix_rfl List.prefix_rfl List.prefix_rfl"),
                               ("inc", "ok", "a", "inc", "List.prefix_rfl (Hψ.e_ok_a ▸ h.isPrefix) List.prefix_rfl List.prefix_rfl"),
                               ("data", "pk", "dt", "data", "List.prefix_rfl List.prefix_rfl (Hψ.e_pk_dt ▸ h.isPrefix) List.prefix_rfl"),
                               ("q1", "unp", "q1", "q1", "List.prefix_rfl List.prefix_rfl List.prefix_rfl (Hψ.e_unp_q1 ▸ h.isPrefix)")]:
    v = var(c, cp)
    ty = stype(c, cp)
    w(f"theorem in_{ext} (v : {ty}) (h : {v} ⊏ v) :")
    w(f"    {psi_with({v: 'v'}, f'{{ sp with {fld} := v }}')} where")
    for e in ["e_unp_st", "e_unp_q1", "e_ok_a", "e_pk_dt"]:
        target = {"e_unp_st": ("unp", "st"), "e_unp_q1": ("unp", "q1"), "e_ok_a": ("ok", "a"), "e_pk_dt": ("pk", "dt")}[e]
        w(f"  {e} := rfl" if target == (c, cp) else f"  {e} := Hψ.{e}")
    for d, dp, c2, cp2 in wires:
        w(f"  w_{c2}_{cp2} := Hψ.w_{c2}_{cp2}.trans ({W_src(d,dp)}_mono {monos})")
    if ext == "data":
        old = "⟨" + ", ".join(var("pk", p) for p in pack_ports) + "⟩"
        new = "⟨" + ", ".join("v" if p == "dt" else var("pk", p) for p in pack_ports) + "⟩"
        w("  d_hist := Hψ.d_hist.trans (pack2Out_mono' " + " ".join("List.prefix_rfl" if p != "dt" else "h.isPrefix" for p in pack_ports) + ")")
    else:
        w("  d_hist := Hψ.d_hist")
    w()
w("/-- The packer's current output satisfies the block's contract. -/")
pk_prefixes = []
for p in pack_ports:
    pk_prefixes.append("(Hψ.e_pk_dt ▸ List.prefix_rfl : pk_dt <+: sp.data)" if ("pk", p) in extdrv else f"Hψ.w_pk_{p}")
w("theorem out_comb : CombOut (nextDep Bool sp) (nextFun Bool) (nextLen Bool sp) 0 8")
w("    (pack2Out ⟨" + ", ".join(var("pk", p) for p in pack_ports) + "⟩) :=")
w("  CombOut.of_prefix (pack2Out_mono' " + " ".join(pk_prefixes) + ") (W_pack_comb sp)")
w()
w("theorem out_psi :")
w(f"    {psi_with({}, '{ sp with d := pack2Out ⟨' + ', '.join(var('pk', p) for p in pack_ports) + '⟩ }')} :=")
w("  { Hψ with d_hist := List.prefix_rfl }")
w()
def drv_out_expr(d, dp):
    k = kind_of[d]
    if k == "gate2": return f"gateOut {fterm(f_of[d])} {var(d,'a')} {var(d,'b')}"
    if k == "gate1": return f"gate1Out {fterm(f_of[d])} {var(d,'a')}"
    if k.startswith("fork"): return var(d, "in")
    if k == "unpack":
        if dp in unpack_outs: return f"List.map ({unpack_outs[dp]}) unp_st"
        return f"List.map ({unpack_q1_outs[dp]}) unp_q1"
    raise Exception(d)
def prefix_of_input(d, p):
    if (d, p) in extdrv:
        e = {"st": "e_unp_st", "inc": "e_ok_a", "data": "e_pk_dt", "q1": "e_unp_q1"}[extdrv[(d, p)]]
        return f"(Hψ.{e} ▸ List.prefix_rfl)"
    return f"Hψ.w_{d}_{p}"
def new_field_proof(d, dp):
    k = kind_of[d]
    if k == "gate2": return f"gateOut_mono _ {prefix_of_input(d,'a')} {prefix_of_input(d,'b')}"
    if k == "gate1": return f"gate1Out_mono _ {prefix_of_input(d,'a')}"
    if k.startswith("fork"): return prefix_of_input(d, "in")
    if k == "unpack":
        e = "e_unp_st" if dp in unpack_outs else "e_unp_q1"
        return f"(by rw [Hψ.{e}]; exact List.prefix_rfl)"
for idx, (d, dp, c, cp) in enumerate(wires):
    v = var(c, cp)
    w(f"theorem int_{idx} (h : {v} ⊏ {drv_out_expr(d,dp)}) :")
    w(f"    {psi_with({v: '(' + drv_out_expr(d,dp) + ')'}, 'sp')} :=")
    if c == "pk":
        old = "⟨" + ", ".join(var("pk", p) for p in pack_ports) + "⟩"
        newv = "(" + drv_out_expr(d, dp) + ")"
        new = "⟨" + ", ".join(newv if p == cp else var("pk", p) for p in pack_ports) + "⟩"
        prefs = " ".join("h.isPrefix" if p == cp else "List.prefix_rfl" for p in pack_ports)
        w("  { Hψ with")
        w(f"    w_{c}_{cp} := {new_field_proof(d,dp)}")
        w(f"    d_hist := Hψ.d_hist.trans (pack2Out_mono' {prefs}) }}")
    else:
        w(f"  {{ Hψ with w_{c}_{cp} := {new_field_proof(d,dp)} }}")
    w()
w("end Cases")
w()
def destr(prefix):
    parts = []
    for n, _, _ in nodes:
        ps = ports_of(n)
        if len(ps) == 1: parts.append(prefix + var(n, ps[0]))
        else: parts.append("⟨" + ", ".join(prefix + var(n, p) for p in ps) + "⟩")
    return "⟨" + ", ".join(parts) + "⟩"
w("/-! ### One lemma per internal rule")
w("")
w("The reduced module lists its internal rules in the order of the netlist's wires, so rule `k`")
w("transfers wire `k`.  Each case is its own declaration: handling all of them in one proof keeps")
w("52 goals over 56-component states alive at once and exhausts memory.  Inside a case, the rule")
w("is applied to `rfl` to discharge its trivial type-equality guard, instead of simplifying the")
w("guard away, which would traverse the whole rule body; the original hypothesis is cleared, since")
w("it still holds all 52 rules and every `subst` would otherwise rewrite it. -/")
w()
for k in range(len(wires)):
    w(f"theorem int_case_{k} (s : NextSt Bool 2) (i mid : gateNextT) (Hψ : ψ i s)")
    w(f"    (Hrule : (gateNext.internals.getD {k} (fun _ _ => False)) i mid) :")
    w("    ∃ s', existSR (nextBlock Bool (n := 2) 0 8).internals s s' ∧ ψ mid s' := by")
    w(f"  obtain {destr('')} := i")
    w(f"  obtain {destr('m_')} := mid")
    w("  dsimp only [ψ] at Hψ ⊢")
    w("  have H := Hrule.1 rfl")
    w("  clear Hrule")
    w(f"  obtain ⟨{destr('c_')}, out, Hrule⟩ := H")
    w("  simp only [Prod.mk.injEq, PackSt.mk.injEq, and_assoc, and_true, true_and] at Hrule")
    w("  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)")
    w(f"  exact ⟨s, existSR_reflexive, int_{k} Hψ ‹_›⟩")
    w()
w("/-- The internal rules, each named by its index: membership then splits over small terms instead")
w("of the 52 rule bodies. -/")
w("theorem gateNext_internals_eq : gateNext.internals = [" +
  ", ".join(f"gateNext.internals.getD {k} (fun _ _ => False)" for k in range(len(wires))) + "] := rfl")
w()
w("set_option maxHeartbeats 1000000 in")
w("theorem refines_ψ : gateNext ⊑_{ψ} nextBlock Bool (n := 2) 0 8 := by")
w("  intro i s Hψ")
w("  constructor")
w("  · intro ident mid_i v Hrule")
w(f"    obtain {destr('')} := i")
w("    dsimp only [ψ] at Hψ")
w(f"    obtain {destr('m_')} := mid_i")
w("    case_transition Hcontains : Module.inputs gateNext, ident, (PortMap.getIO_not_contained_false' Hrule)")
w("    dsimp only [gateNext] at Hcontains")
w("    simp at Hcontains")
w("    rcases Hcontains with h | h | h | h")
w("    all_goals subst h")
w("    all_goals rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule")
w("    all_goals dsimp only at Hrule")
w("    all_goals simp only [Prod.mk.injEq, PackSt.mk.injEq, and_assoc] at Hrule")
w("    all_goals repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)")
w("    all_goals first")
w("      | exact ⟨_, _, spec_in_st s _ (by rw [← Hψ.e_unp_st]; assumption), existSR_reflexive, in_st Hψ _ ‹_›⟩")
w("      | exact ⟨_, _, spec_in_inc s _ (by rw [← Hψ.e_ok_a]; assumption), existSR_reflexive, in_inc Hψ _ ‹_›⟩")
w("      | exact ⟨_, _, spec_in_data s _ (by rw [← Hψ.e_pk_dt]; assumption), existSR_reflexive, in_data Hψ _ ‹_›⟩")
w("      | exact ⟨_, _, spec_in_q1 s _ (by rw [← Hψ.e_unp_q1]; assumption), existSR_reflexive, in_q1 Hψ _ ‹_›⟩")
w("  · intro ident mid_i v Hrule")
w(f"    obtain {destr('')} := i")
w("    dsimp only [ψ] at Hψ")
w(f"    obtain {destr('m_')} := mid_i")
w("    case_transition Hcontains : Module.outputs gateNext, ident, (PortMap.getIO_not_contained_false' Hrule)")
w("    dsimp only [gateNext] at Hcontains")
w("    simp at Hcontains")
w("    subst Hcontains")
w("    rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule")
w("    dsimp only at Hrule")
w("    simp only [Prod.mk.injEq, PackSt.mk.injEq, and_assoc] at Hrule")
w("    repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)")
w("    exact ⟨s, _, existSR_reflexive, spec_out_d s _ Hψ.d_hist (out_comb Hψ), out_psi Hψ⟩")
w("  · intro rule mid_i Hin Hrule")
w("    rw [gateNext_internals_eq] at Hin")
w("    simp only [List.mem_cons, List.not_mem_nil, or_false] at Hin")
w("    rcases Hin with " + " | ".join("h" for _ in wires))
for k in range(len(wires)):
    w(f"    · subst h; exact int_case_{k} s i mid_i Hψ Hrule")
w()
w("set_option maxHeartbeats 1000000 in")
w("theorem refines_initial : Module.refines_initial gateNext (nextBlock Bool (n := 2) 0 8) ψ := by")
w("  intro i hi")
w(f"  obtain {destr('')} := i")
w("  dsimp only [gateNext] at hi")
w("  simp only [Prod.mk.injEq, PackSt.mk.injEq, and_assoc] at hi")
w("  obtain ⟨" + ", ".join("rfl" for _ in allvars) + "⟩ := hi")
w("  exact ⟨⟨[], [], [], [], []⟩, rfl, Psi.init⟩")
w()
w("/-- **The gate netlist refines the timed next-state block** with delay window `[0, 8]`. -/")
w("theorem gateNext_refines : gateNext ⊑ nextBlock Bool (n := 2) 0 8 :=")
w("  ⟨inferInstance, ψ, refines_ψ, refines_initial⟩")
w()
w("end Graphiti.AsyncFifo.GateNext")

open(OUT, "w").write("\n".join(out) + "\n")
print(f"wrote {os.path.normpath(OUT)}: nodes {len(nodes)}, wires {len(wires)}, streams {len(streams)}, dmax {DMAX}")
