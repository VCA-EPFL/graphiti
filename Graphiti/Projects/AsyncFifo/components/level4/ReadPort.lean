/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Core.Graph.ModuleLemmas
import Graphiti.Core.Graph.ModuleReduction
import Graphiti.Core.Graph.ExprHighElaborator
import Graphiti.Projects.AsyncFifo.components.level0.Streams
import Graphiti.Projects.AsyncFifo.components.level1.Gates
import Graphiti.Projects.AsyncFifo.components.level3.Contracts

/-!
# The read port as gates

The read domain's data output is `mem[ptr]`: combinational, and at depth 4 with one-bit data it
is a two-bit address decode and a four-way multiplexer --- eleven gates.

The one thing that has to be said about it is why the memory can be gates at all.  The wire that
carries it from the write domain has type `List (BitVec 2 → Bool)`: at each instant a *function*
from address to value.  That is what makes `Contracts.MemAt` sayable --- a write to one entry is
invisible to another --- but gates carry `Bool`.  The bridge is a projection: a function-valued
wire *is* four wires, and `entry a` picks one of them, exactly as `WriteState.bitsOf` picks a bit out
of a record.  It computes nothing; it is the same kind of adapter as `unpackSt` or `unpackNext`.

The other thing worth naming is why the contract is `Contracts.ReadOut` and not `Comb`.  A
multiplexer depends combinationally on *all four* entries, so a `Comb` argument would demand the
whole memory stand still over the delay window --- which is precisely what a memory is for not
having to do.  The gate-level argument is the one `RegFile.W_en_false` already makes for the write
decoder: once the address has settled, the three disabled AND gates are `false` whatever their
data, so only the selected entry reaches the output.  `ReadOut`'s two hypotheses (the address
stable, the *selected* word held) are exactly what that argument consumes.

The window is `[3, 5]`: an entry reaches the output through one AND and two ORs, and the address
through an inverter first.
-/

set_option linter.unusedSectionVars false

namespace Graphiti.AsyncFifo.ReadPort

open Graphiti.AsyncFifo Graphiti.AsyncFifo.Gates Graphiti.AsyncFifo.Contracts

/-! ### The two projections

Neither is logic: both are the identity on the wires the stream stands for. -/

/-- Bit `i` of the read address. -/
def addrBit (i : Nat) (st : List (RSt 2)) : List Bool :=
  st.map (fun x => (x.ptr.setWidth 2).getLsbD i)

/-- Entry `a` of the memory, as its own wire. -/
def entry (a : BitVec 2) (mem : List (BitVec 2 → Bool)) : List Bool :=
  mem.map (fun f => f a)

/-- The boundary cut: the block reports only as far as its own inputs are known.  `ReadOut`'s
length clause has no `+ 1` --- a combinational block is not entitled to the instant a Moore
block is --- so the cut is exact. -/
def cutOut (o r1 r2 : List Bool) : List Bool := o.take (min r1.length r2.length)

/-! ### The netlist -/

/-- The two projections as a block: no logic, only wiring.  `a0c`/`m0c` are the same wires as
`a0`/`m0`, offered a second time for the boundary cut. -/
@[drcomponents]
def unpRD : StringModule (List (RSt 2) × List (BitVec 2 → Bool)) :=
  { inputs := [ (↑"st", ⟨List (RSt 2), fun s v s' => s.1 ⊏ v ∧ s' = (v, s.2)⟩)
              , (↑"mem", ⟨List (BitVec 2 → Bool), fun s v s' => s.2 ⊏ v ∧ s' = (s.1, v)⟩)
              ].toAssocList
    outputs := [ (↑"a0", ⟨List Bool, fun s v s' => s' = s ∧ v = addrBit 0 s.1⟩)
               , (↑"a0c", ⟨List Bool, fun s v s' => s' = s ∧ v = addrBit 0 s.1⟩)
               , (↑"a1", ⟨List Bool, fun s v s' => s' = s ∧ v = addrBit 1 s.1⟩)
               , (↑"m0", ⟨List Bool, fun s v s' => s' = s ∧ v = entry 0#2 s.2⟩)
               , (↑"m0c", ⟨List Bool, fun s v s' => s' = s ∧ v = entry 0#2 s.2⟩)
               , (↑"m1", ⟨List Bool, fun s v s' => s' = s ∧ v = entry 1#2 s.2⟩)
               , (↑"m2", ⟨List Bool, fun s v s' => s' = s ∧ v = entry 2#2 s.2⟩)
               , (↑"m3", ⟨List Bool, fun s v s' => s' = s ∧ v = entry 3#2 s.2⟩)
               ].toAssocList
    internals := []
    init_state := fun s => s = ([], []) }

/-- The boundary cut as a block. -/
@[drcomponents]
def cutRD : StringModule (List Bool × List Bool × List Bool) :=
  { inputs := [ (↑"in", ⟨List Bool, fun s v s' => s.1 ⊏ v ∧ s' = (v, s.2)⟩)
              , (↑"r1", ⟨List Bool, fun s v s' => s.2.1 ⊏ v ∧ s' = (s.1, v, s.2.2)⟩)
              , (↑"r2", ⟨List Bool, fun s v s' => s.2.2 ⊏ v ∧ s' = (s.1, s.2.1, v)⟩)
              ].toAssocList
    outputs := [ (↑"out", ⟨List Bool, fun s v s' => s' = s ∧ v = cutOut s.1 s.2.1 s.2.2⟩)
               ].toAssocList
    internals := []
    init_state := fun s => s = ([], [], []) }

def muxGraph := [graphEnv|
    st [type="io"];
    mem [type="io"];
    q [type="io"];

    unpRD [type="unpRD", typeImp=$(⟨_, unpRD⟩)];
    fa0 [type="fork3", typeImp=$(⟨_, fork3⟩)];
    fa1 [type="fork3", typeImp=$(⟨_, fork3⟩)];
    na0 [type="inv", typeImp=$(⟨_, gate1 not⟩)];
    na1 [type="inv", typeImp=$(⟨_, gate1 not⟩)];
    fn0 [type="fork2", typeImp=$(⟨_, fork2 Bool⟩)];
    fn1 [type="fork2", typeImp=$(⟨_, fork2 Bool⟩)];
    s0 [type="and2", typeImp=$(⟨_, gate2 Bool.and⟩)];
    s1 [type="and2", typeImp=$(⟨_, gate2 Bool.and⟩)];
    s2 [type="and2", typeImp=$(⟨_, gate2 Bool.and⟩)];
    s3 [type="and2", typeImp=$(⟨_, gate2 Bool.and⟩)];
    g0 [type="and2", typeImp=$(⟨_, gate2 Bool.and⟩)];
    g1 [type="and2", typeImp=$(⟨_, gate2 Bool.and⟩)];
    g2 [type="and2", typeImp=$(⟨_, gate2 Bool.and⟩)];
    g3 [type="and2", typeImp=$(⟨_, gate2 Bool.and⟩)];
    o01 [type="or2", typeImp=$(⟨_, gate2 Bool.or⟩)];
    o23 [type="or2", typeImp=$(⟨_, gate2 Bool.or⟩)];
    outg [type="or2", typeImp=$(⟨_, gate2 Bool.or⟩)];
    cut [type="cutRD", typeImp=$(⟨_, cutRD⟩)];

    st -> unpRD [to="st"];
    mem -> unpRD [to="mem"];

    unpRD -> fa0 [from="a0", to="in"];
    unpRD -> fa1 [from="a1", to="in"];
    unpRD -> cut [from="a0c", to="r1"];
    unpRD -> cut [from="m0c", to="r2"];
    fa0 -> na0 [from="out1", to="a"];
    fa1 -> na1 [from="out1", to="a"];
    na0 -> fn0 [from="out", to="in"];
    na1 -> fn1 [from="out", to="in"];
    fn0 -> s0 [from="out1", to="a"];
    fn1 -> s0 [from="out1", to="b"];
    fa0 -> s1 [from="out2", to="a"];
    fn1 -> s1 [from="out2", to="b"];
    fn0 -> s2 [from="out2", to="a"];
    fa1 -> s2 [from="out2", to="b"];
    fa0 -> s3 [from="out3", to="a"];
    fa1 -> s3 [from="out3", to="b"];
    s0 -> g0 [from="out", to="a"];
    unpRD -> g0 [from="m0", to="b"];
    s1 -> g1 [from="out", to="a"];
    unpRD -> g1 [from="m1", to="b"];
    s2 -> g2 [from="out", to="a"];
    unpRD -> g2 [from="m2", to="b"];
    s3 -> g3 [from="out", to="a"];
    unpRD -> g3 [from="m3", to="b"];
    g0 -> o01 [from="out", to="a"];
    g1 -> o01 [from="out", to="b"];
    g2 -> o23 [from="out", to="a"];
    g3 -> o23 [from="out", to="b"];
    o01 -> outg [from="out", to="a"];
    o23 -> outg [from="out", to="b"];
    outg -> cut [from="out", to="in"];

    cut -> q [from="out"];
  ]

@[drunfold_defs]
def muxLowered := muxGraph.1.lower_TR |>.get rfl

def rdenv := muxGraph.2

/-- **The read port, as gates.** -/
def readImpl := [e| muxLowered, rdenv.find? ]

section Spec
variable {n : Nat}
variable (α : Type) [Inhabited α]

/-- State of the read port: the state register's output, the memory snapshot, and the data it
has emitted. -/
structure RDataSt (α : Type) (n : Nat) where
  st : List (RSt n)
  mem : List (BitVec n → α)
  q : List α

def rdataLen (s : RDataSt α n) : Nat := min s.st.length s.mem.length

/-- The read port: the memory word at the read address, combinational with a delay window. -/
@[drcomponents]
def readSpec (dmin dmax : Nat) : StringModule (RDataSt α n) :=
  { inputs := [ (↑"st", ⟨List (RSt n), fun s v s' => s.st ⊏ v ∧ s' = { s with st := v }⟩)
              , (↑"mem", ⟨List (BitVec n → α), fun s v s' => s.mem ⊏ v ∧ s' = { s with mem := v }⟩)
              ].toAssocList
    outputs := [ (↑"q", ⟨List α, fun s v s' => s.q <+: v ∧
                    ReadOut dmin dmax (fun u => (s.st.getD u default).ptr.setWidth n)
                      (fun u => s.mem.getD u (fun _ => default)) (rdataLen α s) v ∧
                    s' = { s with q := v }⟩) ].toAssocList
    internals := []
    init_state := fun s => s = ⟨[], [], []⟩ }

end Spec

end Graphiti.AsyncFifo.ReadPort
