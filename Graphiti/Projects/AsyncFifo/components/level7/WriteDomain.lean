/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Core.Graph.ModuleLemmas
import Graphiti.Core.Graph.ModuleReduction
import Graphiti.Core.Graph.ExprHighElaborator
import Graphiti.Projects.AsyncFifo.components.level0.Gray
import Graphiti.Projects.AsyncFifo.components.level0.Streams
import Graphiti.Projects.AsyncFifo.components.level2.Domains
import Graphiti.Projects.AsyncFifo.components.level1.Filters
import Graphiti.Projects.AsyncFifo.components.level3.Contracts
import Graphiti.Projects.AsyncFifo.components.level6.WriteBank
import Graphiti.Projects.AsyncFifo.components.level4.WriteNext
import Graphiti.Projects.AsyncFifo.components.level5.SyncStage

/-!
# The write clock domain

Its specification `wdomSpec` says what the domain may show on its outputs: the Gray pointer,
the flag and the data as the register-level machine of `Domains.lean` would, up to the timing
filters --- a clk-to-q window on each edge, glitch-free bits on the bus that crosses domains, and
nothing promised once a timing assumption has been violated.

Its implementation `wdomImpl` is a graph of its register bank (`WriteBank`),
its next-state logic (`WriteNext`) and its synchroniser's first stage (`SyncStage`), each standing for its
specification; `wdomImpl_refines` (`TopRefinement.lean`) is this layer's theorem.
-/

namespace Graphiti.AsyncFifo

open Graphiti.AsyncFifo.Contracts

section Filters
set_option linter.unusedSectionVars false
open Gray
variable {α : Type} [Inhabited α] {n : Nat}
variable (lat stl su kq P S R pw : Nat) (clk inc : List Bool) (data : List α) (rgray : List (BitVec (n+1))) (orc : List (Orc n))

/-- The write domain's timing assumptions hold for all edges before `t`.  The last one, on the
width of the clock's pulses, is what a netlist of gates needs and a register-level model does
not; it is a promise about the environment like the others. -/
def WFilter (t : Nat) : Prop :=
  ClockOK P clk t ∧ InOK S clk inc t ∧ InOK S clk data t ∧ ResetOK R clk t ∧ PulseOK pw clk t

/-- Relaxed Gray-pointer output: exact when settled, glitch-free inside the clk-to-q window. -/
def WGrayF (v : List (BitVec (n+1))) : Prop :=
  v.length ≤ wLen lat clk inc data rgray orc + 1 ∧
  ∀ t, t < v.length → WFilter P S R pw clk inc data t →
    (Settled kq clk t → v.getD t 0 = gray (wRun lat stl su clk inc data rgray orc t).ptr) ∧
    (∀ e, LastEdge clk e t → t < e + kq → ∀ i,
      (v.getD t 0).getLsbD i = (gray (wRun lat stl su clk inc data rgray orc t).ptr).getLsbD i ∨
      (v.getD t 0).getLsbD i = (gray (wRun lat stl su clk inc data rgray orc e).ptr).getLsbD i)

/-- Relaxed `full` output: exact when settled. -/
def WFullF (v : List Bool) : Prop :=
  v.length ≤ wLen lat clk inc data rgray orc + 1 ∧
  ∀ t, t < v.length → WFilter P S R pw clk inc data t → Settled kq clk t →
    v.getD t false = (wRun lat stl su clk inc data rgray orc t).full

/-- A write to entry `a` at (edge) instant `e`, as decided by the machine. -/
def WriteAt (a : BitVec n) (e : Nat) : Prop :=
  riseAt clk e = true ∧ (inc.getD e false && !(wRun lat stl su clk inc data rgray orc e).full) = true ∧
  (wRun lat stl su clk inc data rgray orc e).ptr.setWidth n = a

/-- Entry `a` is outside the clk-to-q window of any write to it. -/
def MemSettled (a : BitVec n) (t : Nat) : Prop :=
  ∀ e, e < t → WriteAt lat stl su clk inc data rgray orc a e → e + kq ≤ t

/-- Relaxed memory output: exact for entries not being written. -/
def WMemF (v : List (BitVec n → α)) : Prop :=
  v.length ≤ wLen lat clk inc data rgray orc + 1 ∧
  ∀ t, t < v.length → WFilter P S R pw clk inc data t → ∀ a, MemSettled lat stl su kq clk inc data rgray orc a t →
    (v.getD t (fun _ => default)) a = (wRun lat stl su clk inc data rgray orc t).mem a

end Filters

section Spec
variable (α : Type) [Inhabited α] (n lat stl su : Nat)

/-- State of the filtered write-domain module: the five input streams and the three output
streams emitted so far. -/
structure WStateF (α : Type) (n : Nat) where
  clk : List Bool
  inc : List Bool
  data : List α
  rgray : List (BitVec (n+1))
  orc : List (Orc n)
  gray_q : List (BitVec (n+1))
  full_q : List Bool
  mem_q : List (BitVec n → α)

/-- The write domain with its timing assumptions as filters: the outputs are only determined
outside clk-to-q windows (`kq`) and while the clock (`P`) and the inputs (`S`) respect their
assumptions; an output may only be extended. -/
@[drcomponents]
def wdomSpec (kq P S R pw : Nat) : StringModule (WStateF α n) :=
  { inputs := [ (↑"clk", ⟨List Bool, fun s v s' => s.clk ⊏ v ∧ s' = { s with clk := v }⟩)
              , (↑"inc", ⟨List Bool, fun s v s' => s.inc ⊏ v ∧ s' = { s with inc := v }⟩)
              , (↑"data", ⟨List α, fun s v s' => s.data ⊏ v ∧ s' = { s with data := v }⟩)
              , (↑"rgray", ⟨List (BitVec (n+1)), fun s v s' => s.rgray ⊏ v ∧ s' = { s with rgray := v }⟩)
              , (↑"orc", ⟨List (Orc n), fun s v s' => s.orc ⊏ v ∧ s' = { s with orc := v }⟩)
              ].toAssocList
    outputs := [ (↑"gray", ⟨List (BitVec (n+1)), fun s v s' => s.gray_q <+: v ∧
                    WGrayF lat stl su kq P S R pw s.clk s.inc s.data s.rgray s.orc v ∧ s' = { s with gray_q := v }⟩)
               , (↑"full", ⟨List Bool, fun s v s' => s.full_q <+: v ∧
                    WFullF lat stl su kq P S R pw s.clk s.inc s.data s.rgray s.orc v ∧ s' = { s with full_q := v }⟩)
               , (↑"mem", ⟨List (BitVec n → α), fun s v s' => s.mem_q <+: v ∧
                    WMemF lat stl su kq P S R pw s.clk s.inc s.data s.rgray s.orc v ∧ s' = { s with mem_q := v }⟩)
               ].toAssocList
    internals := []
    init_state := fun s => s = ⟨[], [], [], [], [], [], [], []⟩ }

end Spec

/-! ## Implementation: the domain as blocks

Each block is used through its specification (`bankSpec`, `nextSpec`, `syncSpec`); that each
block's own implementation meets it is proved one level down, and `TopGates.lean` substitutes
the gates in. -/

section Impl
variable (α : Type) [Inhabited α]
variable (n lat kq su stl dmin dmax P pw Rr Rc : Nat)

/-- The write domain as timed RTL blocks.  Same interface as `writeDomain`: the clear is
produced inside the domain by `clrS`, so nothing outside has to know the bank needs one. -/
def wdomGraph := [graphEnv|
    clk [type="io"];
    inc [type="io"];
    data [type="io"];
    rgray [type="io"];
    orc [type="io"];
    gray [type="io"];
    full [type="io"];
    mem [type="io"];

    clkF [type="clkF", typeImp=$(⟨_, fork2 Bool⟩)];
    regs [type="WriteBank", typeImp=$(⟨_, WriteBank.bankSpec α (n := n) kq su P pw Rr Rc⟩)];
    clrS [type="clearSrc", typeImp=$(⟨_, clearSrc Rc⟩)];
    next [type="WriteNext", typeImp=$(⟨_, WriteNext.nextSpec α (n := n) dmin dmax⟩)];
    sync [type="SyncStage", typeImp=$(⟨_, SyncStage.syncSpec (n := n) lat su stl⟩)];

    clk -> clkF [to="in"];
    clkF -> regs [from="out1", to="clk"];
    clrS -> regs [from="crn", to="clrn"];
    clkF -> sync [from="out2", to="clk"];
    rgray -> sync [to="d"];
    orc -> sync [to="orc"];
    inc -> next [to="inc"];
    data -> next [to="data"];
    sync -> next [from="q", to="q1"];
    regs -> next [from="st", to="st"];
    next -> regs [from="d", to="d"];

    regs -> gray [from="gray"];
    regs -> full [from="full"];
    regs -> mem [from="mem"];
  ]

/-- The blocks of `wdomGraph`, by type name. -/
def wenv := (wdomGraph α n lat kq su stl dmin dmax P pw Rr Rc).2

/-- The wiring of `wdomGraph` (independent of the parameters). -/
@[drunfold_defs]
def wdomLowered := (wdomGraph Unit 0 0 0 0 0 0 0 0 0 0 0).1.lower_TR |>.get rfl

/-- The write domain as blocks. -/
def wdomImpl := [e| wdomLowered, (wenv α n lat kq su stl dmin dmax P pw Rr Rc).find? ]

end Impl

end Graphiti.AsyncFifo
