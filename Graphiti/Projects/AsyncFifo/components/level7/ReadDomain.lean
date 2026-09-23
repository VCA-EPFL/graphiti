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
import Graphiti.Projects.AsyncFifo.components.level6.ReadBank
import Graphiti.Projects.AsyncFifo.components.level4.ReadNext
import Graphiti.Projects.AsyncFifo.components.level5.SyncStage
import Graphiti.Projects.AsyncFifo.components.level4.ReadPort

/-!
# The read clock domain

Its specification `rdomSpec` says what the domain may show on its outputs: the Gray pointer,
the flag and the data as the register-level machine of `Domains.lean` would, up to the timing
filters --- a clk-to-q window on each edge, glitch-free bits on the bus that crosses domains, and
nothing promised once a timing assumption has been violated.

Its implementation `rdomImpl` is a graph of its register bank (`ReadBank`),
its next-state logic (`ReadNext`), its synchroniser's first stage (`SyncStage`) and its read
port (`ReadPort`), each standing for its
specification; `rdomImpl_refines` (`TopRefinement.lean`) is this layer's theorem.
-/

namespace Graphiti.AsyncFifo

open Graphiti.AsyncFifo.Contracts

section Filters
set_option linter.unusedSectionVars false
open Gray
variable {α : Type} [Inhabited α] {n : Nat}
variable (lat stl su kq rdly P S R pw : Nat) (rclk rinc : List Bool) (wgray : List (BitVec (n+1))) (orc : List (Orc n))
  (mem : List (BitVec n → α))

def RFilter (t : Nat) : Prop :=
  ClockOK P rclk t ∧ InOK S rclk rinc t ∧ ResetOK R rclk t ∧ PulseOK pw rclk t

def RGrayF (v : List (BitVec (n+1))) : Prop :=
  v.length ≤ rLen lat rclk rinc wgray orc + 1 ∧
  ∀ t, t < v.length → RFilter P S R pw rclk rinc t →
    (Settled kq rclk t → v.getD t 0 = gray (rRun lat stl su rclk rinc wgray orc t).ptr) ∧
    (∀ e, LastEdge rclk e t → t < e + kq → ∀ i,
      (v.getD t 0).getLsbD i = (gray (rRun lat stl su rclk rinc wgray orc t).ptr).getLsbD i ∨
      (v.getD t 0).getLsbD i = (gray (rRun lat stl su rclk rinc wgray orc e).ptr).getLsbD i)

def REmptyF (v : List Bool) : Prop :=
  v.length ≤ rLen lat rclk rinc wgray orc + 1 ∧
  ∀ t, t < v.length → RFilter P S R pw rclk rinc t → Settled kq rclk t →
    v.getD t false = (rRun lat stl su rclk rinc wgray orc t).empty

/-- Entry `a` held its value over the read port's window `d`.  This is what an asynchronous read
port needs of the memory, and all it needs: a write to any *other* entry is invisible to it. -/
def MemHold (d : Nat) (m : List (BitVec n → α)) (a : BitVec n) (t : Nat) : Prop :=
  ∀ u, t - d ≤ u → u ≤ t → (m.getD u (fun _ => default)) a = (m.getD t (fun _ => default)) a

/-- Relaxed read data: the memory word at the read address, once the pointer has settled *and*
the read port's own window `rdly` has passed.  The port is combinational, so it needs two things
its neighbours do not: the address settled `rdly` longer than a register would (`kq + rdly`), and
the entry it addresses held over that window --- the one place a read-domain output depends on
the write domain's timing. -/
def RDataF (v : List α) : Prop :=
  v.length ≤ rDataLen lat rclk rinc wgray orc mem ∧
  ∀ t, rdly ≤ t → t < v.length → RFilter P S R pw rclk rinc t → Settled (kq + rdly) rclk t →
    MemHold rdly mem ((rRun lat stl su rclk rinc wgray orc t).ptr.setWidth n) t →
    v.getD t default = rval lat stl su rclk rinc wgray orc mem t

end Filters

section Spec
variable (α : Type) [Inhabited α] (n lat stl su : Nat)

structure RStateF (α : Type) (n : Nat) where
  clk : List Bool
  inc : List Bool
  wgray : List (BitVec (n+1))
  orc : List (Orc n)
  mem : List (BitVec n → α)
  gray_q : List (BitVec (n+1))
  empty_q : List Bool
  rdata_q : List α

@[drcomponents]
def rdomSpec (kq rdly P S R pw : Nat) : StringModule (RStateF α n) :=
  { inputs := [ (↑"clk", ⟨List Bool, fun s v s' => s.clk ⊏ v ∧ s' = { s with clk := v }⟩)
              , (↑"inc", ⟨List Bool, fun s v s' => s.inc ⊏ v ∧ s' = { s with inc := v }⟩)
              , (↑"wgray", ⟨List (BitVec (n+1)), fun s v s' => s.wgray ⊏ v ∧ s' = { s with wgray := v }⟩)
              , (↑"orc", ⟨List (Orc n), fun s v s' => s.orc ⊏ v ∧ s' = { s with orc := v }⟩)
              , (↑"mem", ⟨List (BitVec n → α), fun s v s' => s.mem ⊏ v ∧ s' = { s with mem := v }⟩)
              ].toAssocList
    outputs := [ (↑"gray", ⟨List (BitVec (n+1)), fun s v s' => s.gray_q <+: v ∧
                    RGrayF lat stl su kq P S R pw s.clk s.inc s.wgray s.orc v ∧ s' = { s with gray_q := v }⟩)
               , (↑"empty", ⟨List Bool, fun s v s' => s.empty_q <+: v ∧
                    REmptyF lat stl su kq P S R pw s.clk s.inc s.wgray s.orc v ∧ s' = { s with empty_q := v }⟩)
               , (↑"rdata", ⟨List α, fun s v s' => s.rdata_q <+: v ∧
                    RDataF lat stl su kq rdly P S R pw s.clk s.inc s.wgray s.orc s.mem v ∧ s' = { s with rdata_q := v }⟩)
               ].toAssocList
    internals := []
    init_state := fun s => s = ⟨[], [], [], [], [], [], [], []⟩ }

end Spec

/-! ## Implementation: the domain as blocks

Each block is used through its specification (`bankSpec`, `nextSpec`, `syncSpec`, `readSpec`); that each
block's own implementation meets it is proved one level down, and `TopGates.lean` substitutes
the gates in. -/

section Impl
variable (α : Type) [Inhabited α]
variable (n lat kq su stl dmin dmax ddmin ddmax P pw Rr Rc : Nat)

/-- The read domain as timed RTL blocks.  Same interface as `readDomain`. -/
def rdomGraph := [graphEnv|
    clk [type="io"];
    inc [type="io"];
    wgray [type="io"];
    orc [type="io"];
    mem [type="io"];
    gray [type="io"];
    empty [type="io"];
    rdata [type="io"];

    clkF [type="clkF", typeImp=$(⟨_, fork2 Bool⟩)];
    regs [type="ReadBank", typeImp=$(⟨_, ReadBank.bankSpec (n := n) kq su P pw Rr Rc⟩)];
    clrS [type="clearSrc", typeImp=$(⟨_, clearSrc Rc⟩)];
    next [type="ReadNext", typeImp=$(⟨_, ReadNext.nextSpec (n := n) dmin dmax⟩)];
    sync [type="SyncStage", typeImp=$(⟨_, SyncStage.syncSpec (n := n) lat su stl⟩)];
    stF [type="stF", typeImp=$(⟨_, fork2 (RSt n)⟩)];
    rdat [type="ReadPort", typeImp=$(⟨_, ReadPort.readSpec α (n := n) ddmin ddmax⟩)];

    clk -> clkF [to="in"];
    clkF -> regs [from="out1", to="clk"];
    clrS -> regs [from="crn", to="clrn"];
    clkF -> sync [from="out2", to="clk"];
    wgray -> sync [to="d"];
    orc -> sync [to="orc"];
    inc -> next [to="inc"];
    sync -> next [from="q", to="q1"];
    regs -> stF [from="st", to="in"];
    stF -> next [from="out1", to="st"];
    stF -> rdat [from="out2", to="st"];
    mem -> rdat [to="mem"];
    next -> regs [from="d", to="d"];

    regs -> gray [from="gray"];
    regs -> empty [from="empty"];
    rdat -> rdata [from="q"];
  ]

/-- The blocks of `rdomGraph`, by type name. -/
def renv := (rdomGraph α n lat kq su stl dmin dmax ddmin ddmax P pw Rr Rc).2

/-- The wiring of `rdomGraph` (independent of the parameters). -/
@[drunfold_defs]
def rdomLowered := (rdomGraph Unit 0 0 0 0 0 0 0 0 0 0 0 0 0).1.lower_TR |>.get rfl

/-- The read domain as blocks. -/
def rdomImpl := [e| rdomLowered, (renv α n lat kq su stl dmin dmax ddmin ddmax P pw Rr Rc).find? ]

end Impl

end Graphiti.AsyncFifo
