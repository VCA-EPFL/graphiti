/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.components.level1.Filters
import Graphiti.Core.Graph.ModuleLemmas

/-!
# What the FIFO must do

This is one half of what you have to read.  `FifoOK` says the property: at every instant up
to which both clocks have respected their assumed minimum periods and the synchronous inputs
their setup windows, the values dequeued are a prefix of the values enqueued.  `fifoSpec` is
that property as a Graphiti module --- the right-hand side of the main theorem in
`TopRefinement.lean`.

The filters it quantifies over are in `components/level1/Filters.lean`; the streams and the
prefix order in `components/level0/Streams.lean`.
-/

namespace Graphiti.AsyncFifo

section

variable {α : Type} [Inhabited α]

/-- Enqueue event at time `t`. -/
def enqAt (wclk winc full : List Bool) (t : Nat) : Bool :=
  riseAt wclk t && winc.getD t false && !full.getD t false

/-- Dequeue event at time `t`. -/
def deqAt (rclk rinc empty : List Bool) (t : Nat) : Bool :=
  riseAt rclk t && rinc.getD t false && !empty.getD t false

/-- Values enqueued strictly before time `T`, in order. -/
def enqs (wclk winc : List Bool) (wdata : List α) (full : List Bool) (T : Nat) : List α :=
  events (enqAt wclk winc full) (fun t => wdata.getD t default) T

/-- Values dequeued strictly before time `T`, in order. -/
def deqs (rclk rinc empty : List Bool) (rdata : List α) (T : Nat) : List α :=
  events (deqAt rclk rinc empty) (fun t => rdata.getD t default) T

/-- The eight signals at the interface of the FIFO.  This is also the state of the
Graphiti specification module: the inputs it has received and the outputs it has
committed to so far. -/
structure FifoIO (α : Type) where
  wclk : List Bool
  winc : List Bool
  wdata : List α
  rclk : List Bool
  rinc : List Bool
  full : List Bool
  empty : List Bool
  rdata : List α

namespace FifoIO

/-- `T` is an instant up to which every signal is known. -/
def known (s : FifoIO α) (T : Nat) : Prop :=
  T ≤ s.wclk.length ∧ T ≤ s.winc.length ∧ T ≤ s.wdata.length ∧ T ≤ s.rclk.length ∧
  T ≤ s.rinc.length ∧ T ≤ s.full.length ∧ T ≤ s.empty.length ∧ T ≤ s.rdata.length

def enqs (s : FifoIO α) (T : Nat) : List α := AsyncFifo.enqs s.wclk s.winc s.wdata s.full T
def deqs (s : FifoIO α) (T : Nat) : List α := AsyncFifo.deqs s.rclk s.rinc s.empty s.rdata T

def empty_io : FifoIO α := ⟨[], [], [], [], [], [], [], []⟩

end FifoIO

/-- **The FIFO specification.**  At every instant up to which all signals are known and up to
which both clocks have respected their minimum periods, the dequeued values form a prefix
of the enqueued values. -/
def FifoOK (P_w P_r S_w S_r R_w R_r pw_w pw_r : Nat) (s : FifoIO α) : Prop :=
  ∀ T, s.known T → ClockOK P_w s.wclk T → ClockOK P_r s.rclk T →
    InOK S_w s.wclk s.winc T → InOK S_w s.wclk s.wdata T → InOK S_r s.rclk s.rinc T →
    ResetOK R_w s.wclk T → ResetOK R_r s.rclk T →
    PulseOK pw_w s.wclk T → PulseOK pw_r s.rclk T →
    s.deqs T <+: s.enqs T


end

section

variable (α : Type) [Inhabited α]

/-- **The specification module.**  Its state records the inputs received and the outputs
committed so far; an output may be extended (non-strictly) as long as `FifoOK` keeps holding for
the committed streams --- that is, as long as the FIFO property holds at every instant up to
which both clocks have respected their assumed minimum periods and the synchronous inputs their
setup windows. -/
def fifoSpec (P_w P_r S_w S_r R_w R_r pw_w pw_r : Nat) : StringModule (FifoIO α) :=
  { inputs := [ (↑"wclk", ⟨List Bool, fun s v s' => s.wclk ⊏ v ∧ s' = { s with wclk := v }⟩)
              , (↑"winc", ⟨List Bool, fun s v s' => s.winc ⊏ v ∧ s' = { s with winc := v }⟩)
              , (↑"wdata", ⟨List α, fun s v s' => s.wdata ⊏ v ∧ s' = { s with wdata := v }⟩)
              , (↑"rclk", ⟨List Bool, fun s v s' => s.rclk ⊏ v ∧ s' = { s with rclk := v }⟩)
              , (↑"rinc", ⟨List Bool, fun s v s' => s.rinc ⊏ v ∧ s' = { s with rinc := v }⟩)
              ].toAssocList
    outputs := [ (↑"full", ⟨List Bool, fun s v s' =>
                    s.full <+: v ∧ FifoOK P_w P_r S_w S_r R_w R_r pw_w pw_r { s with full := v } ∧ s' = { s with full := v }⟩)
               , (↑"empty", ⟨List Bool, fun s v s' =>
                    s.empty <+: v ∧ FifoOK P_w P_r S_w S_r R_w R_r pw_w pw_r { s with empty := v } ∧ s' = { s with empty := v }⟩)
               , (↑"rdata", ⟨List α, fun s v s' =>
                    s.rdata <+: v ∧ FifoOK P_w P_r S_w S_r R_w R_r pw_w pw_r { s with rdata := v } ∧ s' = { s with rdata := v }⟩)
               ].toAssocList
    internals := []
    init_state := fun s => s = FifoIO.empty_io }


end

end Graphiti.AsyncFifo
