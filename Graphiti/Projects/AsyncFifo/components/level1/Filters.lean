/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Core.Graph.ModuleLemmas
import Graphiti.Core.Graph.ModuleReduction
import Graphiti.Core.Graph.ExprHighElaborator
import Graphiti.Projects.AsyncFifo.components.level0.Streams

/-!
# The timing filters

The conditions under which the FIFO is required to behave: minimum clock periods, setup
windows on the synchronous inputs, minimum pulse widths, reset and clear.  They appear in the
specification (`TopSpec.lean`) and again, as `Contracts.GateOK`, in what a netlist of gates may
promise.  Everything else in this development is proved *under* these.
-/

namespace Graphiti.AsyncFifo

variable {α : Type} [Inhabited α]

/-- All rising edges of `c` before instant `T` are at least `P` instants apart. -/
def ClockOK (P : Nat) (c : List Bool) (T : Nat) : Prop :=
  ∀ e e', e < e' → e' < T → riseAt c e = true → riseAt c e' = true → e + P ≤ e'

/-- `x` holds its value over the `S + 1` instants ending at `e` (a setup window). -/
def StableBefore {β : Type} [Inhabited β] (S : Nat) (x : List β) (e : Nat) : Prop :=
  ∀ u, e - S ≤ u → u ≤ e → x.getD u default = x.getD e default

/-- Input-setup filter: before instant `T`, every rising edge of `clk` sees `x` stable over its
setup window. -/
def InOK {β : Type} [Inhabited β] (S : Nat) (clk : List Bool) (x : List β) (T : Nat) : Prop :=
  ∀ e, e < T → riseAt clk e = true → StableBefore S x e

/-- The clock's pulses are at least `w` instants wide: every rising edge has `w` instants of low
clock before it and `w` of high from it, as far as the stream goes.

`ClockOK` keeps rising edges `P` apart, which is all a register-level model cares about.  A
netlist cares about the pulse itself: a clock that is high for one instant in `P` satisfies
`ClockOK` while leaving a flip-flop's internal loops unresolved.  This is the filter the gate
level adds, and like the others it is a promise about the environment, not a precondition the
circuit could enforce. -/
def PulseOK (w : Nat) (clk : List Bool) (T : Nat) : Prop :=
  ∀ e, e < T → riseAt clk e = true →
    w ≤ e ∧ (∀ u, e - w ≤ u → u < e → clk.getD u false = false) ∧
    (∀ u, e ≤ u → u < e + w → u < T → clk.getD u false = true)

/-- Reset filter: no rising edge of `clk` before instant `R`.  The combinational logic of a
gate-level implementation starts from all-low outputs and needs a few instants to settle on
its initial inputs before the first edge samples it. -/
def ResetOK (R : Nat) (clk : List Bool) (T : Nat) : Prop :=
  ∀ e, e < T → riseAt clk e = true → R ≤ e

/-- Clear filter: the clear is asserted over the first `R` instants and released afterwards.
A netlist of gates has no defined state until something puts it there; this is the only filter
of the four that constrains a signal other than the clock. -/
def ClearOK (R : Nat) (crn : List Bool) (T : Nat) : Prop :=
  (∀ u, u < R → crn.getD u false = false) ∧ (∀ u, R ≤ u → u < T → crn.getD u false = true)

end Graphiti.AsyncFifo
