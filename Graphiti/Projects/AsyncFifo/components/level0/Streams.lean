/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

/-!
# Streams and Moore machines

This file sets up the signal model used for the asynchronous FIFO, following the
methodology of Kobler's report on loopy combinational circuits:

* a discrete-time signal is a `List`, the value at time `t` being the `t`-th element
  and nothing being known beyond the end of the list;
* the information order on signals is the prefix order `<+:` (a longer list knows
  more about the future);
* a clocked block is a *Moore machine* whose output at time `t` is a function of the
  state reached after consuming the inputs at times `0, …, t-1`.  This means an
  output stream is one element longer than the (shortest) input stream, which is the
  "delay" that lets information flow around feedback loops.

Everything here is generic; the FIFO-specific parts live in `TopSpec.lean` and
`components/level2/Domains.lean`.
-/

namespace Graphiti.AsyncFifo

variable {α β S I O : Type _}

/-! ### Prefix order -/

/-- Strict information increase: a proper prefix. -/
def StrictPrefix (s₁ s₂ : List α) : Prop := s₁ <+: s₂ ∧ s₁.length < s₂.length

scoped infix:50 " ⊏ " => StrictPrefix

/-! ### Timelines and Moore machines -/

/-- A stream of length `N` given by a function of time. -/
def timeline (f : Nat → O) (N : Nat) : List O := (List.range N).map f

/-- Iterate a step function for `t` steps over the per-time inputs `inp`. -/
def run (step : S → I → S) (init : S) (inp : Nat → I) : Nat → S
  | 0 => init
  | t + 1 => step (run step init inp t) (inp t)

/-! ### Clock edges -/

/-- Rising edge of a clock signal at time `t`: the clock is high at `t` and was low at
`t - 1` (time `0` counts as a rising edge if the clock starts high). -/
def riseAt (c : List Bool) (t : Nat) : Bool :=
  c.getD t false && (t == 0 || !c.getD (t - 1) false)

/-! ### Events -/

/-- The values `vals t` at the times `t < T` where the event `ev t` fires, in time order. -/
def events (ev : Nat → Bool) (vals : Nat → α) (T : Nat) : List α :=
  (List.range T).filterMap (fun t => if ev t then some (vals t) else none)

end Graphiti.AsyncFifo
