/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.Streams

/-!
# The structural invariant of a netlist, once

Every netlist in this development is proved the same way: each wire holds a prefix of whatever
drives it, and a connection rule advances one wire towards its driver.  Stated as a record with
one field per wire, that shape forces a lemma per rule, each re-establishing every field, which
is why these proofs used to be generated.

Stated over an index type it is four lemmas, none of which mention a particular circuit.  A block
supplies a wire type `W`, a driver function, and the fact that the driver is monotone; everything
below is shared.
-/

namespace Graphiti.AsyncFifo.Netlist

variable {W : Type} [DecidableEq W]

/-- An assignment of streams to wires. -/
abbrev Wires (W : Type) := W → List Bool

/-- What a netlist computes: the driver of each wire, given all the wires.  The block's own
inputs are closed over, which is what lets the lemmas below say nothing about them. -/
abbrev Drv (W : Type) := Wires W → Wires W

/-- `drv` is monotone: growing the wires grows what they drive. -/
def Mono (drv : Drv W) : Prop := ∀ {a b : Wires W}, (∀ j, a j <+: b j) → ∀ k, drv a k <+: drv b k

/-- **The invariant**: every wire holds a prefix of what drives it. -/
def Wf (drv : Drv W) (w : Wires W) : Prop := ∀ k, w k <+: drv w k

/-- One wire takes a new value, the rest stand. -/
def upd (w : Wires W) (k : W) (v : List Bool) : Wires W := fun j => if j = k then v else w j

theorem upd_ge {w : Wires W} {k v} (h1 : w k <+: v) : ∀ j, w j <+: upd w k v j := by
  intro j; by_cases hj : j = k
  · subst hj; simpa [upd] using h1
  · simp only [upd, if_neg hj]; exact List.prefix_rfl

@[simp] theorem upd_self {w : Wires W} {k v} : upd w k v k = v := by simp [upd]

theorem upd_other {w : Wires W} {k v j} (h : j ≠ k) : upd w k v j = w j := by simp [upd, h]

/-- Any step that only grows wires, and grows none past what currently drives it, preserves the
invariant. -/
theorem Wf_step {drv : Drv W} {w w' : Wires W} (mono : Mono drv)
    (hle : ∀ j, w j <+: w' j) (hd : ∀ j, w' j <+: drv w j) : Wf drv w' :=
  fun k => (hd k).trans (mono hle k)

/-- **The lemma that replaces a per-rule lemma**: the shape every connection has, one wire
advancing towards its driver while the rest stand still. -/
theorem Wf_set {drv : Drv W} {w : Wires W} (mono : Mono drv) (hw : Wf drv w) (k : W)
    (v : List Bool) (h1 : w k <+: v) (h2 : v <+: drv w k) : Wf drv (upd w k v) := by
  refine Wf_step mono (upd_ge h1) (fun j => ?_); by_cases hj : j = k
  · subst hj; simpa [upd] using h2
  · simp only [upd, if_neg hj]; exact hw j

/-- **The lemma behind every input rule**: growing an input grows every driver, so the invariant
survives.  A block instantiates this with `drv` for the old inputs and `drv'` for the new. -/
theorem Wf_drv {drv drv' : Drv W} {w : Wires W} (hw : Wf drv w)
    (h : ∀ k, drv w k <+: drv' w k) : Wf drv' w := fun k => (hw k).trans (h k)

/-- Nothing has been driven yet. -/
theorem Wf_nil {drv : Drv W} : Wf drv (fun _ => []) := fun _ => List.nil_prefix

/-- A port's value arrives from `PortMap.getIO` under an `Eq.mp` between *identical* types.
`cast_eq` will not fire on it, because the proof is not syntactically `rfl`; proof irrelevance
being definitional, this closes it.  Leaving the cast in place makes `isDefEq` unfold `getIO`
looking for a way through, which is how these proofs run out of heartbeats. -/
theorem cast_self {α : Type _} (h : α = α) (x : α) : cast h x = x := rfl

end Graphiti.AsyncFifo.Netlist
