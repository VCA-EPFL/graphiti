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

Stated over an index type it is a handful of lemmas, none of which mention a particular circuit.
A block supplies a wire type `W`, a driver function, and the fact that the driver is monotone;
everything below is shared.  A connection is `Wf_step_of` (or `Wf_set`, which is the same thing
through `upd`), an input rule is `Wf_drv` followed by `Wf_congr`, and nothing else is needed.
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

/-- Any step that only grows wires, and grows none past what currently drives it, preserves the
invariant. -/
theorem Wf_step {drv : Drv W} {w w' : Wires W} (mono : Mono drv)
    (hle : ∀ j, w j <+: w' j) (hd : ∀ j, w' j <+: drv w j) : Wf drv w' :=
  fun k => (hd k).trans (mono hle k)

/-- `Wf_step` with the starting assignment pinned by the invariant the block already has.
Without `_hw`, `w` is a metavariable the two pointwise arguments have to determine, and the
elaborator spends its heartbeats guessing it. -/
theorem Wf_step_of {drv : Drv W} {w w' : Wires W} (_hw : Wf drv w) (mono : Mono drv)
    (hle : ∀ j, w j <+: w' j) (hd : ∀ j, w' j <+: drv w j) : Wf drv w' :=
  Wf_step mono hle hd

/-- **The lemma that replaces a per-rule lemma**: the shape every connection has, one wire
advancing towards its driver while the rest stand still. -/
theorem Wf_set {drv : Drv W} {w : Wires W} (mono : Mono drv) (hw : Wf drv w) (k : W)
    (v : List Bool) (h1 : w k <+: v) (h2 : v <+: drv w k) : Wf drv (upd w k v) := by
  refine Wf_step mono (upd_ge h1) (fun j => ?_); by_cases hj : j = k
  · subst hj; simpa [upd] using h2
  · simp only [upd, if_neg hj]; exact hw j

/-! A rule of thumb these blocks were built on, and the reason for `Wf_congr` below.  When a
proof hands the kernel a fact about one assignment where the goal names another, the kernel
compares the two *applications*; when the fact is handed over one wire, or one argument, at a
time, it compares the *arguments*.  The first is what runs out of heartbeats on a large block --
it unfolds `wires` over the whole state tuple, or a combinational output over the nested `min`s
in its length.  The second is a `cases`.  The same rule decides where a `first | exact …`
alternative may be offered: an alternative whose expected type is a deep definition makes the
unifier unfold it looking for a way through, so the deep cases are named instead. -/

/-- The invariant carried across a rule that leaves every wire alone.  `Wf_drv` already does
this, but it hands back the invariant for the *old* assignment, and the goal names the new one;
letting the kernel see those two are the same means comparing `wires i` with `wires mid` as
whole functions, which is where a 35-wire block runs out of heartbeats.  Wire by wire, it is
two `cases`. -/
theorem Wf_congr {drv : Drv W} (mono : Mono drv) {w w' : Wires W} (hw : Wf drv w)
    (hle : ∀ j, w' j <+: w j) (hge : ∀ j, w j <+: w' j) : Wf drv w' :=
  fun k => (hle k).trans ((hw k).trans (mono hge k))

/-- **The lemma behind every input rule**: growing an input grows every driver, so the invariant
survives.  A block instantiates this with `drv` for the old inputs and `drv'` for the new. -/
theorem Wf_drv {drv drv' : Drv W} {w : Wires W} (hw : Wf drv w)
    (h : ∀ k, drv w k <+: drv' w k) : Wf drv' w := fun k => (hw k).trans (h k)

/-- A port's value arrives from `PortMap.getIO` under an `Eq.mp` between *identical* types.
`cast_eq` will not fire on it, because the proof is not syntactically `rfl`; proof irrelevance
being definitional, this closes it.  Leaving the cast in place makes `isDefEq` unfold `getIO`
looking for a way through, which is how these proofs run out of heartbeats. -/
theorem cast_self {α : Type _} (h : α = α) (x : α) : cast h x = x := rfl

/-! ### Wires that carry more than a bit

A gate's wire carries `Bool`, but an assembly's wires carry buses -- `List (WSt 2)`,
`List (BitVec 3)` -- so `Sync`, `Bank` and `BankR` do not fit the definitions above.  Indexing
what each wire carries fixes that.

There is deliberately no `upd` here.  Building one would need a dependent `if` to cast between
`List (Ty j)` and `List (Ty k)`, and using it would force each step to prove two assignments
equal.  `step` asks instead for two pointwise facts about the assignment the module already
has -- which is `Wf_step_of` above, and is what the homogeneous blocks use too.  `upd` and
`Wf_set` stay because `BusReg`, `StReg`, `StRegR` and `ReadMux` are written against them and
are fast enough; on `Dff` the two shapes measure within 15% of each other. -/

namespace Het

variable {W : Type} {Ty : W → Type}

/-- What each wire carries, wire by wire. -/
abbrev Wires (Ty : W → Type) := (k : W) → List (Ty k)

/-- The driver of each wire, given all the wires. -/
abbrev Drv (Ty : W → Type) := Wires Ty → Wires Ty

/-- Growing the wires grows what they drive. -/
def Mono (drv : Drv Ty) : Prop :=
  ∀ {a b : Wires Ty}, (∀ j, a j <+: b j) → ∀ k, drv a k <+: drv b k

/-- Every wire holds a prefix of what drives it. -/
def Wf (drv : Drv Ty) (w : Wires Ty) : Prop := ∀ k, w k <+: drv w k

/-- **The lemma that replaces every per-rule lemma.**  `_hw` is unused; it pins `w` to the
assignment the block started from, which the two pointwise arguments are stated against. -/
theorem step {drv : Drv Ty} {w w' : Wires Ty} (_hw : Wf drv w) (mono : Mono drv)
    (hle : ∀ j, w j <+: w' j) (hd : ∀ j, w' j <+: drv w j) : Wf drv w' :=
  fun k => (hd k).trans (mono hle k)

/-- **The lemma behind every input rule**: growing an input grows every driver. -/
theorem drv_le {drv drv' : Drv Ty} {w : Wires Ty} (hw : Wf drv w)
    (h : ∀ k, drv w k <+: drv' w k) : Wf drv' w := fun k => (hw k).trans (h k)

end Het

end Graphiti.AsyncFifo.Netlist
