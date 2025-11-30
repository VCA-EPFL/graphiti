/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

module

public import Lean

namespace List

@[simp]
public def _root_.List.remove {α : Type _} (as : List α) (i : Fin as.length) : List α := as.eraseIdx i

public theorem perm_erase {α : Type _} [DecidableEq α] (l₁ l₂ : List α) i:
  l₁.Perm l₂ →
  (l₁.erase i).Perm (l₂.erase i) := by
  intro H; induction H generalizing i with
  | nil => simp
  | cons x l1 l2 =>
    rename_i l1' l2'
    rw [List.erase_cons]
    rw [List.erase_cons]
    split <;> simp [*]
  | swap x y l =>
    rw [List.erase_cons]
    rw [List.erase_cons]
    rw [List.erase_cons]
    rw [List.erase_cons]
    split <;> split <;> (try simp [*])
    · simp [*] at *
      rename_i H1 H2; rw [H1,H2]
    · simp [*] at *; apply List.Perm.swap
  | trans _ _ H1 H2 =>
    rename_i l₃ _ _
    apply Perm.trans; apply H1; simp [*]

end List
