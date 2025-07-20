/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Lean
import Mathlib.Tactic.Common
import Batteries.Data.RBMap

open Batteries (RBMap)

namespace Graphiti

def _root_.Batteries.RBMap.modifyKeys {α β c} (map : RBMap α β c) (f : α → α) : RBMap α β c :=
  map.foldl (λ new_map k v => new_map.insert (f k) v) ∅

/--
Same as keysList, but is implemented in terms of toList, as there are more
lemmas avaiable for it.
-/
def _root_.Batteries.RBMap.keysList' {α β γ} (m : RBMap α β γ) := m.toList.map (·.1)

theorem keysInMap {α β γ} [@Batteries.OrientedCmp α γ] [@Batteries.TransCmp α γ] (m : RBMap α β γ) : ∀ k, k ∈ m.keysList' → m.contains k := by
  dsimp only [RBMap.contains, RBMap.keysList', Option.isSome]
  intro k H
  apply List.exists_of_mem_map at H
  rcases H with ⟨ ⟨ k, v ⟩, H, Heq ⟩; subst_vars
  have H' : m.findEntry? k = some (k, v) := by
    rw [Batteries.RBMap.findEntry?_some]
    solve_by_elim [Batteries.OrientedCmp.cmp_refl]
  simp [H']

theorem keysInMap' {α β γ} [BEq α] [LawfulBEq α] [Batteries.BEqCmp (α := α) γ] [@Batteries.TransCmp α γ] (m : RBMap α β γ) : ∀ k, m.contains k → k ∈ m.keysList' := by
  dsimp only [RBMap.contains, RBMap.keysList', Option.isSome]
  intro k H
  split at H <;> [skip ; simp at H]
  rename_i _ _ Hfind
  rw [Batteries.BEqCmp.cmp_iff_eq.mp (RBMap.findEntry?_some_eq_eq Hfind)]
  solve_by_elim [List.mem_map_of_mem, Batteries.RBMap.findEntry?_some_mem_toList]

theorem in_inputs {α β γ} [BEq α] [LawfulBEq α] [Batteries.BEqCmp (α := α) γ] [@Batteries.TransCmp α γ] (t : Batteries.RBMap α β γ) y ident : t.find? ident = some y → ident ∈ t.keysList' := by
  intro H; apply keysInMap'
  dsimp only [Batteries.RBMap.contains, Batteries.RBMap.find?, Option.map] at *
  split at H <;> cases H; simp [*]

end Graphiti
