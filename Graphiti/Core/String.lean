/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

namespace String

theorem congr_append : ∀ (a b : String), a ++ b = String.mk (a.data ++ b.data)
  | ⟨_⟩, ⟨_⟩ => rfl

theorem append_eq_left (s1 s2 s1' s2' : String) :
  s1 ++ s1' = s2 ++ s2' → s1.length = s2.length → s1 = s2 := by
  cases s1; cases s2; cases s1'; cases s2'
  intro heq hlen
  repeat rw [congr_append] at heq
  rw [String.ext_iff] at heq
  solve_by_elim [List.append_inj_left]

theorem append_neq_left (s1 s2 s1' s2' : String) :
  s1 ≠ s2 → s1.length = s2.length → s1 ++ s1' ≠ s2 ++ s2' := by
  intros; solve_by_elim [append_eq_left]

end String
