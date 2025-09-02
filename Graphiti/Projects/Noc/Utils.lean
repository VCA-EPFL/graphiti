/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Gurvan Debaussart
-/

-- A bunch of random stuff which doesn't quite fit with the rest

import Graphiti.Core.Module
import Graphiti.Core.ModuleLemmas
import Graphiti.Core.Component

open Batteries (AssocList)

namespace Graphiti.Projects.Noc

  @[simp] abbrev typeOf {α} (_ : α) := α

  -- fin_range -----------------------------------------------------------------

  def lift_fin {sz : Nat} (n : Fin sz) : Fin (sz + 1) :=
    ⟨n.1 + 1, by simp only [Nat.add_lt_add_iff_right, Fin.is_lt] ⟩

  def fin_range (sz : Nat) : List (Fin sz) :=
    match sz with
    | 0 => []
    | sz' + 1 => ⟨0, Nat.zero_lt_succ _⟩ :: (fin_range sz').map lift_fin

  def fin_range' (sz : Nat) : List (Fin sz) :=
    List.replicate sz 0
    |>.mapFinIdx (λ i _ h => ⟨i, by rwa [List.length_replicate] at h⟩)

  theorem map_mapFinIdx {α β δ} (l : List α) (f : (i : Nat) → α → (h : i < l.length) → β) (g : β → δ) :
    (l.mapFinIdx f).map g = l.mapFinIdx (λ i v h => g (f i v h)) := by
      revert f g
      induction l with
      | nil => intros _ _; rfl
      | cons hd tl HR =>
        intro f g
        simp only [List.mapFinIdx_cons, List.map_cons, HR, List.length_cons]

  theorem fin_range_eq {sz : Nat} :
    fin_range sz = fin_range' sz := by
      induction sz with
      | zero => rfl
      | succ n HR =>
        dsimp [fin_range]; rw [HR]; dsimp [fin_range']
        simp only [
          List.replicate, List.length_cons, List.mapFinIdx_cons, Fin.zero_eta,
          map_mapFinIdx, lift_fin
        ]

  theorem fin_in_fin_range' (sz : Nat) (i : Fin sz) : i ∈ fin_range' sz := by
    simp only [fin_range', List.mem_mapFinIdx, List.length_replicate]
    exists i.1, i.2

  theorem fin_in_fin_range (sz : Nat) (i : Fin sz) : i ∈ fin_range sz := by
    rw [fin_range_eq]; exact fin_in_fin_range' sz i

  theorem fin_range_len (sz : Nat) :
    (fin_range sz).length = sz := by
      induction sz with
      | zero => rfl
      | succ sz HR => simpa [fin_range, HR]

  def fin_range_len_cast {sz : Nat} : Fin (fin_range sz).length = Fin sz :=
    by rw [fin_range_len]

  def fin_conv {sz : Nat} (i : Fin (fin_range sz).length) : Fin sz :=
    ⟨i.1, by cases i; rename_i v h; rw [fin_range_len] at h; simpa only⟩

  def fin_conv' {sz : Nat} (i : Fin sz) : Fin (fin_range sz).length :=
    ⟨i.1, by rw [fin_range_len]; cases i; assumption⟩

  theorem fin_conv_conv {sz : Nat} (i : Fin (fin_range sz).length) :
    fin_conv' (fin_conv i) = i := by rfl

  theorem fin_conv_conv' {sz : Nat} (i : Fin sz) :
    fin_conv (fin_conv' i) = i := by rfl

  theorem mapFinIdx_length {α β} (l : List α) (f : (i : Nat) → α → (h : i < l.length) → β) :
    (List.mapFinIdx l f).length = l.length := by
      simpa only [List.length_mapFinIdx]

  theorem mapFinIdx_get {α β} (l : List α) (f : (i : Nat) → α → (h : i < l.length) → β) (i : Fin (List.mapFinIdx l f).length) :
    (List.mapFinIdx l f).get i = f i l[i] (by rw [←mapFinIdx_length l f]; exact i.2) := by
      simpa

  theorem fin_range_get {sz : Nat} {i : Fin (fin_range sz).length} :
    (fin_range sz).get i = fin_conv i := by
    -- rw [fin_range_eq]
    -- dsimp [fin_range]
    -- apply mapFinIdx_get
    sorry

  theorem fin_cast {sz sz' : Nat} (h : sz = sz' := by rfl) :
    Fin sz = Fin sz' := by subst h; rfl

  -- RelIO ---------------------------------------------------------------------

  @[simp] abbrev RelIO (S : Type) := Σ T : Type, S → T → S → Prop

  def RelIO.liftFinf {α : Type _} (n : Nat) (f : Fin n → α) : PortMap Nat α :=
    fin_range n |>.map (λ i => ⟨↑i.toNat, f i⟩) |>.toAssocList

  theorem RelIO.liftFinf_in {S} {ident : InternalPort Nat} {n : Nat} {f : Fin n → RelIO S}:
    AssocList.contains ident (RelIO.liftFinf n f) = true
    → ∃ i : Fin n, ident = i := by
        -- dsimp [liftFinf, fin_range]
        -- simp only [
        --   AssocList.contains_eq, List.toList_toAssocList, List.any_map,
        --   List.any_eq_true, List.mem_mapFinIdx, List.length_replicate,
        --   Function.comp_apply, beq_iff_eq, forall_exists_index, and_imp
        -- ]
        -- intros x1 x2 H1 H2 H3
        -- subst ident
        -- exists x1
        sorry

  theorem RelIO.liftFinf_get {S} {n : Nat} {i : Fin n} {f : Fin n → RelIO S}:
    (RelIO.liftFinf n f).getIO i = f i := by sorry

  theorem RelIO.mapVal {α β} {n : Nat} {f : Fin n → α} {g : α → β} :
    AssocList.mapVal (λ _ => g) (RelIO.liftFinf n f) = RelIO.liftFinf n (λ i => g (f i)) := by
      -- dsimp [RelIO.liftFinf, fin_range]
      -- rw [AssocList.mapVal_map_toAssocList]
      sorry

  -- RelInt --------------------------------------------------------------------

  def RelInt.liftFinf {S : Type} (n : Nat) (f : Fin n → List (RelInt S)) : List (RelInt S) :=
    fin_range n |>.map f |>.flatten

  theorem RelInt.liftFinf_in {S} {rule : RelInt S} {n : Nat} {f : Fin n → List (RelInt S)}:
    -- TODO: This is probably an equivalence too
    rule ∈ (RelInt.liftFinf n f)
    → ∃ (i : Fin n) (j : Fin (f i).length), rule = (f i).get j := by sorry

  theorem RelInt.liftFinf_in' {S} {rule : RelInt S} {n : Nat} {f : Fin n → List (RelInt S)}:
    (∃ (i : Fin n) (j : Fin (f i).length), rule = (f i).get j) →
    rule ∈ (RelInt.liftFinf n f) := by
      intro ⟨i, j, Hij⟩
      rw [Hij]
      unfold liftFinf
      simp only [RelInt, List.get_eq_getElem, List.mem_flatten, List.mem_map]
      exists (f i)
      sorry
      -- and_intros
      -- · exists i; and_intros
      --   · apply fin_in_fin_range
      --   · rfl
      -- · simpa

  -- Some stuff about permutations ---------------------------------------------

  theorem in_list_idx {α} {l : List α} {x : α} (H : x ∈ l) :
    ∃ i : Fin (List.length l), l[i] = x := by
      induction l with
      | nil => contradiction
      | cons hd tl HR =>
        rw [List.mem_cons] at H
        cases H <;> rename_i H
        · subst x; apply Exists.intro ⟨0, by simpa⟩; rfl
        · obtain ⟨i, Hi'⟩ := HR H; exists ⟨i + 1, by simpa⟩

  variable {α} {n : Nat}

  theorem vec_in_if_idx {v : Vector α n} {x : α} (hin : x ∈ v) :
     ∃ i : Fin n, v[i] = x := by sorry

  theorem idx_in_vec {v : Vector α n} {x : α} (hidx : ∃ i : Fin n, v[i] = x) :
     x ∈ v := by sorry

  theorem vec_set_concat_perm {v : Vector (List α) n} {idx : Fin n} {l : List α} {elt : α} :
    v.toList.flatten.Perm l →
    (v.set idx (v[idx] ++ [elt])).toList.flatten.Perm (l ++ [elt]) := by
      sorry

  theorem vec_set_map {α β} {v : Vector α n} {idx : Fin n} {elt : α}
    {f : (idx : Nat) → α → (idx < n) → β} :
    (v.set idx elt).mapFinIdx f = (v.mapFinIdx f).set idx (f idx.1 elt idx.2) := by
      sorry

  theorem vec_set_toList {v : Vector α n} {idx : Fin n} {elt : α} :
    (v.set idx elt).toList = v.toList.set idx elt := by
      sorry

  theorem list_set_flatten {l : List (List α)} {l1 : List α} {elt : α}
    {idx : Nat} {hidx : idx < l.length}  :
    (l.set idx (l1 ++ [elt])).flatten
    = (l.set idx l1).flatten.insertIdx (idx + List.length l1) elt := by
    induction l with
    | nil => contradiction
    | cons hd tl HR => sorry

  theorem list_Perm_insertIdx {l1 l2 : List α} {hPerm : l1.Perm l2} {idx1 idx2
  : Nat} {hidx1 : idx1 <= l1.length} {hidx2 : idx2 <= l2.length} {elt : α} :
    (l1.insertIdx idx1 elt).Perm (l2.insertIdx idx2 elt) := by sorry

  theorem list_map_eraseIdx {α β} {l : List α} {idx : Fin l.length} {f : α → β} :
    (l.eraseIdx idx).map f = (l.map f).eraseIdx idx := by
      induction l with
      | nil => rfl
      | cons hd tl HR =>
        simp
        cases heq: idx.toNat with
        | zero => simp at heq; subst idx; simpa
        | succ idx' =>
            obtain ⟨idxv, idxh⟩ := idx
            simp only [List.length_cons, Fin.toNat_eq_val] at heq
            simp only [heq, List.eraseIdx_cons_succ, List.map_cons, List.cons.injEq, true_and]
            rw [heq] at idxh
            simp only [List.length_cons, Nat.add_lt_add_iff_right] at idxh
            exact @HR ⟨idx', idxh⟩

  theorem list_set_eraseIdx {l : List (List α)} {l1 : List α}
    {idx idx1 : Nat}  {hidx : idx < l.length} {hidx1 : idx1 < l1.length} :
    ∃ idx' : Fin (l.set idx l1).flatten.length,
      (l.set idx (l1.eraseIdx idx1)).flatten = (l.set idx l1).flatten.eraseIdx idx'
      ∧ l1[idx1] = (l.set idx l1).flatten[idx']
      := by sorry

  theorem list_Perm_eraseIdx {l1 l2 : List α} {idx1 idx2 : Nat} {hidx1 : idx1 <
  l1.length} {hidx2 : idx2 < l2.length} {heq : l1[idx1] = l2[idx2]} {hperm :
  l1.Perm l2} :
    (l1.eraseIdx idx1).Perm (l2.eraseIdx idx2) := by sorry

  theorem vec_set_concat_in {v : Vector (List α) n} {idx : Fin n} {l : List α} {elt : α} :
    v.toList.flatten ⊆ l →
    (v.set idx (v[idx] ++ [elt])).toList.flatten ⊆ (l ++ [elt]) := by
      intros H x Hx
      simp only [Fin.getElem_fin, List.mem_flatten, Vector.mem_toList_iff] at Hx
      obtain ⟨l', Hl1, Hl2⟩ := Hx
      sorry

  theorem vec_set_subset_in {v : Vector (List α) n} {idx : Fin n} {l : List α} {elt : α} :
    (v.set idx (elt :: v[↑idx])).toList.flatten ⊆ l →
    ∃ idx' : Fin (List.length l), l[idx'] = elt := by
      intros H
      apply in_list_idx
      apply H
      rw [List.mem_flatten]
      apply Exists.intro (elt :: v[↑idx])
      simpa [Vector.mem_set]

  theorem vec_set_in (v : Vector (List α) n) (idx : Fin n) (elt : α) :
    elt ∈ (Vector.set v idx (elt :: v[idx]))[idx] := by simpa

  theorem vec_set_in_flatten (v : Vector (List α) n) (idx : Fin n) (elt : α) :
    elt ∈ (Vector.set v idx (elt :: v[↑idx])).toList.flatten := by
      simp only [Fin.getElem_fin, List.mem_flatten, Vector.mem_toList_iff]
      exists (elt :: v[↑idx])
      and_intros <;> simpa [Vector.mem_set]

  theorem vec_set_subset {v : Vector (List α) n} {idx : Fin n} {l : List α} {elt : α} :
    (v.set idx (elt :: v[idx])).toList.flatten ⊆ l →
    ∃ idx' : Fin (List.length l), l[idx'] = elt := by
      intros H
      specialize H (vec_set_in_flatten v idx elt)
      rw [List.mem_iff_get] at H
      obtain ⟨n, Hn⟩ := H
      exists n

  theorem vec_set_subset' {v : Vector (List α) n} {idx : Fin n} {l : List α} {elt : α} :
    (v.set idx (elt :: v[idx]))[idx] ⊆ l →
    ∃ idx' : Fin (List.length l), l[idx'] = elt := by
      intros H
      specialize H (vec_set_in v idx elt)
      rw [List.mem_iff_get] at H
      obtain ⟨n, Hn⟩ := H
      exists n

  theorem vec_set_cons_perm {v : Vector (List α) n} {idx1 idx2 : Fin n} {elt : α} :
    (Vector.set v idx1 (elt :: v[idx1])).toList.flatten.Perm
    (Vector.set v idx2 (v[idx2] ++ [elt])).toList.flatten := by sorry

  theorem vec_set_cons_in {v : Vector (List α) n} {idx1 idx2 : Fin n} {elt : α} :
    (Vector.set v idx1 (v[idx1] ++ [elt])).toList.flatten ⊆
    (Vector.set v idx2 (elt :: v[idx2])).toList.flatten := by
      intros x Hx
      simp only [Fin.getElem_fin, List.mem_flatten, Vector.mem_toList_iff] at ⊢ Hx
      obtain ⟨l, Hl1, Hl2⟩ := Hx
      sorry

  theorem vec_set_cons_remove_in {v : Vector (List α) n} {idx1 : Fin n} {l} {idx2 : Fin (List.length l)} {elt : α} :
    l[idx2] = elt →
    (v.set idx1 (elt :: v[idx1])).toList.flatten ⊆ l →
    v.toList.flatten ⊆ (l.remove idx2) := by
      intros H1 H2 x Hx
      sorry

    theorem vec_point_eq {v1 v2 : Vector α n} :
      (∀ (idx : Fin n), v1[↑idx] = v2[↑idx]) → v1 = v2 := by
        intros h
        obtain ⟨⟨l1⟩, sz1⟩ := v1
        obtain ⟨⟨l2⟩, sz2⟩ := v2
        congr
        dsimp at h
        dsimp [Array.size] at sz1 sz2
        induction l1 generalizing n l2 with
        | nil =>
          induction l2 with
          | nil => rfl
          | cons hd2 tl2 HR2 => rw [←sz1] at sz2; contradiction
        | cons hd1 tl1 HR1 =>
          induction l2 with
          | nil => rw [←sz1] at sz2; contradiction
          | cons hd2 tl2 HR2 =>
            congr
            · apply h ⟨0, by simpa [←sz2]⟩
            · apply @HR1 (n - 1)
              · intros idx
                obtain ⟨idxv, idxh⟩ := idx
                let idx' : Fin n := ⟨idxv + 1, by sorry⟩
                specialize h idx'
                simp only [List.getElem_cons_succ, idx'] at h
                exact h
              · simpa [←sz1]
              · simpa [←sz2]

   theorem vec_set_reconstruct {v v' : Vector α n} {idx : Fin n} {f : α → α} :
      (∀ idx' : Fin n, ¬(idx = idx') → v'[↑idx'] = v[↑idx']) →
      v'[↑idx] = f v[↑idx] →
      v' = v.set idx (f v[↑idx])
      := by
        intros H1 H2
        apply vec_point_eq
        intros idx'
        by_cases heq: ↑idx' = ↑idx
        · subst idx'
          simp only [Fin.getElem_fin, Vector.getElem_set_self]
          assumption
        · dsimp [Fin.getElem_fin]
          rw [Vector.getElem_set_ne]
          · apply H1
            intro h
            apply heq
            rw [h]
          · simp
            intros h
            apply heq
            cases idx; cases idx'; simp at heq h <;> simp [h]

    theorem list_perm_in {l1 l2 : List α} (hPerm : l1.Perm l2) :
      ∀ x, x ∈ l1 → x ∈ l2 := by
        sorry

     theorem perm_eraseIdx {l1 l2 : List α} {hPerm : l1.Perm l2}
      {idx1 : Fin l1.length} {idx2 : Fin l2.length} :
      l1[idx1] = l2[idx2] → (l1.eraseIdx idx1).Perm (l2.eraseIdx idx2)
      := by
        revert idx1 idx2
        induction hPerm with
        | nil => intro ⟨_, _⟩; contradiction
        | cons x l1 l2 => sorry
        | swap x y l => sorry
        | trans _ _ H1 H2 => sorry

    theorem list_mem_concat_either {α} {elt : α} {l1 l2 : List α} :
      List.Mem elt (l1 ++ l2) → List.Mem elt l1 ∨ List.Mem elt l2 := by
        induction l1 with
        | nil => dsimp; intro h; right; assumption
        | cons hd tl HR =>
          dsimp
          by_cases Heq: hd = elt
          · subst hd; intro h; left; constructor
          · intro h; cases h
            · contradiction
            · rename_i Hmem; specialize HR Hmem; cases HR
              · left; apply List.Mem.tail; assumption
              · right; assumption

    theorem list_mem_concat_either' {α} {elt : α} {l1 l2 : List α} :
      List.Mem elt l1 ∨ List.Mem elt l2 → List.Mem elt (l1 ++ l2) := by
        intro h;
        cases h
        · induction l1
          · contradiction
          · rename_i hd tl HR H
            cases H
            · constructor
            · rename_i H
              apply List.Mem.tail _ (HR H)
        · sorry

    theorem list_mem_concat_false {α} {elt1 elt2 : α} {l: List α} :
      ¬elt1 = elt2 → List.Mem elt1 (l ++ [elt2]) → List.Mem elt1 l := by
        intro H1 H2
        cases list_mem_concat_either H2
        · assumption
        · rename_i h
          cases h <;> contradiction

    theorem list_mem_eraseIdx {α} {elt : α} {l: List α} {idx}:
      List.Mem elt (l.eraseIdx idx) → List.Mem elt l := by sorry

  section DPList

    variable {α : Type _}

    abbrev DPList'.{u} (acc : Type u) (l : List α) (f : α → Type u) :=
      List.foldr (λ i acc => f i × acc) acc l

    abbrev DPList := @DPList' α Unit

    theorem DPList_zero {f : α → Type _} :
      DPList [] f = Unit := by rfl

    theorem DPList_succ' {hd : α} {tl : List α} {acc : Type _} {f : α → Type _} :
      DPList' acc (hd :: tl) f = (f hd × (DPList' acc tl f)) := by
        rfl

    theorem DPList_succ {hd : α} {tl : List α} {f : α → Type _} :
      DPList (hd :: tl) f = (f hd × (DPList tl f)) := by
        rfl

    theorem DPList.mk_cast {l : List α} {f : α → Type _} {g : (i : α) → f i} :
      (List.foldr (λ i acc => (⟨f i × acc.1, (g i, acc.2)⟩: Σ T, T)) ⟨Unit, ()⟩ l).fst
    = DPList l f := by
      induction l with
      | nil => rfl
      | cons hd tl HR => simpa only [List.foldr_cons, HR]

    def DPList.mk (l : List α) (f : α → Type _) (g : (i : α) → f i) : DPList l f :=
      Module.dep_foldr_1.mp
        (List.foldr
          (λ i acc => (⟨f i × acc.1, (g i, acc.2)⟩ : Σ T, T))
          ⟨Unit, ()⟩ l
        ).snd

    def DPList.get' {l : List α} {f} (pl : DPList l f) (i : Nat) (h : i < List.length l) : f (l.get ⟨i, h⟩) :=
      match l with
      | [] => by contradiction
      | hd :: tl =>
        have pl' := DPList_succ.mp pl
        match i with
        | 0 => pl'.1
        | i' + 1 => pl'.2.get' i' (by simp only [List.length_cons, Nat.add_lt_add_iff_right] at h; exact h)

    def DPList.get {l : List α} {f} (pl : DPList l f) (i : Fin (List.length l)) : f (l.get i) :=
      DPList.get' pl i.1 i.2

  end DPList

  -- dep_foldr but for Σ'
  section dep_foldr'

    universe u1 u2 u3
    variable {Ident}
    variable {α : Type u1}
    variable {β : Sort u2 → Sort (u3 + 1)}

    @[simp]
    abbrev dep_foldr'
      (f : α → Sort u2 → Sort u2)
      (g : (i : α) → (acc : Σ' (S : Sort u2), β S) → β (f i acc.1))
      (acc : Σ' (S : Sort u2), β S) (l : List α)
      : Σ' (S : Sort u2), β S :=
      List.foldr (λ i acc => ⟨f i acc.1, g i acc⟩) acc l

    theorem dep_foldr_1' {acc} {l} {f : α → Sort _ → Sort _} {g : (i : α) → (acc : Σ' S, β S) → β (f i acc.1)} :
      (dep_foldr' f g acc l).1 = List.foldr f acc.1 l := by
        induction l generalizing acc with
        | nil => rfl
        | cons x xs ih => dsimp [dep_foldr']; rw [ih]

    theorem dep_foldr_β' {acc l} {f : α → Sort _ → Sort _} {g : (i : α) → (acc : Σ' S, β S) → β (f i acc.1)} :
      β (dep_foldr' f g acc l).1 = β (List.foldr f acc.1 l) := by
        rw [dep_foldr_1']

  end dep_foldr'

  section arith

    theorem mul_add_one (x y) : x * (y + 1) = x + x * y := by
      simpa [Nat.mul_add, Nat.add_comm]

    theorem add_mul {n x y : Nat} (hltx : x < n) (hlty : y < n) : x * n + y < n * n := by
      induction n generalizing x y with
      | zero => contradiction
      | succ n hr =>
        rw [mul_add_one, mul_add_one]
        rw (occs := [2]) [Nat.mul_comm]
        rw [mul_add_one]
        sorry

  end arith

  section portmap

  end portmap

end Graphiti.Projects.Noc
