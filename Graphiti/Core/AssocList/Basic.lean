/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Batteries.Data.AssocList

import Graphiti.Core.Simp

namespace Batteries.AssocList

deriving instance DecidableEq for AssocList
deriving instance Repr for AssocList

def append {α β} (a b : AssocList α β) : AssocList α β :=
  match a with
  | .nil => b
  | .cons x y xs =>
    .cons x y <| xs.append b

instance {α β} : Append (AssocList α β) := ⟨ append ⟩

@[simp, drcompute] theorem nil_append {α β} (as : AssocList α β) : .nil ++ as = as := rfl
@[simp, drcompute] theorem cons_append {α β} {a : α} {a' : β} {as bs : AssocList α β} : (.cons a a' as) ++ bs = .cons a a' (as ++ bs) := rfl
@[simp, drcompute] theorem lift_append {α β} (as bs : AssocList α β) : as.append bs = as ++ bs := rfl

@[specialize, simp] def eraseAllP {α β} (p : α → β → Bool) : AssocList α β → AssocList α β
  | nil         => nil
  | cons k v es => bif p k v then eraseAllP p es else cons k v (eraseAllP p es)

def concat {α β} (a : α) (b : β) (m : AssocList α β) :=
  m ++ AssocList.nil.cons a b

@[specialize] def eraseAllP_TR {α β} (p : α → β → Bool) (m : AssocList α β) : AssocList α β :=
  go .nil m
  where
    go (rst : AssocList α β)
    | .nil => rst
    | .cons k v xs =>
      bif p k v then go rst xs else go (rst.concat k v) xs

@[inline] def containsVal {α β} [BEq β] (a : β) (l : AssocList α β) : Bool := any (fun _ k => k == a) l

@[inline] def eraseAllVal {α β} [BEq β] (a : β) (l : AssocList α β) : AssocList α β := eraseAllP (fun _ k => k == a) l

/-- `O(n)`. Remove the first entry in the list with key equal to `a`. -/
@[inline] def eraseAll {α β} [BEq α] (a : α) (l : AssocList α β) : AssocList α β :=
  eraseAllP_TR (fun k _ => k == a) l

/-- `O(n)`. Map a function `f` over the values of the list. -/
@[simp] def map {α β δ γ} (f : α → β → δ × γ) : AssocList α β → AssocList δ γ
  | nil        => nil
  | cons k v t => let (k', v') := f k v; cons k' v' (map f t)

def keysList {α β} (map : AssocList α β) : List α :=
  map.toList.map (·.fst)

def valsList {α β} (map : AssocList α β) : List β :=
  map.toList.map (·.snd)

def disjoint_keys {α β γ} [DecidableEq α] (a : AssocList α β) (b : AssocList α γ) : Bool :=
  a.keysList.inter b.keysList = []

def disjoint_vals {α β γ} [DecidableEq γ] (a : AssocList α γ) (b : AssocList β γ) : Bool :=
  a.valsList.inter b.valsList = []

def filter {α β} (f : α → β → Bool) (l : AssocList α β) :=
  l.foldl (λ c a b => if f a b then c.concat a b else c) (∅ : AssocList α β)

def mem {α β} [BEq α] (a : α) (b : β) (l : AssocList α β) : Prop :=
  l.find? a = some b

def flatten {α β} (l : List (AssocList α β)): AssocList α β :=
  match l with
  | .nil        => .nil
  | .cons hd tl => hd.append (flatten tl)

def inverse {α β} : AssocList α β → AssocList β α
| .nil => .nil
| .cons a b xs => xs.inverse |>.cons b a

def beq_left_ooo {α β} [DecidableEq α] [DecidableEq β] (a b : AssocList α β) : Bool :=
  a.keysList.all (λ k => a.find? k == b.find? k)

def beq_ooo {α β} [DecidableEq α] [DecidableEq β] (a b : AssocList α β) : Bool :=
  beq_left_ooo a b ∧ beq_left_ooo b a

def filterId {α} [DecidableEq α] (p : AssocList α α) : AssocList α α :=
  p.filter (λ a b => a ≠ b)

def subsetOf {α β} [DecidableEq α] (a b : AssocList α β) : Prop :=
  ∀ i v, a.find? i = .some v → b.find? i = .some v

def EqExt {α β} [DecidableEq α] (a b : AssocList α β) : Prop :=
  -- a.subsetOf b ∧ b.subsetOf a
  ∀ i, a.find? i = b.find? i

theorem EqExt.refl {α β} [DecidableEq α] (a : AssocList α β) : a.EqExt a := by simp [EqExt]
theorem EqExt.symm {α β} [DecidableEq α] {b a : AssocList α β} : a.EqExt b → b.EqExt a := by simp +contextual [EqExt]
theorem EqExt.trans {α β} [DecidableEq α] {a b c : AssocList α β} : a.EqExt b → b.EqExt c → a.EqExt c := by
  simp +contextual [EqExt]

instance AssocListExtSetoid {α β} [DecidableEq α] : Setoid (AssocList α β) :=
  ⟨EqExt, ⟨EqExt.refl, EqExt.symm, EqExt.trans⟩⟩

def wf {α β} (a : AssocList α β) : Prop := a.keysList.Nodup

def invertible_efficient {α} [DecidableEq α] (p : AssocList α α) : Bool := true

-- @[implemented_by invertible_efficient]
def invertible {α} [DecidableEq α] (p : AssocList α α) : Bool :=
  p.filterId.keysList.inter p.inverse.filterId.keysList = ∅ ∧ p.keysList.Nodup ∧ p.inverse.keysList.Nodup

/--
Just like bijectivePortRenaming, but pushes the function generation into the definition.  This doesn't seem to make a
big difference.
-/
def bijectivePortRenaming_quick {α} [DecidableEq α] (p : AssocList α α) : α → α :=
  if p.invertible then
    let map := p.filterId.append p.inverse.filterId
    fun i => map.find? i |>.getD i
  else id

-- @[implemented_by bijectivePortRenaming]
def bijectivePortRenaming {α} [DecidableEq α] (p : AssocList α α) (i : α) : α :=
  if p.invertible then
    let map := p.filterId.append p.inverse.filterId
    map.find? i |>.getD i
  else i

@[simp] def mapKey' {α β δ} (f : α → β → δ) : AssocList α β → AssocList δ β
  | nil        => nil
  | cons k v t => cons (f k v) v (mapKey' f t)

def squash {α β} [DecidableEq α] (a : AssocList α β) : AssocList α β → AssocList α β
| nil => a
| cons k v t => if a.contains k then squash a t else cons k v (squash a t)

end Batteries.AssocList
