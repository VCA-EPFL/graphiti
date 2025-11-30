/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

module

@[expose] public section

namespace Graphiti

/--
Create a class for an arbitrary state transition system.
-/
class StateTransition (State : Type _) (Event : outParam (Type _)) where
  init : State → Prop
  step : State → List Event → State → Prop

/--
These are notations, which allow you to have nicer syntax when you write
theorems.  We don't have to use them though, so below I've just left it as
normal function syntax.
-/
notation:45 s " -[ " t:45 " ]-> " s':44 => StateTransition.step s t s'

section Behaviour

variable {State Event : Type _}
variable [trans: StateTransition State Event]

inductive star : State → List Event → State → Prop where
  | refl : ∀ s1, star s1 [] s1
  | step : ∀ s1 s2 s3 e1 e2, trans.step s1 e1 s2 → star s2 e2 s3 → star s1 (e1 ++ e2) s3

notation:45 s " -[ " t:45 " ]*> " s':44 => star s t s'

def behaviour (l : List Event) : Prop :=
  ∃ s s', trans.init s ∧ star s l s'

def reachable (l : List Event) (s' : State) : Prop :=
  ∃ s, trans.init s ∧ star s l s'

def future (s : State) (t : List Event) : Prop :=
  ∃ s', s -[ t ]*> s'

def liveness_refine {S I Event} (ST_S : StateTransition S Event) (ST_I : StateTransition I Event) : Prop :=
  ∀ (l : List Event) (i : I) (s : S),
  reachable l i → reachable l s → ∀ l', future s l' → future i l'

theorem star.plus_one (s s' : State) (e : List Event) :
    s -[e]-> s' → s -[e]*> s' := by
  intros Hstep
  have He : e = e ++ [] := by simp
  rw [He]
  apply star.step <;> first | assumption | apply star.refl

theorem step_internal (s1 s2 s3 : State) e2 :
  s1 -[[]]-> s2 → s2 -[e2]*> s3 → s1 -[e2]*> s3 := by
  have h : e2 = [] ++ e2 := by rfl
  intros; rw [h]
  apply star.step <;> assumption

@[deprecated star.plus_one (since := "2025-09-23")]
theorem step_one (s1 s2 : State) e2 : s1 -[e2]-> s2 → s1 -[e2]*> s2 := star.plus_one s1 s2 e2

theorem star.trans_star (s s' s'' : State) e e' :
  s -[e]*> s' → s' -[e']*> s'' → s -[e ++ e']*> s''  := by
  intros H1; induction H1 generalizing s'' e'
  . simp
  . intros H1
    rw [List.append_assoc]
    apply star.step
    assumption
    rename_i ih
    apply ih; apply H1

end Behaviour

section UpdateFin

variable {α : Type _}
variable {n : Nat}

def update_Fin (i' : Fin n) (e : α) (f : Fin n → α) : Fin n → α :=
  fun i =>
    if i == i' then
      e
    else
      f i

@[simp]
theorem update_Fin_gso (i i' : Fin n) (e : α) (f : Fin n → α) :
  ¬(i = i') → update_Fin i' e f i = f i := by
    intro h1
    unfold update_Fin
    simp [*] at *


@[simp]
theorem update_Fin_gss (i  : Fin n) (e : α) (f : Fin n → α) :
  update_Fin i e f i  = e := by
    unfold update_Fin
    simp

def enq_Fin (i' : Fin n)  (e : α) (f : Fin n → List α) : Fin n → List α :=
  fun i =>
    if i == i' then
      f i ++ [e]
    else
      f i

end UpdateFin

def subtract_Fin (i : Fin 3): Fin 2 :=
  match i with
  | 0 => 0
  | 1 => 0
  | 2 => 1

abbrev Token := Nat
abbrev Port2 := Fin 2
abbrev Port3 := Fin 3
abbrev Queue := List Token

inductive Event size where
  | write_port (v : Token)
  | read_port (n : Fin size) (v : Token)
  deriving Inhabited, Repr

def range (n : Nat) : List (Fin n) :=
  loop n (Nat.le_of_eq (Eq.refl n)) []
where
  loop : (y : Nat) → y ≤ n → List (Fin n) → List (Fin n)
  | 0,   _,  ns => ns
  | n+1, lt, ns => let ltn := Nat.lt_of_succ_le lt; loop n (Nat.le_of_lt ltn) ({val := n, isLt := ltn}::ns)

instance {b n} [Repr b] : Repr (Fin n → b) where
  reprPrec a _n := Id.run <| do
    let mut s : Std.Format := ""
    for nVal in range n do
      s := s ++ (repr <| a nVal)
    return s

end Graphiti
