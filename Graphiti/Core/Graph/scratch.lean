import Mathlib -- needed for whnf tactic

def type' : Nat → Type
  | 0 => Nat
  | n+1 => type' n

seal type' in
example : ∀ (a : type' 1000), ∃ (a:Nat), True := by
  intro a
  -- simulating a call to `isTypeCorrect` which times out.
  with_unfolding_all whnf at a
  exists a

structure Wrapper (T : Type) where get : T
theorem prop (t: Wrapper (type' 10000)) : True := True.intro

def a (n : Wrapper (type' 10000)) := Wrapper.get n
