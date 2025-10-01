/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Padrini
-/
import Graphiti.Core.StateTransition


namespace Graphiti



section Behaviour

variable {State Event : Type _}
variable [trans: StateTransition State Event]

variable {State Event : Type _}
variable [trans: StateTransition State Event]

inductive star_rev : State → List Event → State → Prop where
  | refl : ∀ s1, star_rev s1 [] s1
  | step : ∀ s1 s2 s3 e1 e2, trans.step s2 e2 s3 → star_rev s1 e1 s2 → star_rev s1 (e1 ++ e2) s3



theorem star_eq_star_rev (s1 s2: State) (e1: List Event): star s1 e1 s2 ↔ star_rev s1 e1 s2 := by
  constructor
  . intro st1
    induction st1
    . apply star_rev.refl
    . sorry -- HAVE TO ADD starRev multiple cases
  . intro ex
    induction ex
    . apply star.refl
    . rename_i s3 s4 l1 l2 stepIn star2In starIn
      have cc := star.plus_one s3 s4 l2 stepIn
      have cc2 := star.trans_star s1 s3 s4 l1 l2 starIn cc
      assumption
