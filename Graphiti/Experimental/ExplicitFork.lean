/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.StateTransition

namespace Graphiti

/--
This is the main state of a fork, it consists of the input and output queues,
which are just lists of tokens (natural numbers).
-/
structure ForkState where
  input_queue : Queue
  output_queues : Fin 2 → Queue
  deriving Inhabited, Repr

/--
The semantics of a fork with one input and two outputs.  There are three rules,
two rules deal with IO and one rule is an internal transition from the internal
input queue to both output queues.

Note: In the semantics, just to make it easier to fit into the [StateTransition]
framework, IO events are actually lists, but should only really represent an
event (list of one event) or an empty event (empty list).

In addition to that, internal transitions (that don't output an event) and
external transitions (that are observable and output an event) are both defined
in the same set of rules, but they could also be separated out.
-/
inductive step_fork : ForkState → List (Event 2) → ForkState → Prop where
  | handle_write_event : ∀ s v,
    step_fork s [Event.write_port v] { s with input_queue := s.input_queue ++ [v] }
  | handle_read_event : ∀ s n v rst,
    s.output_queues n = v :: rst →
    step_fork s [Event.read_port n v] { s with output_queues := update_Fin n rst s.output_queues }
  | internal_step : ∀ s v rst,
    s.input_queue = v :: rst →
    step_fork s [] { s with output_queues := enq_Fin 0 v (enq_Fin 1 v s.output_queues),
                            input_queue := rst
                   }

/--
We instantiate the state transition class so that we can use some fancy
notation.
-/
instance : StateTransition (Event 2) ForkState where
  init := default
  step := step_fork

/--
We now construct a state for the larger system, which combines the two forks
into the greater fork, which should then be equivalent with a fork with three
outputs.

Here we can reuse the fork states of the forks themselves, so that in the
semantics we can reuse the semantics of a single fork.
-/
structure DoubleForkState where
  fork1 : ForkState
  fork2 : ForkState
  deriving Inhabited, Repr

/--
We then define the semantics for the double fork, where we handle write events
by passing them to the first fork, and handle read events by reading from either
fork output depending on the value of the port one wants to read from.
-/
inductive step_double_fork : DoubleForkState → List (Event 3) → DoubleForkState → Prop where
/--
Push a token to the port of fork1.
-/
  | handle_write_event : ∀ s fork1' v,
    step_fork s.fork1 [Event.write_port v] fork1' →
    step_double_fork s [Event.write_port v] { s with fork1 := fork1' }
/--
Read a token from the external port of fork1 (port 0).
-/
  | handle_read_event1 : ∀ s fork1' v,
    step_fork s.fork1 [Event.read_port 0 v] fork1' →
    step_double_fork s [Event.read_port 0 v] { s with fork1 := fork1' }
/--
Read a token from the external ports of fork2 (port 1 and 2).
-/
  | handle_read_event2 : ∀ s fork2' (n : Fin 3) v,
    n ≠ 0 →
    step_fork s.fork2 [Event.read_port (subtract_Fin n) v] fork2' →
    step_double_fork s [Event.read_port n v] { s with fork2 := fork2' }
/--
Run an internal step of fork1.
-/
  | run_internal_fork1 : ∀ s fork1',
    step_fork s.fork1 [] fork1' →
    step_double_fork s [] { s with fork1 := fork1' }
/--
Run an internal step of fork2.
-/
  | run_internal_fork2 : ∀ s fork2',
    step_fork s.fork2 [] fork2' →
    step_double_fork s [] { s with fork2 := fork2' }
/--
Push a token from the port of fork1 to the input port of fork2.
-/
  | push_internal_token : ∀ s v fork1' fork2',
    step_fork s.fork1 [Event.read_port 1 v] fork1' →
    step_fork s.fork2 [Event.write_port v] fork2' →
    step_double_fork s [] { s with fork1 := fork1',
                                   fork2 := fork2'
                          }

instance : StateTransition (Event 3) DoubleForkState where
  init := default
  step := step_double_fork

/--
This theorem states that if we assume that the input_queue has a token with
value 5, then we can read 5 from the 2nd port of fork2 (the third port of the
whole system).  To "execute" the system, we have to manually apply the steps of
the transition system to go from the input step to some output state from which
we can observe a read of the value 5.
-/
theorem can_reach_some_output :
  ∃ s', { (default : DoubleForkState) with fork1.input_queue := [5] }
          -[ [(Event.read_port 2 5 : Event 3)] ]*> s' := by
    simp [default]; constructor
    apply step_internal
    · apply step_double_fork.run_internal_fork1
      apply step_fork.internal_step
      and_intros <;> rfl
    · apply step_internal
      · apply step_double_fork.push_internal_token
        apply step_fork.handle_read_event
        · unfold enq_Fin; simp
          and_intros <;> rfl
        · apply step_fork.handle_write_event
      · apply step_internal
        · apply step_double_fork.run_internal_fork2
          apply step_fork.internal_step
          simp; and_intros <;> rfl
        · apply step_one
          apply step_double_fork.handle_read_event2
          · omega
          · have h : subtract_Fin 2 = 1 := by simp [subtract_Fin]
            simp; rw [h]
            apply step_fork.handle_read_event
            simp [enq_Fin]; rfl

end Graphiti
