import Mathlib.Tactic

namespace TwoPhaseCommit

structure Coordinator where

structure State where
  c2p1 : Option Unit
  c2p2 : Option Unit
  p12c : Option Bool
  p22c : Option Bool
  p1 : Option Bool
  p2 : Option Bool

inductive Rule where
| init1
| init2
| part1
| part2
| commit

inductive Protocol : Rule → State → State → Prop where
| step_init1 {s : State} : s.c2p1 = .none → Protocol .init1 s {s with c2p1 := .some .unit}
| step_init2 {s : State} : s.c2p2 = .none → Protocol .init2 s {s with c2p2 := .some .unit}
| step_part1 {s : State} {b : Bool} : s.c2p1 = .some .unit → Protocol .part1 s {s with p12c := .some b}
| step_part2 {s : State} {b : Bool} : s.c2p2 = .some .unit → Protocol .part2 s {s with p22c := .some b}
| step_commit {s : State} : s.p12c = s.p22c → s.p12c.isSome → Protocol .commit s {s with p1 := s.p12c, p2 := s.p22c}

theorem comm_init1_init2 {s s' s''} :
  Protocol .init1 s s' →
  Protocol .init2 s s'' →
  ∃ s''', Protocol .init1 s'' s''' ∧ Protocol .init2 s' s''' := by
  grind

theorem comm_init1_part1 {s s' s''} :
  Protocol .init1 s s' →
  Protocol .part1 s s'' →
  ∃ s''', Protocol .init1 s'' s''' ∧ Protocol .part1 s' s''' := by
  grind

theorem comm_init1_part2 {s s' s''} :
  Protocol .init1 s s' →
  Protocol .part2 s s'' →
  ∃ s''', Protocol .init1 s'' s''' ∧ Protocol .part2 s' s''' := by
  grind

theorem comm_init1_commit {s s' s''} :
  Protocol .init1 s s' →
  Protocol .commit s s'' →
  ∃ s''', Protocol .init1 s'' s''' ∧ Protocol .commit s' s''' := by
  grind

theorem comm_init2_part1 {s s' s''} :
  Protocol .init2 s s' →
  Protocol .part1 s s'' →
  ∃ s''', Protocol .init2 s'' s''' ∧ Protocol .part1 s' s''' := by
  grind

theorem comm_init2_part2 {s s' s''} :
  Protocol .init2 s s' →
  Protocol .part2 s s'' →
  ∃ s''', Protocol .init2 s'' s''' ∧ Protocol .part2 s' s''' := by
  grind

theorem comm_init2_commit {s s' s''} :
  Protocol .init2 s s' →
  Protocol .commit s s'' →
  ∃ s''', Protocol .init2 s'' s''' ∧ Protocol .commit s' s''' := by
  grind

theorem comm_part1_part2 {s s' s''} :
  Protocol .part1 s s' →
  Protocol .part2 s s'' →
  ∃ s''', Protocol .part1 s'' s''' ∧ Protocol .part2 s' s''' := by
  grind

end TwoPhaseCommit
