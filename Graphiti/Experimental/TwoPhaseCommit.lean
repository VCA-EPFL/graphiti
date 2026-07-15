namespace TwoPhaseCommit

structure Coordinator where

inductive PState where
| empty
| tentative (b : Bool)
| committed (b : Bool)

def PState.commit : PState → PState
| .tentative b => .committed b
| e => e

structure State where
  p12c : Option Bool
  p22c : Option Bool
  p1 : PState
  p2 : PState

inductive Rule where
| pinit1
| pinit2
| part1
| part2
| commit

inductive Protocol : Rule → State → State → Prop where
| step_pinit1 {s : State} {b : Bool} : s.p1 = .empty → Protocol .pinit1 s {s with p1 := .tentative b}
| step_pinit2 {s : State} {b : Bool} : s.p2 = .empty → Protocol .pinit2 s {s with p2 := .tentative b}
| step_part1 {s : State} {b : Bool} : s.p1 = .tentative b → Protocol .part1 s {s with p12c := .some b}
| step_part2 {s : State} {b : Bool} : s.p2 = .tentative b → Protocol .part2 s {s with p22c := .some b}
| step_commit {s : State} : s.p12c.isSome → s.p12c = s.p22c → Protocol .commit s {s with p1 := s.p1.commit, p2 := s.p2.commit}

theorem comm_init1_init2 {s s' s''} :
  Protocol .init1 s s' →
  Protocol .init2 s s'' →
  ∃ s''', Protocol .init1 s'' s''' ∧ Protocol .init2 s' s''' := by
  intro h₁ h₂
  cases h₁ with
  | step_init1 hs₁ =>
    cases h₂ with
    | step_init2 hs₂ =>
      refine ⟨_, Protocol.step_init1 ?_, Protocol.step_init2 ?_⟩ <;> assumption

theorem comm_init1_pinit1 {s s' s''} :
  Protocol .init1 s s' →
  Protocol .pinit1 s s'' →
  ∃ s''', Protocol .init1 s'' s''' ∧ Protocol .pinit1 s' s''' := by
  intro h₁ h₂
  cases h₁ with
  | step_init1 hs₁ =>
    cases h₂ with
    | step_pinit1 hs₂ hp₂ => simp_all

theorem comm_init1_pinit2 {s s' s''} :
  Protocol .init1 s s' →
  Protocol .pinit2 s s'' →
  ∃ s''', Protocol .init1 s'' s''' ∧ Protocol .pinit2 s' s''' := by
  intro h₁ h₂
  cases h₁ with
  | step_init1 hs₁ =>
    cases h₂ with
    | step_pinit2 hs₂ hp₂ =>
      refine ⟨_, Protocol.step_init1 ?_, Protocol.step_pinit2 ?_ ?_⟩ <;> assumption

theorem comm_init1_part1 {s s' s''} :
  Protocol .init1 s s' →
  Protocol .part1 s s'' →
  ∃ s''', Protocol .init1 s'' s''' ∧ Protocol .part1 s' s''' := by
  intro h₁ h₂
  cases h₁ with
  | step_init1 hs₁ =>
    cases h₂ with
    | step_part1 hs₂ =>
      refine ⟨_, Protocol.step_init1 ?_, Protocol.step_part1 ?_⟩ <;> assumption

theorem comm_init1_part2 {s s' s''} :
  Protocol .init1 s s' →
  Protocol .part2 s s'' →
  ∃ s''', Protocol .init1 s'' s''' ∧ Protocol .part2 s' s''' := by
  intro h₁ h₂
  cases h₁ with
  | step_init1 hs₁ =>
    cases h₂ with
    | step_part2 hs₂ =>
      refine ⟨_, Protocol.step_init1 ?_, Protocol.step_part2 ?_⟩ <;> assumption

theorem comm_init1_commit {s s' s''} :
  Protocol .init1 s s' →
  Protocol .commit s s'' →
  ∃ s''', Protocol .init1 s'' s''' ∧ Protocol .commit s' s''' := by
  intro h₁ h₂
  cases h₁ with
  | step_init1 hs₁ =>
    cases h₂ with
    | step_commit heq hsome =>
      refine ⟨_, Protocol.step_init1 ?_, Protocol.step_commit ?_ ?_⟩ <;> assumption

theorem comm_init2_pinit1 {s s' s''} :
  Protocol .init2 s s' →
  Protocol .pinit1 s s'' →
  ∃ s''', Protocol .init2 s'' s''' ∧ Protocol .pinit1 s' s''' := by
  intro h₁ h₂
  cases h₁ with
  | step_init2 hs₁ =>
    cases h₂ with
    | step_pinit1 hs₂ hp₂ =>
      refine ⟨_, Protocol.step_init2 ?_, Protocol.step_pinit1 ?_ ?_⟩ <;> assumption

theorem comm_init2_pinit2 {s s' s''} :
  Protocol .init2 s s' →
  Protocol .pinit2 s s'' →
  ∃ s''', Protocol .init2 s'' s''' ∧ Protocol .pinit2 s' s''' := by
  intro h₁ h₂
  cases h₁ with
  | step_init2 hs₁ =>
    cases h₂ with
    | step_pinit2 hs₂ hp₂ => simp_all

theorem comm_init2_part1 {s s' s''} :
  Protocol .init2 s s' →
  Protocol .part1 s s'' →
  ∃ s''', Protocol .init2 s'' s''' ∧ Protocol .part1 s' s''' := by
  intro h₁ h₂
  cases h₁ with
  | step_init2 hs₁ =>
    cases h₂ with
    | step_part1 hs₂ =>
      refine ⟨_, Protocol.step_init2 ?_, Protocol.step_part1 ?_⟩ <;> assumption

theorem comm_init2_part2 {s s' s''} :
  Protocol .init2 s s' →
  Protocol .part2 s s'' →
  ∃ s''', Protocol .init2 s'' s''' ∧ Protocol .part2 s' s''' := by
  intro h₁ h₂
  cases h₁ with
  | step_init2 hs₁ =>
    cases h₂ with
    | step_part2 hs₂ =>
      refine ⟨_, Protocol.step_init2 ?_, Protocol.step_part2 ?_⟩ <;> assumption

theorem comm_init2_commit {s s' s''} :
  Protocol .init2 s s' →
  Protocol .commit s s'' →
  ∃ s''', Protocol .init2 s'' s''' ∧ Protocol .commit s' s''' := by
  intro h₁ h₂
  cases h₁ with
  | step_init2 hs₁ =>
    cases h₂ with
    | step_commit heq hsome =>
      refine ⟨_, Protocol.step_init2 ?_, Protocol.step_commit ?_ ?_⟩ <;> assumption

theorem comm_pinit1_pinit2 {s s' s''} :
  Protocol .pinit1 s s' →
  Protocol .pinit2 s s'' →
  ∃ s''', Protocol .pinit1 s'' s''' ∧ Protocol .pinit2 s' s''' := by
  intro h₁ h₂
  cases h₁ with
  | step_pinit1 hs₁ hp₁ =>
    cases h₂ with
    | step_pinit2 hs₂ hp₂ =>
      refine ⟨_, Protocol.step_pinit1 ?_ ?_, Protocol.step_pinit2 ?_ ?_⟩ <;> assumption

theorem comm_pinit1_part1 {s s' s''} :
  Protocol .pinit1 s s' →
  Protocol .part1 s s'' →
  ∃ s''', Protocol .pinit1 s'' s''' ∧ Protocol .part1 s' s''' := by
  intro h₁ h₂
  cases h₁ with
  | step_pinit1 hc hp =>
    cases h₂ with
    | step_part1 hp' => simp_all

theorem comm_pinit1_part2 {s s' s''} :
  Protocol .pinit1 s s' →
  Protocol .part2 s s'' →
  ∃ s''', Protocol .pinit1 s'' s''' ∧ Protocol .part2 s' s''' := by
  intro h₁ h₂
  cases h₁ with
  | step_pinit1 hs₁ hp₁ =>
    cases h₂ with
    | step_part2 hs₂ =>
      refine ⟨_, Protocol.step_pinit1 ?_ ?_, Protocol.step_part2 ?_⟩ <;> assumption

theorem comm_pinit2_part1 {s s' s''} :
  Protocol .pinit2 s s' →
  Protocol .part1 s s'' →
  ∃ s''', Protocol .pinit2 s'' s''' ∧ Protocol .part1 s' s''' := by
  intro h₁ h₂
  cases h₁ with
  | step_pinit2 hs₁ hp₁ =>
    cases h₂ with
    | step_part1 hs₂ =>
      refine ⟨_, Protocol.step_pinit2 ?_ ?_, Protocol.step_part1 ?_⟩ <;> assumption

theorem comm_pinit2_part2 {s s' s''} :
  Protocol .pinit2 s s' →
  Protocol .part2 s s'' →
  ∃ s''', Protocol .pinit2 s'' s''' ∧ Protocol .part2 s' s''' := by
  intro h₁ h₂
  cases h₁ with
  | step_pinit2 hc hp =>
    cases h₂ with
    | step_part2 hp' => simp_all

theorem comm_part1_part2 {s s' s''} :
  Protocol .part1 s s' →
  Protocol .part2 s s'' →
  ∃ s''', Protocol .part1 s'' s''' ∧ Protocol .part2 s' s''' := by
  intro h₁ h₂
  cases h₁ with
  | step_part1 hs₁ =>
    cases h₂ with
    | step_part2 hs₂ =>
      refine ⟨_, Protocol.step_part1 ?_, Protocol.step_part2 ?_⟩ <;> assumption

theorem comm_pinit1_commit {s s' s''} :
  Protocol .pinit1 s s' →
  Protocol .commit s s'' →
  ∃ s''', Protocol .pinit1 s'' s''' ∧ Protocol .commit s' s''' := by
  -- One order leaves p1 tentative, while the other commits it.
  sorry

theorem comm_pinit2_commit {s s' s''} :
  Protocol .pinit2 s s' →
  Protocol .commit s s'' →
  ∃ s''', Protocol .pinit2 s'' s''' ∧ Protocol .commit s' s''' := by
  -- One order leaves p2 tentative, while the other commits it.
  sorry

theorem comm_part1_commit {s s' s''} :
  Protocol .part1 s s' →
  Protocol .commit s s'' →
  ∃ s''', Protocol .part1 s'' s''' ∧ Protocol .commit s' s''' := by
  -- Commit makes p1 committed, disabling the part1 step on that branch.
  sorry

theorem comm_part2_commit {s s' s''} :
  Protocol .part2 s s' →
  Protocol .commit s s'' →
  ∃ s''', Protocol .part2 s'' s''' ∧ Protocol .commit s' s''' := by
  -- Commit makes p2 committed, disabling the part2 step on that branch.
  sorry

end TwoPhaseCommit
