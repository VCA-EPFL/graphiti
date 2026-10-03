import Graphiti.Projects.CombinationalStream

namespace Graphiti.LICircuits

open Graphiti.CombModule
open Graphiti.CombModule.List

abbrev N := List Nat
abbrev Tok := List (Option Bool)


def to_tokens (d v : D) : Tok :=
  List.zipWith (λ x y => if y then x else none) d v

def token_to_stalled_token : Tok → D → Tok
  | [], _ => []
  | _, [] => []
  | x :: xs, r :: rs =>
    x :: (if r || x.isNone then token_to_stalled_token xs rs        -- advace
          else token_to_stalled_token (x :: xs) rs)                  -- stay on the same data

def token_valid (s : Tok) : D := s.map Option.isSome
def token_data (s : Tok) : D := s.map (fun x => x.getD false) -- default value should not matter

def handshake_to_token_m (s : String := "") : StringModule (Named s (D × D)) :=
  { inputs := [(↑"di", ⟨ Named s!"{s}.di" D, λ s tt s' => s.1 <<: tt ∧ s'.1 = tt ∧ s'.2 = s.2 ⟩),
               (↑"vi", ⟨ Named s!"{s}.vi" D, λ s tt s' => s.2 <<: tt ∧ s'.2 = tt ∧ s'.1 = s.1 ⟩)].toAssocList,
    outputs := [(↑"Do", ⟨ Named s!"{s}.Do" Tok, λ s tt s' => s = s' ∧ tt = to_tokens s.1 s.2 ⟩),
                (↑"ri", ⟨ Named s!"{s}.ri" D, λ s tt s' => s = s' ∧ tt = List.replicate (s.2.length +1) true ⟩)].toAssocList -- TODOcheck: size of ri
    init_state := λ s => s = default
  }

def token_to_handshake_m (s : String := "") : StringModule (Named s (Tok × D)) :=
  { inputs := [(↑"Di", ⟨ Named s!"{s}.Di" Tok, λ s tt s' => s.1 <<: tt ∧ s'.1 = tt ∧ s'.2 = s.2 ⟩),
               (↑"ro", ⟨ Named s!"{s}.ro" D, λ s tt s' => s.2 <<: tt ∧ s'.2 = tt ∧ s'.1 = s.1 ⟩)].toAssocList,
    outputs := [(↑"do", ⟨ Named s!"{s}.do" D, λ s tt s' => s = s' ∧ tt = token_data (token_to_stalled_token s.1 s.2) ⟩),
                (↑"vo", ⟨ Named s!"{s}.vo" D, λ s tt s' => s = s' ∧ tt = token_valid (token_to_stalled_token s.1 s.2)⟩)].toAssocList
    init_state := λ s => s = default
  }

def not_hw_m (s : String := "") : StringModule (Named s (D × (D × D))) :=
  { inputs := [(↑"di", ⟨ Named s!"{s}.di" D, λ s tt s' => s.1 <<: tt ∧ s'.1 = tt ∧ s'.2.1 = s.2.1 ∧ s'.2.2 = s.2.2 ⟩),
               (↑"vi", ⟨ Named s!"{s}.vi" D, λ s tt s' => s.2.1 <<: tt ∧ s'.2.1 = tt ∧ s'.1 = s.1 ∧ s'.2.2 = s.2.2 ⟩),
               (↑"ro", ⟨ Named s!"{s}.ro" D, λ s tt s' => s.2.2 <<: tt ∧ s'.2.2 = tt ∧ s'.1 = s.1 ∧ s'.2.1 = s.2.1 ⟩)].toAssocList,
    outputs := [(↑"do", ⟨ Named s!"{s}.do" D, λ s tt s' => s = s' ∧ tt = not s.1 ⟩),
                (↑"vo", ⟨ Named s!"{s}.vo" D, λ s tt s' => s = s' ∧ tt = s.2.1 ⟩),
                (↑"ri", ⟨ Named s!"{s}.ri" D, λ s tt s' => s = s' ∧ tt = s.2.2 ⟩)].toAssocList
    init_state := λ s => s = default
  }

def plus1 (s : List Nat) : List Nat := s.map (fun a : Nat => a+1)

def plus1_hw_m (s : String := "") : StringModule (Named s (N × (D × D))) :=
{ inputs := [(↑"di", ⟨ Named s!"{s}.di" N, λ s tt s' => s.1 <<: tt ∧ s'.1 = tt ∧ s'.2.1 = s.2.1 ∧ s'.2.2 = s.2.2 ⟩),
            (↑"vi", ⟨ Named s!"{s}.vi" D, λ s tt s' => s.2.1 <<: tt ∧ s'.2.1 = tt ∧ s'.1 = s.1 ∧ s'.2.2 = s.2.2 ⟩),
            (↑"ro", ⟨ Named s!"{s}.ro" D, λ s tt s' => s.2.2 <<: tt ∧ s'.2.2 = tt ∧ s'.1 = s.1 ∧ s'.2.1 = s.2.1 ⟩)].toAssocList,
  outputs := [(↑"do", ⟨ Named s!"{s}.do" N, λ s tt s' => s = s' ∧ tt = plus1 s.1 ⟩),
              (↑"vo", ⟨ Named s!"{s}.vo" D, λ s tt s' => s = s' ∧ tt = s.2.1 ⟩),
              (↑"ri", ⟨ Named s!"{s}.ri" D, λ s tt s' => s = s' ∧ tt = s.2.2 ⟩)].toAssocList
  init_state := λ s => s = default
}

example {s1 s2 s3} :
  (plus1_hw_m.inputs.getIO "di").2 default [1, 2, 3] s1 →
  (plus1_hw_m.inputs.getIO "vi").2 s1 [True, False, True] s2 →
  (plus1_hw_m.inputs.getIO "ro").2 s2 [True, True, True] s3 →
  (plus1_hw_m.outputs.getIO "do").2 s3 [2, 3, 4] s3
  ∧ (plus1_hw_m.outputs.getIO "vo").2 s3 [True, False, True] s3
  ∧ (plus1_hw_m.outputs.getIO "ri").2 s3 [True, True, True] s3 := by
  intro h1 h2 h3
  obtain ⟨s1x, s1y, s1z⟩ := s1
  obtain ⟨s2x, s2y, s2z⟩ := s2
  obtain ⟨s3x, s3y, s3z⟩ := s3
  simp [PortMap.getIO,reduceAssocListfind?,default] at *
  obtain ⟨h1_1, h1_2, h1_3, h1_4⟩ := h1
  obtain ⟨h2_1, h2_2, h2_3, h2_4⟩ := h2
  obtain ⟨h3_1, h3_2, h3_3, h3_4⟩ := h3
  subst_vars
  and_intros <;> rfl

end Graphiti.LICircuits
