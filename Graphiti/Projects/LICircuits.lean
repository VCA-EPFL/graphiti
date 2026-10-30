import Graphiti.Projects.CombinationalStream

namespace Graphiti.LICircuits

open Graphiti.CombModule
open Graphiti.CombModule.List
-- todo check
open Batteries (AssocList)


abbrev N := List Nat
abbrev DV := List (BitVec 32)               --  data vector
abbrev Tok := List (Option (BitVec 32))     --  data tocken

def buffer_spec_m (s : String := "") : StringModule (Named s (D × D)) :=
 {
  inputs := [(↑"in", ⟨ Named s!"{s}.in" D, λ s tt s' => s.1 <<: tt ∧ s'.1 = tt ∧ s'.2 = s.2 ⟩)].toAssocList,
  outputs := [(↑"out", ⟨ Named s!"{s}.out" D, λ s tt s' => s.2 <+: tt ∧ tt <+: s.1 ∧ s'.2 = tt ∧ s'.1 = s.1⟩)].toAssocList,
  init_state := λ s => s = default
 }


def to_tokens (d: DV) (v: D): Tok :=
  List.zipWith (λ x y => if y then x else none) d v

def token_to_stalled_token : Tok → D → Tok
  | [], _ => []
  | _, [] => []
  | x :: xs, r :: rs =>
    x :: (if r || x.isNone then token_to_stalled_token xs rs        -- advace
          else token_to_stalled_token (x :: xs) rs)                  -- stay on the same data

def token_valid (s : Tok) : D := s.map Option.isSome
def token_data (s : Tok) : DV := s.map (fun x => x.getD 0) -- default value should not matter

def handshake_to_token_m (s : String := "") : StringModule (Named s (DV × D)) :=
  { inputs := [(↑"di", ⟨ Named s!"{s}.di" DV, λ s tt s' => s.1 <<: tt ∧ s'.1 = tt ∧ s'.2 = s.2 ⟩),
               (↑"vi", ⟨ Named s!"{s}.vi" D, λ s tt s' => s.2 <<: tt ∧ s'.2 = tt ∧ s'.1 = s.1 ⟩)].toAssocList,
    outputs := [(↑"Do", ⟨ Named s!"{s}.Do" Tok, λ s tt s' => s = s' ∧ tt = to_tokens s.1 s.2 ⟩),
                (↑"ri", ⟨ Named s!"{s}.ri" D, λ s tt s' => s = s' ∧ tt = List.replicate (s.2.length +1) true ⟩)].toAssocList -- TODOcheck: size of ri
    init_state := λ s => s = default
  }

def token_to_handshake_m (s : String := "") : StringModule (Named s (Tok × D)) :=
  { inputs := [(↑"Di", ⟨ Named s!"{s}.Di" Tok, λ s tt s' => s.1 <<: tt ∧ s'.1 = tt ∧ s'.2 = s.2 ⟩),
               (↑"ro", ⟨ Named s!"{s}.ro" D, λ s tt s' => s.2 <<: tt ∧ s'.2 = tt ∧ s'.1 = s.1 ⟩)].toAssocList,
    outputs := [(↑"do", ⟨ Named s!"{s}.do" DV, λ s tt s' => s = s' ∧ tt = token_data (token_to_stalled_token s.1 s.2) ⟩),
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

def plus1 (s : DV) : DV := s.map (fun a :BitVec 32  => a +1)

def plus1_hw_m (s : String := "plus1_hw_m") : StringModule (Named s (DV × (D × D))) :=
{ inputs := [(↑"di", ⟨ Named s!"{s}.di" DV, λ s tt s' => s.1 <<: tt ∧ s'.1 = tt ∧ s'.2.1 = s.2.1 ∧ s'.2.2 = s.2.2 ⟩),
            (↑"vi", ⟨ Named s!"{s}.vi" D, λ s tt s' => s.2.1 <<: tt ∧ s'.2.1 = tt ∧ s'.1 = s.1 ∧ s'.2.2 = s.2.2 ⟩),
            (↑"ro", ⟨ Named s!"{s}.ro" D, λ s tt s' => s.2.2 <<: tt ∧ s'.2.2 = tt ∧ s'.1 = s.1 ∧ s'.2.1 = s.2.1 ⟩)].toAssocList,
  outputs := [(↑"do", ⟨ Named s!"{s}.do" DV, λ s tt s' => s = s' ∧ tt = plus1 s.1 ⟩),
              (↑"vo", ⟨ Named s!"{s}.vo" D, λ s tt s' => s = s' ∧ tt = s.2.1 ⟩),
              (↑"ri", ⟨ Named s!"{s}.ri" D, λ s tt s' => s = s' ∧ tt = s.2.2 ⟩)].toAssocList
  init_state := λ s => s = default
}

-- Tests
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


example {s1 s2} : -- test handshake_to_token_m
  (handshake_to_token_m.inputs.getIO "di").2 default [1, 1, 2, 3 ] s1 →
  (handshake_to_token_m.inputs.getIO "vi").2 s1 [true , true, false, true ] s2 →
  (handshake_to_token_m.outputs.getIO "Do").2 s2 [some 1, some 1, none, some 3 ] s2
  ∧ (handshake_to_token_m.outputs.getIO "ri").2 s2 [true, true, true, true] s2 := by
  intro h1 h2
  obtain ⟨s1x, s1y⟩ := s1
  obtain ⟨s2x, s2y⟩ := s2
  simp [PortMap.getIO, reduceAssocListfind?, default] at *
  obtain ⟨h1_1, h1_2, h1_3⟩ := h1
  obtain ⟨h2_1, h2_2, h2_3⟩ := h2
  subst_vars
  and_intros
  rfl;rfl

example {s1 s2} : -- token_to_handshake_m
  (token_to_handshake_m.inputs.getIO "Di").2 default [some 1, some 1, none, some 3 ] s1 →
  (token_to_handshake_m.inputs.getIO "ro").2 s1 [true, true, true, true ] s2 →
  (token_to_handshake_m.outputs.getIO "do").2 s2 [1, 1, 0, 3 ] s2
  ∧ (token_to_handshake_m.outputs.getIO "vo").2 s2 [ true , true, false, true ] s2 := by
  sorry

example {a1 a2 b1 b2 b3 c1 c2} {d1 d2 : DV} {v1 v2 r1 r2: D}: -- pipleline of token_to_handshake_m + plus1 + handshake_to_token_m
  -- 1: token_to_handshake_m
  (token_to_handshake_m.inputs.getIO "Di").2 default [some 1, none, none, some 3] a1 →   -- input tokens
  (token_to_handshake_m.inputs.getIO "ro").2 a1 r1 a2 →            -- ready
  (token_to_handshake_m.outputs.getIO "do").2 a2 d1 a2 →
  (token_to_handshake_m.outputs.getIO "vo").2 a2 v1 a2 →
  -- 2: plus1
  (plus1_hw_m.inputs.getIO "di").2 default d1 b1 →
  (plus1_hw_m.inputs.getIO "vi").2 b1 v1 b2 →
  (plus1_hw_m.inputs.getIO "ro").2 b2 r2 b3 →                   -- ready
  (plus1_hw_m.outputs.getIO "do").2 b3 d2 b3 →
  (plus1_hw_m.outputs.getIO "vo").2 b3 v2 b3 →
  (plus1_hw_m.outputs.getIO "ri").2 b3 r1 b3 →
  -- 3: handshake_to_token_m
  (handshake_to_token_m.inputs.getIO "di").2 default d2 c1 →
  (handshake_to_token_m.inputs.getIO "vi").2 c1 v2 c2 →
  (handshake_to_token_m.outputs.getIO "ri").2 c2 r2 c2 →
  -- expected final output
  (handshake_to_token_m.outputs.getIO "Do").2 c2 [some 2, none, none, some 4] c2 := by   -- ✎ expected
  intro h1 h2 h3 h4
  intro h5 h6 h7 h8 h9 h10
  intro h11 h12 h13
  obtain ⟨a1x, a1y⟩ := a1
  obtain ⟨a2x, a2y⟩ := a2
  obtain ⟨b1x, b1y, b1z⟩ := b1
  obtain ⟨b2x, b2y, b2z⟩ := b2
  obtain ⟨b3x, b3y, b3z⟩ := b3
  obtain ⟨c1x, c1y⟩ := c1
  obtain ⟨c2x, c2y⟩ := c2
  simp [PortMap.getIO, reduceAssocListfind?, default] at *
  obtain ⟨h12_1, h12_2, h12_3⟩ := h12
  obtain ⟨h11_1, h11_2, h11_3⟩ := h11
  obtain ⟨h7_1, h7_2, h7_3, h7_4⟩ := h7
  obtain ⟨h6_1, h6_2, h6_3, h6_4⟩ := h6
  obtain ⟨h1_1, h1_2, h1_3⟩ := h1
  obtain ⟨h2_1, h2_2, h2_3⟩ := h2
  obtain ⟨h5_1, h5_2, h5_3, h5_4⟩ := h5

  subst_vars
  simp [token_to_stalled_token, token_valid, token_data, plus1, to_tokens]

-- todo : edit the implementation of the Hs2T
-----------------------------------------------------------------------------

namespace Plus1

open List

def plus1_s := [graphEnv|
    ai [type="io"];
    bo [type="io"];

    t2hs [type="token_to_handshake_m", typeImp=$(⟨_, token_to_handshake_m "t2hs"⟩)];
    hs2t [type="handshake_to_token_m", typeImp=$(⟨_, handshake_to_token_m "hs2t"⟩)];
    p1 [type="plus1_hw_m", typeImp=$(⟨_, plus1_hw_m "p1"⟩)];

    ai -> t2hs [to="Di"];

    t2hs -> p1 [from="do",to="di"];
    t2hs -> p1 [from="vo",to="vi"];
    p1 -> t2hs [from="ri",to="ro"];

    p1 -> hs2t [from="do",to="di"];
    p1 -> hs2t [from="vo",to="vi"];
    hs2t -> p1 [from="ri",to="ro"];

    hs2t -> bo [from="Do"];
  ]

def plus1_s_lowered := plus1_s.1.lower_TR |>.get rfl

-- Data flow plus1 : specification
def plus1_df : StringModule Tok where
  inputs := [ (↑"ai", ⟨ Tok, λ s tt s' => s <<: tt ∧ s' = tt ⟩)].toAssocList
  outputs := [ (↑"bo", ⟨ Tok, λ s tt s' => tt = s.map (fun | .some x => some (x+1) | x=>x) ∧ s = s'⟩)].toAssocList
  internals := []
  init_state s := s = ([])

def env := plus1_s.2

@[drenv] theorem find?_t2hs_m : (Batteries.AssocList.find? "token_to_handshake_m" env) = .some ⟨_, token_to_handshake_m "t2hs"⟩ := rfl
@[drenv] theorem find?_hs2t_m : (Batteries.AssocList.find? "handshake_to_token_m" env) = .some ⟨_, handshake_to_token_m "hs2t"⟩ := rfl
@[drenv] theorem find?_p1_m : (Batteries.AssocList.find? "plus1_hw_m" env) = .some ⟨_, plus1_hw_m "p1"⟩ := rfl

seal env in
def_module plus1_m_t : Type :=
  [T| plus1_s_lowered, env.find? ]
reduction_by
  dsimp [plus1_s_lowered]
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
  simp only [drenv]
  dsimp

seal env in
def_module plus1_m : StringModule plus1_m_t :=
  [e| plus1_s_lowered, env.find? ]
reduction_by
       dsimp [plus1_s_lowered]
       (dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
        dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
        dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
        rw [rw_opaque (by simp only [drenv]; rfl)]; dsimp
        dsimp [Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts, Module.mapInputPorts, reduceAssocListfind?]
        simp (disch := decide) only [AssocList.bijectivePortRenaming_invert]
        dsimp [Module.product]
        dsimp only [reduceModuleconnect'2]
        dsimp only [reduceEraseAll]
        dsimp; dsimp [reduceAssocListfind?]

        unfold Module.connect''
        dsimp [toString]
        )
#print plus1_m

instance : MatchInterface plus1_m plus1_df := by
  dsimp [plus1_m, plus1_df]
  solve_match_interface

axiom φ : plus1_m_t → (DV) → Prop

theorem refines' :
  plus1_m ⊑_{φ} plus1_df := by sorry

theorem refines :
  plus1_m ⊑ plus1_df := by sorry

end Plus1

end Graphiti.LICircuits
