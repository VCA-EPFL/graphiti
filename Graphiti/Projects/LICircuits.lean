import Graphiti.Projects.CombinationalStream

namespace Graphiti.LICircuits

open Graphiti.CombModule
open Graphiti.CombModule.List
-- todo check
open Batteries (AssocList)

namespace Similarity

variable {α : Type _}


def similar : List (Option α) → List (Option α) → Prop -- s1 ≲ s2
  | [], []                     => True
  | [], none :: ys             => similar [] ys
  | [], some _ :: _            => False
  | _ :: _, []                 => False
  | none :: xs, none :: ys     => similar xs ys
  | none :: xs, some b :: ys   => False
  | some a :: xs, none :: ys   => similar (some a :: xs) ys
  | some a :: xs, some b :: ys => a = b ∧ similar xs ys
termination_by x y => x.length + y.length

inductive similarP : List (Option α) → List (Option α) → Prop where
  | empty : similarP [] []
  | sym {xs ys a} : similarP xs ys -> similarP (a :: xs) (a :: ys)
  | noneRight {xs ys} : similarP xs ys -> similarP xs (none :: ys)


infix:50 " ≲ " => similarP

theorem similar_is_reflexive (s :  List (Option α)) : similarP s s := by
  induction s with
  | nil => exact similarP.empty
  | cons x xs ih => exact similarP.sym ih

theorem similar_is_transitive : ∀ {s1 s2 s3 : List (Option α)}, similarP s1 s2 → similarP s2 s3 → similarP s1 s3
  | _, _, _, .empty, h2 => h2
  | _, _, _, .sym h, .sym h2' => .sym (similar_is_transitive h h2')
  | _, _, _, .sym h, .noneRight h2' => .noneRight (similar_is_transitive (.sym h) h2')
  | _, _, _, .noneRight h, .sym h2' => .noneRight (similar_is_transitive h h2')
  | _, _, _, .noneRight h, .noneRight h2' => .noneRight (similar_is_transitive (.noneRight h) h2')
termination_by s1 s2 s3 _ _ => s1.length + s2.length + s3.length

theorem similar_map {α β} (f : α → β) {s1 s2 : List (Option α)} (h : similarP s1 s2) :
    similarP (s1.map (Option.map f)) (s2.map (Option.map f)) := by
    induction h
    case empty => simp ; exact similarP.empty
    case sym xs ys a h1 ih => unfold List.map; exact similarP.sym ih
    case noneRight xs ys h1 ih => simp only [List.map_cons, Option.map_none]; exact similarP.noneRight ih

theorem similar_length_le  {s1 s2:  List (Option α) } (h1 : similarP s1 s2): s1.length ≤ s2.length := by
  induction h1 <;>grind

end Similarity

-- abbrev D := List Bool
abbrev N := List Nat
abbrev DV := List (BitVec 32)               --  data vector
abbrev Tok := List (Option (BitVec 32))     --  data tocken

def buffer_spec_m (s : String := "") : StringModule (Named s (Tok × Tok)) :=
 {
  inputs := [(↑"in", ⟨ Named s!"{s}.in" Tok, λ s tt s' => s.1 <<: tt ∧ s'.1 = tt ∧ s'.2 = s.2 ⟩)].toAssocList,
  outputs := [(↑"out", ⟨ Named s!"{s}.out" Tok, λ s tt s' => s.2 <+: tt ∧ tt <+: s.1 ∧ s'.2 = tt ∧ s'.1 = s.1⟩)].toAssocList,
  init_state := λ s => s = default
 }

def delay_m (s : String := "") : StringModule (Named s (Tok × Tok)) :=
 {
  inputs := [(↑"in", ⟨ Named s!"{s}.in" Tok, λ s tt s' => s.1 <<: tt ∧ s'.1 = tt ∧ s'.2 = s.2 ⟩)].toAssocList,
  outputs := [(↑"out", ⟨ Named s!"{s}.out" Tok, λ s tt s' => s.2 <+: tt ∧ s.1 ≲ tt ∧ s'.2 = tt ∧ s'.1 = s.1⟩)].toAssocList,
  init_state := λ s => s = default
 }

-- Implementation of 𝒜(·)
def to_tokens (d: DV) (v r: D)
              (v0: Bool:= false) (r0: Bool:= false): Tok :=
  match d, v, r   with
  | [], _, _ => []
  | _, [], _ => []
  | _, _, [] => []
  | dh :: dt, vh :: vt, rh :: rt =>
    (if (¬vh ∨ (v0 ∧ ¬r0)) then none else some dh) :: to_tokens dt vt rt vh rh

def token_to_stalled_token : Tok → D → Tok
  | [], _ => []
  | _, [] => []
  | x :: xs, r :: rs =>
    x :: (if r || x.isNone then token_to_stalled_token xs rs        -- advace
          else token_to_stalled_token (x :: xs) rs)                  -- stay on the same data

def token_compact (s : Tok) : DV := s.reduceOption -- removes none from Tok
def token_valid (s : Tok) : D := s.map Option.isSome
-- token_data : when D has some value, d is the same value otherwise d can be anything
def token_data (D : Tok) (d : DV) : Prop :=
  match D, d with
  | [], []                 => True
  | [], _ :: _             => False
  | _ :: _, []             => False
  | none :: xs, _ :: ys    => token_data xs ys
  | some x :: xs, y::ys    => x = y ∧  token_data xs ys

theorem token_data_default (C : Tok) : token_data C (C.map (fun x => x.getD 0)) := by
  induction C with
  | nil => trivial
  | cons x xs ih =>
    cases x with
    | none => simpa [token_data] using ih
    | some v => simpa [token_data] using ih

theorem token_data_append {A C : Tok} {d e : DV} (hd : token_data A d) (he : token_data C e) :
    token_data (A ++ C) (d ++ e) := by
    induction A generalizing d with
  | nil =>
    cases d with
    | nil => simpa [token_data] using he
    | cons _ _ => simp [token_data] at hd
  | cons x xs ih =>
    cases d with
    | nil => simp [token_data] at hd
    | cons y ys =>
      cases x with
      | none => exact ih hd
      | some v => exact ⟨hd.1, ih hd.2⟩

def vr_stable (v r: D) (vstay : Bool := false ) (rstay: Bool := false): Prop:=
  match v, r with
  | [], _              => True
  | _, []              => True
  | v0 :: vs, r0 :: rs =>
      (vstay -> v0 = true) ∧  (rstay -> r0 = true) ∧
      (if (r0 == v0) then vr_stable vs rs false false  -- if there were any data it is transfered
      else if (r0 = true ∧ v0 = false) then vr_stable vs rs false true
      else vr_stable vs rs false true  -- r0 = false ∧ v0 = true
      )


def handshake_to_token_m (s : String := "") : StringModule (Named s (DV × D × D)) := -- (d, v, r)
  { inputs := [(↑"di", ⟨ Named s!"{s}.di" DV, λ s tt s' => s.1 <<: tt ∧ s'.1 = tt ∧ s'.2 = s.2 ⟩),
               (↑"vi", ⟨ Named s!"{s}.vi" D, λ s tt s' => s.2.1 <<: tt ∧ s'.2.1 = tt ∧ s'.1 = s.1 ∧ s'.2.2 = s.2.2 ⟩)].toAssocList,
    outputs := [(↑"Do", ⟨ Named s!"{s}.Do" Tok, λ s tt s' => s = s' ∧ tt = to_tokens s.1 s.2.1 s.2.2⟩),
                (↑"ri", ⟨ Named s!"{s}.ri" D, λ s tt s' => s.2.2 <+: s'.2.2 ∧ vr_stable s'.2.1 s'.2.2 ∧ s'.2.2 = tt ∧ s'.1 = s.1 ∧ s'.2.1 = s.2.1 ⟩)].toAssocList -- TODOcheck:
    init_state := λ s => s = default
  }

-- Note: we are assuming that input D is comming from a source outputting asap.
-- We need to make sure that input ready is not faster than D
def token_to_handshake_m (s : String := "") : StringModule (Named s (Tok × D)) := -- (Di , r)
  { inputs := [(↑"Di", ⟨ Named s!"{s}.Di" Tok, λ s tt s' => s.1 <<: tt ∧ s'.1 = tt ∧ s'.2 = s.2 ⟩),
               (↑"ro", ⟨ Named s!"{s}.ro" D, λ s tt s' => s.2 <<: tt ∧ s'.2 = tt ∧ s'.1 = s.1  ∧
                          vr_stable (token_valid (token_to_stalled_token s.1 s.2)) tt⟩)].toAssocList, -- vr_stable of outputed valid and the ready in the input
    outputs := [(↑"do", ⟨ Named s!"{s}.do" DV, λ s tt s' => s = s' ∧ token_data (token_to_stalled_token s.1 s.2) tt ⟩),
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

-- Testing some examples
-- example {s1 s2} : -- test handshake_to_token_m
--   (handshake_to_token_m.inputs.getIO "di").2 default [1, 1, 2, 3 ] s1 →
--   (handshake_to_token_m.inputs.getIO "vi").2 s1 [true , true, false, true ] s2 →
--   (handshake_to_token_m.outputs.getIO "Do").2 s2 [some 1, some 1, none, some 3 ] s2
--   ∧ (handshake_to_token_m.outputs.getIO "ri").2 s2 [true, true, true, true] s2 := by
--   intro h1 h2
--   obtain ⟨s1x, s1y⟩ := s1
--   obtain ⟨s2x, s2y⟩ := s2
--   simp [PortMap.getIO, reduceAssocListfind?, default] at *
--   obtain ⟨h1_1, h1_2, h1_3⟩ := h1
--   obtain ⟨h2_1, h2_2, h2_3⟩ := h2
--   subst_vars
--   and_intros
--   rfl;rfl

-- example {s1 s2} : -- token_to_handshake_m
--   (token_to_handshake_m.inputs.getIO "Di").2 default [some 1, some 1, none, some 3 ] s1 →
--   (token_to_handshake_m.inputs.getIO "ro").2 s1 [true, true, true, true ] s2 →
--   (token_to_handshake_m.outputs.getIO "do").2 s2 [1, 1, 0, 3 ] s2
--   ∧ (token_to_handshake_m.outputs.getIO "vo").2 s2 [ true , true, false, true ] s2 := by
--   sorry

-- example {a1 a2 b1 b2 b3 c1 c2} {d1 d2 : DV} {v1 v2 r1 r2: D}: -- pipleline of token_to_handshake_m + plus1 + handshake_to_token_m
--   -- 1: token_to_handshake_m
--   (token_to_handshake_m.inputs.getIO "Di").2 default [some 1, none, none, some 3] a1 →   -- input tokens
--   (token_to_handshake_m.inputs.getIO "ro").2 a1 r1 a2 →            -- ready
--   (token_to_handshake_m.outputs.getIO "do").2 a2 d1 a2 →
--   (token_to_handshake_m.outputs.getIO "vo").2 a2 v1 a2 →
--   -- 2: plus1
--   (plus1_hw_m.inputs.getIO "di").2 default d1 b1 →
--   (plus1_hw_m.inputs.getIO "vi").2 b1 v1 b2 →
--   (plus1_hw_m.inputs.getIO "ro").2 b2 r2 b3 →                   -- ready
--   (plus1_hw_m.outputs.getIO "do").2 b3 d2 b3 →
--   (plus1_hw_m.outputs.getIO "vo").2 b3 v2 b3 →
--   (plus1_hw_m.outputs.getIO "ri").2 b3 r1 b3 →
--   -- 3: handshake_to_token_m
--   (handshake_to_token_m.inputs.getIO "di").2 default d2 c1 →
--   (handshake_to_token_m.inputs.getIO "vi").2 c1 v2 c2 →
--   (handshake_to_token_m.outputs.getIO "ri").2 c2 r2 c2 →
--   -- expected final output
--   (handshake_to_token_m.outputs.getIO "Do").2 c2 [some 2, none, none, some 4] c2 := by   -- ✎ expected
--   intro h1 h2 h3 h4
--   intro h5 h6 h7 h8 h9 h10
--   intro h11 h12 h13
--   obtain ⟨a1x, a1y⟩ := a1
--   obtain ⟨a2x, a2y⟩ := a2
--   obtain ⟨b1x, b1y, b1z⟩ := b1
--   obtain ⟨b2x, b2y, b2z⟩ := b2
--   obtain ⟨b3x, b3y, b3z⟩ := b3
--   obtain ⟨c1x, c1y⟩ := c1
--   obtain ⟨c2x, c2y⟩ := c2
--   simp [PortMap.getIO, reduceAssocListfind?, default] at *
--   obtain ⟨h12_1, h12_2, h12_3⟩ := h12
--   obtain ⟨h11_1, h11_2, h11_3⟩ := h11
--   obtain ⟨h7_1, h7_2, h7_3, h7_4⟩ := h7
--   obtain ⟨h6_1, h6_2, h6_3, h6_4⟩ := h6
--   obtain ⟨h1_1, h1_2, h1_3⟩ := h1
--   obtain ⟨h2_1, h2_2, h2_3⟩ := h2
--   obtain ⟨h5_1, h5_2, h5_3, h5_4⟩ := h5

--   subst_vars
--   simp [token_to_stalled_token, token_valid, token_data, plus1, to_tokens]

-- todo : edit the implementation of the Hs2T
-----------------------------------------------------------------------------

namespace Plus1

open List
open Similarity

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

def incTok : Option (BitVec 32) → Option (BitVec 32)
  | some x => some (x + 1)
  | none => none


-- Data flow plus1 : specification
def plus1_df : StringModule Tok where
  inputs := [ (↑"ai", ⟨ Tok, λ s tt s' => s <<: tt ∧ s' = tt ⟩)].toAssocList
  outputs := [ (↑"bo", ⟨ Tok, λ s tt s' => tt = s.map incTok ∧ s = s'⟩)].toAssocList
  internals := []
  init_state s := s = ([])

-- Data flow plus1 followed by a buffer and a delay: specification
def plus1_buf_s := [graphEnv|
    ai [type="io"];
    bo [type="io"];

    p1 [type="plus1_df", typeImp=$(⟨_, plus1_df⟩)];
    buf [type="buffer_spec_m", typeImp=$(⟨_, buffer_spec_m "buf"⟩)];
    delay [type="delay_m", typeImp=$(⟨_, delay_m "delay"⟩)];

    ai -> p1 [to="ai"];
    p1 -> buf [from="bo",to="in"];
    buf -> delay [from="out", to= "in"];
    delay -> bo [from="out"];
  ]

def plus1_buf_s_lowered := plus1_buf_s.1.lower_TR |>.get rfl

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

def env_buf := plus1_buf_s.2

@[drenv] theorem find?_plus1_df : (Batteries.AssocList.find? "plus1_df" env_buf) = .some ⟨_, plus1_df⟩ := rfl
@[drenv] theorem find?_buf_m : (Batteries.AssocList.find? "buffer_spec_m" env_buf) = .some ⟨_, buffer_spec_m "buf"⟩ := rfl
@[drenv] theorem find?_delay_m : (Batteries.AssocList.find? "delay_m" env_buf) = .some ⟨_, delay_m "delay"⟩ := rfl

seal env_buf in
def_module plus1_buf_m_t : Type :=
  [T| plus1_buf_s_lowered, env_buf.find? ]
reduction_by
  dsimp [plus1_buf_s_lowered]
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
  simp only [drenv]
  dsimp

seal env_buf in
def_module plus1_buf_m : StringModule plus1_buf_m_t :=
  [e| plus1_buf_s_lowered, env_buf.find? ]
reduction_by
       dsimp [plus1_buf_s_lowered]
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

-- Refinement of the handshake circuit against the buffered dataflow spec
theorem strict_prefix_map {α β} (f : α → β) {l l' : List α} (h : l <<: l') :
    l.map f <<: l'.map f := by
  obtain ⟨hlen, heq⟩ := h
  refine ⟨by simpa using hlen, ?_⟩
  rw [List.length_map, ← List.map_take, ← heq]

theorem prefix_map {α β} (f : α → β) {l l' : List α} (h : l <+: l') :
    l.map f <+: l'.map f := by grind

theorem token_to_stalled_token_mono :
    ∀ (xx yy : Tok) (zz : D), xx <+: yy →
      token_to_stalled_token xx zz <+: token_to_stalled_token yy zz := by
  intro xx yy zz h
  induction zz generalizing xx yy with
  | nil => cases xx <;> simp [token_to_stalled_token]
  | cons r rs ih =>
    cases xx with
    | nil => simp [token_to_stalled_token]
    | cons x xs =>
      obtain ⟨t, rfl⟩ := h
      simp only [List.cons_append]
      unfold token_to_stalled_token
      split_ifs with hcond
      · obtain ⟨t', heq⟩ := ih xs (xs ++ t) (List.prefix_append xs t)
        exact ⟨t', by simp [List.cons_append, heq]⟩
      · obtain ⟨t', heq⟩ := ih (x :: xs) (x :: xs ++ t) (List.prefix_append (x :: xs) t)
        exact ⟨t', by simp [List.cons_append, heq]⟩



instance : MatchInterface plus1_m plus1_buf_m := by
  dsimp [plus1_m, plus1_buf_m]
  solve_match_interface

def φ (i : plus1_m_t) (s : plus1_buf_m_t) : Prop :=
  let ⟨ s_Di , ⟨ s_r , s_e⟩, ⟨ s_d1 , s_d2⟩ ⟩ := s
  let ⟨⟨ i_1Di, i_1ro⟩, ⟨⟨ i_2di, ⟨ i_2vi, i_2ro⟩⟩,⟨ i_3di, i_3vi, i_3ri⟩⟩⟩ := i

  -- Input
  s_Di = i_1Di ∧
  -- Output
  s_d2 = to_tokens i_3di i_3vi i_3ri ∧ -- = or <+: ??
  -- Spec internals
  s_r <+: i_1Di.map incTok ∧ --  = or <+: ??
  s_e <+: s_r ∧
  s_d1 <+: s_e ∧
  s_d1 ≲ s_d2 ∧
  -- Impl  internals
  i_1ro <+: i_2ro ∧ i_2ro <+: i_3ri ∧
  i_2vi <+: token_valid ( token_to_stalled_token i_1Di i_1ro) ∧
  i_3di <+: plus1 i_2di ∧ i_3vi <+: i_2vi ∧
  ∃ i_2di', token_data ( token_to_stalled_token i_1Di i_1ro) i_2di' ∧ i_2di <+: i_2di'
#print φ
theorem refines' : plus1_m ⊑_{φ} plus1_buf_m := by
  intro init_i init_s Hφ
  apply Module.comp_refines.mk
  · -- Input
    intro ident mid_i v hi
    by_cases HContains : plus1_m.inputs.contains ident
    · obtain ⟨⟨tDi, tro⟩, ⟨pdi, pvi, pro⟩, ⟨hdi, hvi, hri⟩⟩ := init_i
      obtain ⟨x, ⟨ r, e⟩ , ⟨ d1, d2⟩ ⟩ := init_s
      simp [plus1_m] at HContains; subst HContains
      rw [PortMap.rw_rule_execution (by dsimp [plus1_m, reducePortMapgetIO])] at hi
      -- obtain ⟨⟨a1, a2⟩, ⟨b1, b2, b3⟩, ⟨c1, c2, c3⟩⟩ := mid_i
      obtain ⟨⟨m1D, m1r⟩, ⟨m2d, m2v, m2r⟩, ⟨m3d, m3v, m3r⟩⟩ := mid_i
      dsimp [Module.liftL, Module.liftR] at hi
      simp at hi
      obtain ⟨hx, hd2, hr, he, hd1, hd12, htr, hpr, hpv, hdata, hv, h2di⟩ := Hφ
      obtain ⟨⟨hsp, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, rfl, rfl, rfl⟩ := hi
      subst hx
      refine ⟨⟨m1D, ⟨ r, e⟩ , ⟨ d1, d2⟩ ⟩, ⟨m1D, ⟨ r, e⟩ , ⟨ d1, d2⟩ ⟩, ?_, existSR.done _, ?_⟩
      · -- generate almost_mid
        rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]
        dsimp; simp; grind
      · -- simulation relation holds
        dsimp [φ]
        simp
        refine ⟨ hd2, ?_, he, hd1, hd12, htr, hpr,?_,hdata, hv,?_ ⟩
        . have hxx : map incTok x <+: map incTok m1D := prefix_map incTok (strict_prefix_is_prefix _ _ hsp)
          grind
        . apply hpv.trans
          apply IsPrefix.map
          exact token_to_stalled_token_mono _ _ _ (strict_prefix_is_prefix _ _ hsp)

        . -- use i_2di' = old ++ C(use 0 for nones) as a witness
          obtain ⟨old, hold_td, hold_pre⟩ := h2di
          obtain ⟨C, hC⟩ := token_to_stalled_token_mono x m1D m1r (strict_prefix_is_prefix _ _ hsp)
          refine ⟨old ++ C.map (fun a => a.getD 0), ?_, hold_pre.trans (List.prefix_append _ _)⟩
          rw [← hC]
          exact token_data_append hold_td (token_data_default C)


    · exfalso; exact PortMap.getIO_not_contained_false hi HContains
  · -- Output
    intro ident mid_i v hi
    by_cases HContains : plus1_m.outputs.contains ident
    · obtain ⟨⟨tDi, tro⟩, ⟨pdi, pvi, pro⟩, ⟨hdi, hvi, hri⟩⟩ := init_i
      obtain ⟨x, ⟨ r, e⟩ , ⟨ d1, d2⟩ ⟩:= init_s
      simp [plus1_m] at HContains; subst HContains
      rw [PortMap.rw_rule_execution (by dsimp [plus1_m, reducePortMapgetIO])] at hi
      obtain ⟨⟨a1, a2⟩, ⟨b1, b2, b3⟩, ⟨c1, c2⟩⟩ := mid_i
      dsimp [Module.liftL, Module.liftR] at hi
      simp at hi
      obtain ⟨⟨⟨⟨rfl, rfl⟩, hv⟩, ⟨rfl, rfl, rfl⟩⟩, rfl, rfl⟩ := hi
      obtain ⟨hx, hr, he, ht, hp, h1, h2, h3, h4⟩ := Hφ
      -- introduce almost mid and mid
      refine ⟨⟨x, r, e⟩,⟨x, r,to_tokens hdi hvi hri⟩ ,?_, ?_, ?_ ⟩
      . refine  existSR.done _
      . -- going from almost mid to mid and output generation
        rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]
        dsimp; simp;
        constructor
        . grind
        . constructor
          . rw[hv, hr]
            -- have h5 := to_tokens_plus1 (tDi)
            have hhd : hdi <+:plus1 (token_data (token_to_stalled_token tDi tro)) := by
              apply h3.trans
              unfold plus1
              apply IsPrefix.map
              grind
            have hhv : hvi <+: token_valid (token_to_stalled_token tDi tro):= by grind
            -- have h6 := to_tokens_mono hhd hhv --find proper ready
            -- rw [h5] at h6

            sorry
          . grind

      . -- simulation relation holds
        dsimp [φ]
        grind
    · exfalso; exact PortMap.getIO_not_contained_false hi HContains
  · -- Internal
    intro rule mid_i hr hstep
    obtain ⟨⟨tDi, tro⟩, ⟨pdi, pvi, pro⟩, ⟨hdi, hvi, hri⟩⟩ := init_i
    obtain ⟨x, r, e⟩ := init_s
    obtain ⟨⟨a1, a2⟩, ⟨b1, b2, b3⟩, ⟨c1, c2, c3⟩⟩ := mid_i
    obtain ⟨hx, hr', he, ht, hp, h1, h2, h3, h4⟩ := Hφ
    refine ⟨(x, r, e), existSR.done _, ?_⟩
    simp [plus1_m, Module.liftL, Module.liftR, token_to_handshake_m, plus1_hw_m, handshake_to_token_m] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hstep
    · -- t2hs.do -> p1.di
      obtain ⟨⟨rfl, rfl⟩, ⟨⟨hs, rfl⟩, rfl, rfl ,rfl⟩, rfl, rfl⟩ := hstep
      rw[stalled_of_all_true _ _ ht ] at hs ⊢
      dsimp [φ]
      refine ⟨hx, hr', he, ht, hp, by simp,by grind , h3.trans ?_, h4⟩
      simp only[plus1]
      apply prefix_map
      exact h1
    · -- t2hs.vo -> p1.vi
      obtain ⟨⟨rfl, rfl⟩, ⟨⟨hs, rfl⟩, rfl, rfl, rfl⟩, rfl, rfl⟩ := hstep
      rw [stalled_of_all_true _ _ ht] at hs ⊢
      exact ⟨hx, hr', he, ht, hp, h1, List.prefix_refl _, h3, h4.trans (strict_prefix_is_prefix _ _ hs)⟩
    · -- p1.ri -> t2hs.ro
      obtain ⟨⟨⟨⟨rfl, rfl, rfl⟩, rfl, rfl, rfl⟩, rfl⟩, hs, rfl⟩ := hstep
      have hle := hs.1.le
      simp only[φ]
      refine ⟨hx, hr', he, List.prefix_refl a2, hp, h1.trans ?_, h2.trans ?_, h3, h4⟩
      -- todo: monotonic :token_to_stalled_token tDi tro <+: token_to_stalled_token tDi a2
      · unfold token_data; exact List.IsPrefix.map _ (take_mono (List.prefix_refl _) hle)
      · unfold token_valid; exact List.IsPrefix.map _ (take_mono (List.prefix_refl _) hle)
    · -- p1.do -> hs2t.di
      obtain ⟨ ⟨⟨hs, rfl , rfl, rfl⟩, rfl, rfl, rfl⟩, rfl, rfl⟩ := hstep
      simp only[φ]
      exact ⟨hx, hr', he.trans (to_tokens_mono (strict_prefix_is_prefix _ _ hs) (List.prefix_refl _) (List.prefix_refl _)),
        ht, hp, h1, h2, List.prefix_refl _, h4⟩
    · -- p1.vo -> hs2t.vi
      obtain ⟨⟨rfl, rfl⟩, ⟨⟨hs, rfl⟩, rfl, rfl, rfl⟩, rfl, rfl⟩ := hstep
      simp only[φ]
      exact ⟨hx, hr', he.trans (to_tokens_mono (List.prefix_refl _) (strict_prefix_is_prefix _ _ hs) (List.prefix_refl _)),
        ht, hp, h1, h2, h3, List.prefix_refl _⟩
    · -- hs2t.ri -> p1.ro
      obtain ⟨⟨hs, rfl, rfl⟩, ⟨hs2, rfl, rfl, rfl⟩, rfl, rfl⟩ := hstep
      simp only[φ]
      have he': e <+: to_tokens hdi hvi b3 :=
        he.trans (to_tokens_mono (List.prefix_refl hdi) (List.prefix_refl hvi) hs)
      exact ⟨hx, hr', he', by grind, by simp, h1, h2, h3, h4⟩

theorem refines_init : Module.refines_initial plus1_m plus1_buf_m φ := by
  intro i hi
  obtain ⟨⟨tDi, tro⟩, ⟨pdi, pvi, pro⟩, ⟨hdi, hvi, hri⟩⟩ := i
  simp [plus1_m, token_to_handshake_m, plus1_hw_m, handshake_to_token_m] at hi
  refine ⟨([], ⟨[], []⟩ , ⟨[], []⟩), by simp [plus1_buf_m, buffer_spec_m, plus1_df, delay_m]; rfl, ?_⟩
  obtain ⟨⟨rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, rfl, rfl, rfl⟩ := hi
  simp [φ, to_tokens, token_data, token_valid, plus1, token_to_stalled_token]
  refine ⟨rfl, rfl, rfl, similarP.empty, List.nil_prefix, List.nil_prefix, ?_⟩
  refine⟨ [], ?_, List.nil_prefix⟩
  simp [token_to_stalled_token, default ,token_data]



theorem refines : plus1_m ⊑ plus1_buf_m := ⟨inferInstance, φ, refines', refines_init⟩

end Plus1

namespace InterfaceCancellation

open List

def wire_m (s : String := "") : StringModule (Named s (DV × (D × D))) :=
{ inputs := [(↑"di", ⟨ Named s!"{s}.di" DV, λ s tt s' => s.1 <<: tt ∧ s'.1 = tt ∧ s'.2.1 = s.2.1 ∧ s'.2.2 = s.2.2 ⟩),
            (↑"vi", ⟨ Named s!"{s}.vi" D, λ s tt s' => s.2.1 <<: tt ∧ s'.2.1 = tt ∧ s'.1 = s.1 ∧ s'.2.2 = s.2.2 ⟩),
            (↑"ro", ⟨ Named s!"{s}.ro" D, λ s tt s' => s.2.2 <<: tt ∧ s'.2.2 = tt ∧ s'.1 = s.1 ∧ s'.2.1 = s.2.1 ⟩)].toAssocList,
  outputs := [(↑"do", ⟨ Named s!"{s}.do" DV, λ s tt s' => s = s' ∧ tt = s.1 ⟩),
              (↑"vo", ⟨ Named s!"{s}.vo" D, λ s tt s' => s = s' ∧ tt = s.2.1 ⟩),
              (↑"ri", ⟨ Named s!"{s}.ri" D, λ s tt s' => s = s' ∧ tt = s.2.2 ⟩)].toAssocList
  init_state := λ s => s = default
}

def wire_s := [graphEnv|
    dti [type="io"];
    vi [type="io"];
    ro [type="io"];

    dto [type="io"];
    vo [type="io"];
    ri [type="io"];

    wire [type="wire_m", typeImp=$(⟨_, wire_m "wire"⟩)];

    dti -> wire [to="di"];
    vi -> wire [to="vi"];
    ro -> wire [to="ro"];

    wire -> dto [from="do"];
    wire -> vo [from="vo"];
    wire -> ri [from="ri"];
  ]

def wire_s_lowered := wire_s.1.lower_TR |>.get rfl

def env_wire := wire_s.2

@[drenv] theorem find?_wire_m : (Batteries.AssocList.find? "wire_m" env_wire) = .some ⟨_, wire_m⟩ := rfl

seal env_wire in
def_module wire_top_m_t : Type :=
  [T| wire_s_lowered, env_wire.find? ]
reduction_by
  dsimp [wire_s_lowered]
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
  simp only [drenv]
  dsimp

seal env_wire in
def_module wire_top_m : StringModule wire_top_m_t :=
  [e| wire_s_lowered, env_wire.find? ]
reduction_by
       dsimp [wire_s_lowered]
       (dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
        dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
        dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
        rw [rw_opaque (by simp only [drenv]; rfl)]; dsimp
        dsimp [Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts, Module.mapInputPorts, reduceAssocListfind?]
        simp (disch := decide) only [AssocList.bijectivePortRenaming_invert]
        dsimp [Module.product]
        )

def h2t_t2h_s := [graphEnv|
    dti [type="io"];
    vi [type="io"];
    ro [type="io"];

    dto [type="io"];
    vo [type="io"];
    ri [type="io"];

    h2t [type="handshake_to_token_m", typeImp=$(⟨_, handshake_to_token_m "h2t"⟩)];
    t2h [type="token_to_handshake_m", typeImp=$(⟨_, token_to_handshake_m "t2h"⟩)];

    dti -> h2t [to="di"];
    vi -> h2t [to="vi"];
    h2t -> ri [from="ri"];

    h2t -> t2h [from="Do",to="Di"];

    t2h -> dto [from="do"];
    t2h -> vo [from="vo"];
    ro -> t2h [to="ro"];
  ]

def h2t_t2h_s_lowered := h2t_t2h_s.1.lower_TR |>.get rfl

def env_h2t_t2h := h2t_t2h_s.2

@[drenv] theorem find?_handshake_to_token_m : (Batteries.AssocList.find? "handshake_to_token_m" env_h2t_t2h) = .some ⟨_, handshake_to_token_m⟩ := rfl
@[drenv] theorem find?_token_to_handshake_m : (Batteries.AssocList.find? "token_to_handshake_m" env_h2t_t2h) = .some ⟨_, token_to_handshake_m⟩ := rfl

seal env_h2t_t2h in
def_module h2t_t2h_m_t : Type :=
  [T| h2t_t2h_s_lowered, env_h2t_t2h.find? ]
reduction_by
  dsimp [h2t_t2h_s_lowered]
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
  simp only [drenv]
  dsimp

seal env_h2t_t2h in
def_module h2t_t2h_m : StringModule h2t_t2h_m_t :=
  [e| h2t_t2h_s_lowered, env_h2t_t2h.find? ]
reduction_by
       dsimp [h2t_t2h_s_lowered]
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

instance : MatchInterface wire_top_m h2t_t2h_m := by
  dsimp [wire_top_m, h2t_t2h_m]
  solve_match_interface

-- Refinement of the
#print Graphiti.LICircuits.InterfaceCancellation.h2t_t2h_m_t
def φ (i : wire_top_m_t) (s : h2t_t2h_m_t) : Prop :=
  let ⟨ i_d , i_v , i_r⟩ := i

  let ⟨⟨ s_D, s_ro ⟩ , ⟨ s_d , s_v , s_ri ⟩⟩:= s -- TODO : why order is this?!

  s_d = i_d ∧
  s_v = i_v ∧
  s_ri = i_r ∧

  s_ro = s_ri ∧ -- todo : check if prefix or eq

  s_D = to_tokens i_d i_v s_ro


theorem refines' : wire_top_m ⊑_{φ} h2t_t2h_m := by
  sorry

theorem refines_init : Module.refines_initial wire_top_m h2t_t2h_m φ := by
  intro i hi
  obtain ⟨ d,v,r⟩ := i
  simp[wire_top_m, wire_m] at hi

  refine ⟨ ⟨⟨ [],[]⟩ ,⟨[], [], []⟩⟩ ,?_, ?_⟩
  <;> obtain ⟨ rfl, rfl, rfl⟩:= hi
  . simp[h2t_t2h_m, token_to_handshake_m, handshake_to_token_m]
    exact ⟨ rfl, rfl⟩
  . simp[φ]
    exact ⟨ rfl, rfl,rfl⟩





theorem refines : wire_top_m ⊑ h2t_t2h_m := ⟨inferInstance, φ, refines', refines_init⟩

end InterfaceCancellation

end Graphiti.LICircuits
