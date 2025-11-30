/-
Copyright (c) 2024, 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

module

public import Graphiti.Core.Module
public import Graphiti.Core.AssocList.Bijective

public import Mathlib.Tactic.Convert
public import Mathlib.Logic.Function.Basic

@[expose] public section

open Batteries (AssocList)

namespace Graphiti

structure Disjoint {Ident S T} [DecidableEq Ident] (mod1 : Module Ident S) (mod2 : Module Ident T) : Prop where
  inputs_disjoint : mod1.inputs.disjoint_keys mod2.inputs
  outputs_disjoint : mod1.outputs.disjoint_keys mod2.outputs

section Match

/-
The following definition lives in `Type`, I'm not sure if a type class can live
in `Prop` even though it seems to be accepted.
-/

variable {Ident}
variable [DecidableEq Ident]
variable {I S}

/--
Match two interfaces of two modules, which implies that the types of all the
input and output rules match.
-/
class MatchInterface (imod : Module Ident I) (smod : Module Ident S) : Prop where
  inputs_present ident :
    (imod.inputs.find? ident).isSome = (smod.inputs.find? ident).isSome
  outputs_present ident :
    (imod.outputs.find? ident).isSome = (smod.outputs.find? ident).isSome
  input_types ident : (imod.inputs.getIO ident).1 = (smod.inputs.getIO ident).1
  output_types ident : (imod.outputs.getIO ident).1 = (smod.outputs.getIO ident).1

theorem MatchInterface_simpler {imod : Module Ident I} {smod : Module Ident S} :
  (∀ ident, (imod.inputs.mapVal (λ _ => Sigma.fst)).find? ident = (smod.inputs.mapVal (λ _ => Sigma.fst)).find? ident) →
  (∀ ident, (imod.outputs.mapVal (λ _ => Sigma.fst)).find? ident = (smod.outputs.mapVal (λ _ => Sigma.fst)).find? ident) →
  MatchInterface imod smod := by
  intro h1 h2
  constructor
  · intro i; specialize h1 i; specialize h2 i
    cases h : AssocList.find? i imod.inputs <;> cases h' : AssocList.find? i smod.inputs <;> solve | rfl | (simp only [AssocList.find?_mapVal, *] at *; contradiction)
  · intro i; specialize h1 i; specialize h2 i
    cases h : AssocList.find? i imod.outputs <;> cases h' : AssocList.find? i smod.outputs <;> solve | rfl | (simp only [AssocList.find?_mapVal, *] at *; contradiction)
  · intro i; specialize h1 i; specialize h2 i
    dsimp [PortMap.getIO]
    cases h : AssocList.find? i imod.inputs <;> cases h' : AssocList.find? i smod.inputs <;> try solve | rfl | (simp only [AssocList.find?_mapVal, *] at *; contradiction)
    simp only [AssocList.find?_mapVal, *] at *
    rename_i a b; cases a; dsimp at h1; cases h1; rfl
  · intro i; specialize h1 i; specialize h2 i
    dsimp [PortMap.getIO]
    cases h : AssocList.find? i imod.outputs <;> cases h' : AssocList.find? i smod.outputs <;> try solve | rfl | (simp only [AssocList.find?_mapVal, *] at *; contradiction)
    simp only [AssocList.find?_mapVal, *] at *
    rename_i a b; cases a; dsimp at h2; cases h2; rfl

theorem MatchInterface_simpler2 {imod : Module Ident I} {smod : Module Ident S} {ident} :
  MatchInterface imod smod →
  (imod.inputs.mapVal (λ _ => Sigma.fst)).find? ident = (smod.inputs.mapVal (λ _ => Sigma.fst)).find? ident
  ∧ (imod.outputs.mapVal (λ _ => Sigma.fst)).find? ident = (smod.outputs.mapVal (λ _ => Sigma.fst)).find? ident := by
  intro ⟨h1, h2, h3, h4⟩
  specialize h3 ident; specialize h4 ident; specialize h1 ident; specialize h2 ident
  unfold PortMap.getIO at *
  and_intros
  · cases h : AssocList.find? ident imod.inputs <;> cases h' : AssocList.find? ident smod.inputs
    · simp only [AssocList.find?_mapVal, *] at *; rfl
    · simp_all only; contradiction
    · simp_all only; contradiction
    · simp_all only; dsimp at h3
      simp only [AssocList.find?_mapVal, *] at *
      rename_i a b; cases a; cases b; cases h3; rfl
  · cases h : AssocList.find? ident imod.outputs <;> cases h' : AssocList.find? ident smod.outputs
    · simp only [AssocList.find?_mapVal, *] at *; rfl
    · simp_all only; contradiction
    · simp_all only; contradiction
    · simp_all only; dsimp at h4
      simp only [AssocList.find?_mapVal, *] at *
      rename_i a b; cases a; cases b; cases h4; rfl

theorem MatchInterface_simpler_iff {imod : Module Ident I} {smod : Module Ident S} :
  MatchInterface imod smod ↔
  (∀ ident, (imod.inputs.mapVal (λ _ => Sigma.fst)).find? ident = (smod.inputs.mapVal (λ _ => Sigma.fst)).find? ident
  ∧ (imod.outputs.mapVal (λ _ => Sigma.fst)).find? ident = (smod.outputs.mapVal (λ _ => Sigma.fst)).find? ident) := by
  constructor
  · intros; solve_by_elim [MatchInterface_simpler2]
  · intros ha; apply MatchInterface_simpler <;> intro ident <;> specializeAll ident
    · apply ha.left
    · apply ha.right

instance : MatchInterface (@Module.empty Ident S) (Module.empty I) :=
  ⟨ fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl ⟩

instance {m : Module Ident S} : MatchInterface m m :=
  ⟨ fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl ⟩

theorem MatchInterface_EqExt {S} {imod imod' : Module Ident S} :
  imod.EqExt imod' → MatchInterface imod imod' := by
    intros Heq
    unfold Module.EqExt at Heq
    cases Heq; rename_i Hinp Hr
    cases Hr; rename_i Hout Hint
    constructor <;> intros
    · rw [Hinp]
    · rw [Hout]
    · unfold PortMap.getIO; rw [Hinp]
    · unfold PortMap.getIO; rw [Hout]

theorem MatchInterface_transitive {I J S} {imod : Module Ident I} {smod : Module Ident S} (jmod : Module Ident J) :
  MatchInterface imod jmod →
  MatchInterface jmod smod →
  MatchInterface imod smod := by
  intro ⟨ i, j, a, b ⟩ ⟨ k, w, c, d ⟩
  constructor <;> (try simp [*]; done) <;> (intros; simp only [*])

theorem MatchInterface_symmetric {I S} {imod : Module Ident I} (smod : Module Ident S) :
  MatchInterface imod smod →
  MatchInterface smod imod := by
    intro ⟨ i, j, a, b ⟩
    constructor <;> intros
    · rw[i]
    · rw[j]
    · rw[a]
    · rw[b]

-- theorem MatchInterface_Disjoint {I J S K} {imod : Module Ident I} {smod : Module Ident S} {imod' : Module Ident J} {smod' : Module Ident K}
--   [MatchInterface imod smod]
--   [MatchInterface imod' smod'] :
--   Disjoint imod imod' →
--   Disjoint smod smod' := by sorry

instance MatchInterface_connect {I S} {o i} {imod : Module Ident I} {smod : Module Ident S}
         [mm : MatchInterface imod smod]
         : MatchInterface (imod.connect' o i) (smod.connect' o i) := by
  simp only [MatchInterface_simpler_iff] at *; intro ident; specializeAll ident
  obtain ⟨mm1, mm2⟩ := mm
  dsimp [Module.connect']
  constructor
  · simp only [AssocList.eraseAll_map_comm]
    by_cases h : ident = i <;> subst_vars
    · simp only [AssocList.find?_eraseAll_eq]
    · simpa (disch := assumption) only [AssocList.find?_eraseAll_neq]
  · simp only [AssocList.eraseAll_map_comm]
    by_cases h : ident = o <;> subst_vars
    · simp only [AssocList.find?_eraseAll_eq]
    · simpa (disch := assumption) only [AssocList.find?_eraseAll_neq]

theorem MatchInterface_product {I J S T} {imod : Module Ident I} {tmod : Module Ident T}
         {smod : Module Ident S} (jmod : Module Ident J) [inst1 : MatchInterface imod tmod]
         [inst2 : MatchInterface smod jmod] :
         MatchInterface (imod.product smod) (tmod.product jmod) := by
  simp only [MatchInterface_simpler_iff] at *
  intro ident
  specialize inst1 ident; specialize inst2 ident
  obtain ⟨h1, h2⟩ := inst1; obtain ⟨h3, h4⟩ := inst2
  and_intros
  · replace h2 := h3; clear h4; clear h3
    cases h : AssocList.find? ident imod.inputs
      <;> cases h' : AssocList.find? ident smod.inputs
      <;> simp only [AssocList.find?_mapVal, *] at *
      <;> dsimp at *
      <;> (symm at h1 h2; simp -failIfUnchanged only [Option.map_eq_none_iff, Option.map_eq_some_iff] at h1 h2)
    . unfold Module.product; dsimp
      repeat (rw [AssocList.append_find_right] <;> simp only [AssocList.find?_mapVal, *] <;> try rfl)
    · rename_i v0; obtain ⟨v1, hfind, hf⟩ := h2; cases v0; cases v1; cases hf
      unfold Module.product; dsimp
      repeat (rw [AssocList.append_find_right] <;> simp only [AssocList.find?_mapVal, *] <;> try rfl)
    · rename_i v0; obtain ⟨v1, hfind, hf⟩ := h1; cases v0; cases v1; cases hf
      unfold Module.product; dsimp
      repeat rw [AssocList.append_find_left] <;> try solve | (simp only [AssocList.find?_mapVal, *]; rfl)
      rfl
    · rename_i v0; obtain ⟨v1, hfind, hf⟩ := h1; cases v0; cases v1; cases hf
      unfold Module.product; dsimp
      repeat rw [AssocList.append_find_left] <;> try solve | (simp only [AssocList.find?_mapVal, *]; rfl)
      rfl
  · replace h1 := h2; replace h2 := h4; clear h4; clear h3
    cases h : AssocList.find? ident imod.outputs
      <;> cases h' : AssocList.find? ident smod.outputs
      <;> simp only [AssocList.find?_mapVal, *] at *
      <;> dsimp at *
      <;> (symm at h1 h2; simp -failIfUnchanged only [Option.map_eq_none_iff, Option.map_eq_some_iff] at h1 h2)
    . unfold Module.product; dsimp
      repeat (rw [AssocList.append_find_right] <;> simp only [AssocList.find?_mapVal, *] <;> try rfl)
    · rename_i v0; obtain ⟨v1, hfind, hf⟩ := h2; cases v0; cases v1; cases hf
      unfold Module.product; dsimp
      repeat (rw [AssocList.append_find_right] <;> simp only [AssocList.find?_mapVal, *] <;> try rfl)
    · rename_i v0; obtain ⟨v1, hfind, hf⟩ := h1; cases v0; cases v1; cases hf
      unfold Module.product; dsimp
      repeat rw [AssocList.append_find_left] <;> try solve | (simp only [AssocList.find?_mapVal, *]; rfl)
      rfl
    · rename_i v0; obtain ⟨v1, hfind, hf⟩ := h1; cases v0; cases v1; cases hf
      unfold Module.product; dsimp
      repeat rw [AssocList.append_find_left] <;> try solve | (simp only [AssocList.find?_mapVal, *]; rfl)
      rfl

instance MatchInterface_product_instance {I J S T} {imod : Module Ident I} {tmod : Module Ident T}
         {smod : Module Ident S} (jmod : Module Ident J) [MatchInterface imod tmod]
         [MatchInterface smod jmod] :
         MatchInterface (imod.product smod) (tmod.product jmod) := by apply MatchInterface_product

theorem match_interface_inputs_contains {I S} {imod : Module Ident I} {smod : Module Ident S}
  [MatchInterface imod smod] {k}:
  imod.inputs.contains k ↔ smod.inputs.contains k := by
  rcases ‹MatchInterface _ _› with ⟨a, b, c, d⟩
  simp only [←AssocList.contains_find?_isSome_iff]
  rw [a]

theorem match_interface_outputs_contains {I S} {imod : Module Ident I} {smod : Module Ident S}
  [MatchInterface imod smod] {k}:
  imod.outputs.contains k ↔ smod.outputs.contains k := by
  rcases ‹MatchInterface _ _› with ⟨a, b, c, d⟩
  simp only [←AssocList.contains_find?_isSome_iff]
  rw [b]

theorem MatchInterface_mapInputPorts {I S} {imod : Module Ident I}
         {smod : Module Ident S} [inst : MatchInterface imod smod] {f} :
         Function.Bijective f →
         MatchInterface (imod.mapInputPorts f) (smod.mapInputPorts f) := by
  simp only [MatchInterface_simpler_iff] at *
  intro hf ident
  have hinj := hf.injective
  have hbij := (Function.bijective_iff_existsUnique f).mp hf ident
  obtain ⟨ha, hb1, hb2⟩ := hbij; subst ident
  obtain ⟨h1, h2⟩ := inst ha; obtain ⟨h1', h2'⟩ := inst (f ha); clear inst
  and_intros <;> (simp (disch := assumption) only [Module.mapInputPorts, AssocList.find?_mapVal, AssocList.mapKey_find?] at *; assumption)

theorem MatchInterface_mapOutputPorts {I S} {imod : Module Ident I}
         {smod : Module Ident S} [inst : MatchInterface imod smod] {f} :
         Function.Bijective f →
         MatchInterface (imod.mapOutputPorts f) (smod.mapOutputPorts f) := by
  simp only [MatchInterface_simpler_iff] at *
  intro hf ident
  have hinj := hf.injective
  have hbij := (Function.bijective_iff_existsUnique f).mp hf ident
  obtain ⟨ha, hb1, hb2⟩ := hbij; subst ident
  obtain ⟨h1, h2⟩ := inst ha; obtain ⟨h1', h2'⟩ := inst (f ha); clear inst
  and_intros <;> (simp (disch := assumption) only [Module.mapOutputPorts, AssocList.find?_mapVal, AssocList.mapKey_find?] at *; assumption)

set_option maxHeartbeats 0 in
instance MatchInterface_product_associative {I S J} {imod : Module Ident I} {smod : Module Ident S} {jmod : Module Ident J} : MatchInterface (imod.product (smod.product jmod)) ((imod.product smod).product jmod) := by
  simp only [MatchInterface_simpler_iff] at *
  intro ident
  and_intros
  · dsimp [Module.product];
    repeat rw [AssocList.find?_mapVal]
    cases himod : imod.inputs.find? ident
    · cases hsmod : smod.inputs.find? ident
      · cases hjmod : jmod.inputs.find? ident
        · repeat1 ((try rw [AssocList.find?_mapVal]); rw [AssocList.append_find_right])
          any_goals simp [*, AssocList.find?_mapVal, -AssocList.find?_eq]
          repeat1 ((try rw [AssocList.find?_mapVal]); rw [AssocList.append_find_right])
          all_goals simp [*, AssocList.find?_mapVal, -AssocList.find?_eq]
        · repeat1 ((try rw [AssocList.find?_mapVal]); rw [AssocList.append_find_right])
          any_goals simp [*, AssocList.find?_mapVal, -AssocList.find?_eq]
          rfl
          repeat1 ((try rw [AssocList.find?_mapVal]); rw [AssocList.append_find_right])
          all_goals simp [*, AssocList.find?_mapVal, -AssocList.find?_eq]
      · rename_i v
        conv =>
          lhs; rw [AssocList.append_find_right, AssocList.find?_mapVal, AssocList.append_find_left (x := Module.liftL v)]
          dsimp; rfl
          rw [AssocList.find?_mapVal, hsmod]; rfl
          rw [AssocList.find?_mapVal, himod]; rfl
        conv =>
          rhs; rw [AssocList.append_find_left (x := Module.liftL (Module.liftR v))]; dsimp; rfl
          rw [AssocList.find?_mapVal, AssocList.append_find_right, AssocList.find?_mapVal, hsmod]; rfl
          rw [AssocList.find?_mapVal, himod]
        rfl
    · rename_i v
      conv =>
        lhs; rw [AssocList.append_find_left (x := Module.liftL v)]; dsimp; rfl
        rw [AssocList.find?_mapVal, himod]; rfl
      conv =>
        rhs; rw [AssocList.append_find_left (x := Module.liftL (Module.liftL v))]; dsimp; rfl
        rw [AssocList.find?_mapVal, AssocList.append_find_left (x := Module.liftL v)]; dsimp; rfl
        rw [AssocList.find?_mapVal, himod]; rfl
      rfl
  · dsimp [Module.product];
    repeat rw [AssocList.find?_mapVal]
    cases himod : imod.outputs.find? ident
    · cases hsmod : smod.outputs.find? ident
      · cases hjmod : jmod.outputs.find? ident
        · repeat1 ((try rw [AssocList.find?_mapVal]); rw [AssocList.append_find_right])
          any_goals simp [*, AssocList.find?_mapVal, -AssocList.find?_eq]
          repeat1 ((try rw [AssocList.find?_mapVal]); rw [AssocList.append_find_right])
          all_goals simp [*, AssocList.find?_mapVal, -AssocList.find?_eq]
        · repeat1 ((try rw [AssocList.find?_mapVal]); rw [AssocList.append_find_right])
          any_goals simp [*, AssocList.find?_mapVal, -AssocList.find?_eq]
          rfl
          repeat1 ((try rw [AssocList.find?_mapVal]); rw [AssocList.append_find_right])
          all_goals simp [*, AssocList.find?_mapVal, -AssocList.find?_eq]
      · rename_i v
        conv =>
          lhs; rw [AssocList.append_find_right, AssocList.find?_mapVal, AssocList.append_find_left (x := Module.liftL v)]
          dsimp; rfl
          rw [AssocList.find?_mapVal, hsmod]; rfl
          rw [AssocList.find?_mapVal, himod]; rfl
        conv =>
          rhs; rw [AssocList.append_find_left (x := Module.liftL (Module.liftR v))]; dsimp; rfl
          rw [AssocList.find?_mapVal, AssocList.append_find_right, AssocList.find?_mapVal, hsmod]; rfl
          rw [AssocList.find?_mapVal, himod]
        rfl
    · rename_i v
      conv =>
        lhs; rw [AssocList.append_find_left (x := Module.liftL v)]; dsimp; rfl
        rw [AssocList.find?_mapVal, himod]; rfl
      conv =>
        rhs; rw [AssocList.append_find_left (x := Module.liftL (Module.liftL v))]; dsimp; rfl
        rw [AssocList.find?_mapVal, AssocList.append_find_left (x := Module.liftL v)]; dsimp; rfl
        rw [AssocList.find?_mapVal, himod]; rfl
      rfl

instance MatchInterface_product_associative' {I S J} {imod : Module Ident I} {smod : Module Ident S} {jmod : Module Ident J}
  : MatchInterface ((imod.product smod).product jmod) (imod.product (smod.product jmod))
  := MatchInterface_symmetric _ MatchInterface_product_associative

theorem MatchInterface_product_commutative {I S} {imod : Module Ident I} {smod : Module Ident S}
  (h : Disjoint imod smod)
  : MatchInterface (imod.product smod) (smod.product imod) := by
  simp only [MatchInterface_simpler_iff] at *
  intro ident
  obtain ⟨hl, hr⟩ := h
  and_intros
  · unfold Module.product; dsimp
    cases himod : imod.inputs.find? ident
    · cases hsmod : smod.inputs.find? ident
      · rewrite [AssocList.find?_mapVal, AssocList.find?_mapVal, AssocList.append_find_right, AssocList.append_find_right,
                 AssocList.find?_mapVal, AssocList.find?_mapVal, himod, hsmod]; rfl
        · rewrite [AssocList.find?_mapVal, hsmod]; rfl
        · rewrite [AssocList.find?_mapVal, himod]; rfl
      · rename_i v
        rewrite [AssocList.find?_mapVal, AssocList.find?_mapVal, AssocList.append_find_right, AssocList.find?_mapVal, hsmod,
                 AssocList.append_find_left (x := Module.liftL v)]; rfl
        · rewrite [AssocList.find?_mapVal, hsmod]; rfl
        · rewrite [AssocList.find?_mapVal, himod]; rfl
    · rename_i v
      have hsmod := AssocList.disjoint_keys_find_some hl himod
      rewrite [AssocList.find?_mapVal, AssocList.find?_mapVal, AssocList.append_find_left (x := Module.liftL v),
               AssocList.append_find_right, AssocList.find?_mapVal, himod]; rfl
      · rewrite [AssocList.find?_mapVal, hsmod]; rfl
      · rewrite [AssocList.find?_mapVal, himod]; rfl
  · unfold Module.product; dsimp
    cases himod : imod.outputs.find? ident
    · cases hsmod : smod.outputs.find? ident
      · rewrite [AssocList.find?_mapVal, AssocList.find?_mapVal, AssocList.append_find_right, AssocList.append_find_right,
                 AssocList.find?_mapVal, AssocList.find?_mapVal, himod, hsmod]; rfl
        · rewrite [AssocList.find?_mapVal, hsmod]; rfl
        · rewrite [AssocList.find?_mapVal, himod]; rfl
      · rename_i v
        rewrite [AssocList.find?_mapVal, AssocList.find?_mapVal, AssocList.append_find_right, AssocList.find?_mapVal, hsmod,
                 AssocList.append_find_left (x := Module.liftL v)]; rfl
        · rewrite [AssocList.find?_mapVal, hsmod]; rfl
        · rewrite [AssocList.find?_mapVal, himod]; rfl
    · rename_i v
      have hsmod := AssocList.disjoint_keys_find_some hr himod
      rewrite [AssocList.find?_mapVal, AssocList.find?_mapVal, AssocList.append_find_left (x := Module.liftL v),
               AssocList.append_find_right, AssocList.find?_mapVal, himod]; rfl
      · rewrite [AssocList.find?_mapVal, hsmod]; rfl
      · rewrite [AssocList.find?_mapVal, himod]; rfl

end Match

theorem existSR_reflexive {S} {rules : List (RelInt S)} {s} :
  existSR rules s s := existSR.done s

theorem existSR_transitive {S} (rules : List (RelInt S)) :
  ∀ s₁ s₂ s₃,
    existSR rules s₁ s₂ →
    existSR rules s₂ s₃ →
    existSR rules s₁ s₃ := by
  intro s₁ s₂ s₃ He1 He2
  induction He1 generalizing s₃; assumption
  constructor; all_goals solve_by_elim

theorem existSR_append_left {S} (rules₁ rules₂ : List (RelInt S)) :
  ∀ s₁ s₂,
    existSR rules₁ s₁ s₂ →
    existSR (rules₁ ++ rules₂) s₁ s₂ := by
  intro s₁ s₂ hrule
  induction hrule with
  | done => constructor
  | step init mid final rule hrulein hrule hex =>
    apply existSR.step (rule := rule) (mid := mid) <;> simp [*]

theorem existSR_append_right {S} (rules₁ rules₂ : List (RelInt S)) :
  ∀ s₁ s₂,
    existSR rules₂ s₁ s₂ →
    existSR (rules₁ ++ rules₂) s₁ s₂ := by
  intro s₁ s₂ hrule
  induction hrule with
  | done => constructor
  | step init mid final rule hrulein hrule hex =>
    apply existSR.step (rule := rule) (mid := mid) <;> simp [*]

theorem existSR_liftL' {S T} (rules : List (RelInt S)) :
  ∀ s₁ s₂ (t₁ : T),
    existSR rules s₁ s₂ →
    existSR (rules.map Module.liftL') (s₁, t₁) (s₂, t₁) := by
  intro s₁ s₂ t₁ hrule
  induction hrule with
  | done => constructor
  | step init mid final rule hrulein hrule hex ih =>
    apply existSR.step (rule := @Module.liftL' S T rule) (mid := (mid, t₁)) <;> try assumption
    simp; exists rule
    simp [*, Module.liftL']

theorem existSR_liftR' {S T} (rules : List (RelInt S)) :
  ∀ s₁ s₂ (t₁ : T),
    existSR rules s₁ s₂ →
    existSR (rules.map Module.liftR') (t₁, s₁) (t₁, s₂) := by
  intro s₁ s₂ t₁ hrule
  induction hrule with
  | done => constructor
  | step init mid final rule hrulein hrule hex ih =>
    apply existSR.step (rule := @Module.liftR' T S rule) (mid := (t₁, mid)) <;> try assumption
    simp; exists rule
    simp [*, Module.liftR']

theorem existSR_cons {S} {r} {rules : List (RelInt S)} :
  ∀ s₁ s₂,
    existSR rules s₁ s₂ →
    existSR (r :: rules) s₁ s₂ := by
  intro s₁ s₂ hrule
  induction hrule with
  | done => constructor
  | step init mid final rule hrulein hrule hex ih =>
    constructor; right; assumption; assumption; assumption

theorem existSR_single_step {S : Type _} (rules : List (S → S → Prop)):
  ∀ s s', ∀ rule ∈ rules, rule s s' → existSR rules s s' := by
    intros s₁ s₂ rule _ _
    apply existSR.step s₁ s₂ s₂ rule
    . assumption
    . assumption
    . exact existSR_reflexive

theorem existSR_single_step' {S : Type _} (rules : List (S → S → Prop)):
  ∀ s₁ s₂, (∃ r ∈ rules, r s₁ s₂) → existSR rules s₁ s₂ := by
    intros s₁ s₂ h
    obtain ⟨r, _, _⟩ := h
    apply existSR.step s₁ s₂ s₂ r
    . assumption
    . assumption
    . exact existSR_reflexive

theorem existSR_norules {S: Type _}: ∀ (s₁ s₂: S), existSR [] s₁ s₂ → s₁ = s₂ := by
  intro s₁ s₂ h
  cases h with
  | done => rfl
  | step _ _ _ _ h => cases h

namespace Module

section Refinementφ

variable {I : Type _}
variable {S : Type _}
variable {Ident : Type _}
variable [DecidableEq Ident]

variable (imod : Module Ident I)
variable (smod : Module Ident S)

variable [mm : MatchInterface imod smod]

structure comp_refines (φ : I → S → Prop) (init_i : I) (init_s : S) : Prop where
  inputs :
    ∀ ident mid_i v,
      (imod.inputs.getIO ident).2 init_i v mid_i →
      ∃ almost_mid_s mid_s,
        (smod.inputs.getIO ident).2 init_s ((mm.input_types ident).mp v) almost_mid_s
        ∧ existSR smod.internals almost_mid_s mid_s
        ∧ φ mid_i mid_s
  outputs :
    ∀ ident mid_i v,
      (imod.outputs.getIO ident).2 init_i v mid_i →
      ∃ almost_mid_s mid_s,
        existSR smod.internals init_s almost_mid_s
        ∧ (smod.outputs.getIO ident).2 almost_mid_s ((mm.output_types ident).mp v) mid_s
        ∧ φ mid_i mid_s
  internals :
    ∀ rule mid_i,
      rule ∈ imod.internals →
      rule init_i mid_i →
      ∃ mid_s,
        existSR smod.internals init_s mid_s
        ∧ φ mid_i mid_s

structure comp_refines' (φ : I → S → Prop) (init_i : I) (init_s : S) : Prop where
  inputs :
    ∀ ident mid_i v,
      (imod.inputs.getIO ident).2 init_i v mid_i →
      ∃ almost_mid_s mid_s,
        (smod.inputs.getIO ident).2 init_s ((mm.input_types ident).mp v) almost_mid_s
        ∧ existSR smod.internals almost_mid_s mid_s
        ∧ φ mid_i mid_s
  outputs :
    ∀ ident mid_i v,
      (imod.outputs.getIO ident).2 init_i v mid_i →
      ∃ almost_mid_s mid_s,
        (smod.outputs.getIO ident).2 init_s ((mm.output_types ident).mp v) almost_mid_s
        ∧ existSR smod.internals almost_mid_s mid_s
        ∧ φ mid_i mid_s
  internals :
    ∀ rule mid_i,
      rule ∈ imod.internals →
      rule init_i mid_i →
      ∃ mid_s,
        existSR smod.internals init_s mid_s
        ∧ φ mid_i mid_s

theorem imod_eq_in {f} {ident} : (imod.mapInputPorts f).outputs.getIO ident = imod.outputs.getIO ident := rfl
theorem smod_eq_in {f} {ident} : (smod.mapInputPorts f).outputs.getIO ident = smod.outputs.getIO ident := rfl
theorem imod_eq_out {f} {ident} : (imod.mapOutputPorts f).inputs.getIO ident = imod.inputs.getIO ident := rfl
theorem smod_eq_out {f} {ident} : (smod.mapOutputPorts f).inputs.getIO ident = smod.inputs.getIO ident := rfl

theorem product_take_right_in {ident} {J} {imod₂ : Module Ident J}:
  imod.inputs.find? ident = none →
  (imod.product imod₂).inputs.getIO ident = liftR (imod₂.inputs.getIO ident) := by
  intros;
  dsimp [product, PortMap.getIO]
  cases hinps₂ : imod₂.inputs.find? ident
  · rw [AssocList.append_find_right] <;> simp only [AssocList.find?_mapVal, *]; dsimp [liftR]
    congr; simp
    rfl
  · rw [AssocList.append_find_right] <;> simp only [AssocList.find?_mapVal, *]; dsimp [liftR]; rfl

theorem product_take_right_out {ident} {J} {imod₂ : Module Ident J}:
  imod.outputs.find? ident = none →
  (imod.product imod₂).outputs.getIO ident = liftR (imod₂.outputs.getIO ident) := by
  intros;
  dsimp [product, PortMap.getIO]
  cases hinps₂ : imod₂.outputs.find? ident
  · rw [AssocList.append_find_right] <;> simp only [AssocList.find?_mapVal, *]; dsimp [liftR]
    congr; simp
    rfl
  · rw [AssocList.append_find_right] <;> simp only [AssocList.find?_mapVal, *]; dsimp [liftR]; rfl

theorem product_take_left_in {ident} {J} {imod₂ : Module Ident J} {v}:
  imod.inputs.find? ident = some v →
  (imod.product imod₂).inputs.getIO ident = liftL v := by
  intros ha;
  dsimp [product, PortMap.getIO]
  rw [AssocList.append_find_left (by simp only [AssocList.find?_mapVal, ha]; rfl)]
  rfl

theorem product_take_left_out {ident} {J} {imod₂ : Module Ident J} {v}:
  imod.outputs.find? ident = some v →
  (imod.product imod₂).outputs.getIO ident = liftL v := by
  intros ha;
  dsimp [product, PortMap.getIO]
  rw [AssocList.append_find_left (by simp only [AssocList.find?_mapVal, ha]; rfl)]
  rfl

omit mm in
theorem rule_product_associative_input {J} (jmod : Module Ident J) {i₁ i₂ i₃} {new_i new_s new_j} {ident} {v}:
  ((imod.product (smod.product jmod)).inputs.getIO ident).snd (i₁, i₂, i₃) v (new_i, new_s, new_j) →
  (((imod.product smod).product jmod).inputs.getIO ident).snd ((i₁, i₂), i₃) ((MatchInterface.input_types ident).mp v) ((new_i, new_s), new_j) := by
  intro rule
  cases h1 : imod.inputs.find? ident
  · cases h2 : smod.inputs.find? ident
    · cases h3 : jmod.inputs.find? ident
      · have := PortMap.getIO_not_contained_false rule
          (by
            intro hcont
            dsimp [Module.product] at hcont
            simp only [AssocList.contains_append, AssocList.contains_mapval] at hcont
            rw [AssocList.contains_find?_none_iff] at h1 h2 h3
            rw [h1, h2, h3] at hcont
            contradiction
          )
        contradiction
      · rename_i rule'
        have imp : (imod.product (smod.product jmod)).inputs.getIO ident = liftR (liftR rule') := by
          dsimp [Module.product, PortMap.getIO]
          rewrite [AssocList.append_find_right, AssocList.find?_mapVal, AssocList.append_find_right, AssocList.find?_mapVal, h3]; rfl
          · rewrite [AssocList.find?_mapVal, h2]; rfl
          · rewrite [AssocList.find?_mapVal, h1]; rfl
        have spec : ((imod.product smod).product jmod).inputs.getIO ident = liftR rule' := by
          dsimp [Module.product, PortMap.getIO]
          rewrite [AssocList.append_find_right, AssocList.find?_mapVal, h3]; rfl
          rewrite [AssocList.find?_mapVal, AssocList.append_find_right, AssocList.find?_mapVal, h2]; rfl
          rewrite [AssocList.find?_mapVal, h1]; rfl
        rewrite [PortMap.rw_rule_execution (by rw [spec])]
        rewrite [PortMap.rw_rule_execution (by rw [imp])] at rule
        dsimp [liftR] at *
        obtain ⟨⟨rule, r2⟩, r3⟩ := rule; subst_vars
        constructor <;> try rfl
        convert rule; simp
    · rename_i rule'
      have imp : (imod.product (smod.product jmod)).inputs.getIO ident = liftR (liftL rule') := by
        dsimp [Module.product, PortMap.getIO]
        rewrite [AssocList.append_find_right, AssocList.find?_mapVal, AssocList.append_find_left]; rfl
        · rewrite [AssocList.find?_mapVal, h2]; rfl
        · rewrite [AssocList.find?_mapVal, h1]; rfl
      have spec : ((imod.product smod).product jmod).inputs.getIO ident = liftL (liftR rule') := by
        dsimp [Module.product, PortMap.getIO]
        rewrite [AssocList.append_find_left]; rfl
        rewrite [AssocList.find?_mapVal, AssocList.append_find_right, AssocList.find?_mapVal, h2]; rfl
        rewrite [AssocList.find?_mapVal, h1]; rfl
      rewrite [PortMap.rw_rule_execution (by rw [spec])]
      rewrite [PortMap.rw_rule_execution (by rw [imp])] at rule
      dsimp [liftR] at *
      obtain ⟨⟨rule, r2⟩, r3⟩ := rule; subst_vars
      constructor <;> try rfl
      convert rule; simp
  · rename_i rule'
    have imp : (imod.product (smod.product jmod)).inputs.getIO ident = liftL rule' := by
      dsimp [Module.product, PortMap.getIO]
      rewrite [AssocList.append_find_left]; rfl
      rewrite [AssocList.find?_mapVal, h1]; rfl
    have spec : ((imod.product smod).product jmod).inputs.getIO ident = liftL (liftL rule') := by
      dsimp [Module.product, PortMap.getIO]
      rewrite [AssocList.append_find_left]; rfl
      rewrite [AssocList.find?_mapVal, AssocList.append_find_left]; rfl
      rewrite [AssocList.find?_mapVal, h1]; rfl
    rewrite [PortMap.rw_rule_execution (by rw [spec])]
    rewrite [PortMap.rw_rule_execution (by rw [imp])] at rule
    dsimp [liftR, liftL] at *
    obtain ⟨rule, r3⟩ := rule; subst_vars
    cases r3
    constructor <;> try rfl
    convert rule; simp

omit mm in
theorem rule_product_associative_output {J} (jmod : Module Ident J) {i₁ i₂ i₃} {new_i new_s new_j} {ident} {v}:
  ((imod.product (smod.product jmod)).outputs.getIO ident).snd (i₁, i₂, i₃) v (new_i, new_s, new_j) →
  (((imod.product smod).product jmod).outputs.getIO ident).snd ((i₁, i₂), i₃) ((MatchInterface.output_types ident).mp v) ((new_i, new_s), new_j) := by
  intro rule
  cases h1 : imod.outputs.find? ident
  · cases h2 : smod.outputs.find? ident
    · cases h3 : jmod.outputs.find? ident
      · have := PortMap.getIO_not_contained_false rule
          (by
            intro hcont
            dsimp [Module.product] at hcont
            simp only [AssocList.contains_append, AssocList.contains_mapval] at hcont
            rw [AssocList.contains_find?_none_iff] at h1 h2 h3
            rw [h1, h2, h3] at hcont
            contradiction
          )
        contradiction
      · rename_i rule'
        have imp : (imod.product (smod.product jmod)).outputs.getIO ident = liftR (liftR rule') := by
          dsimp [Module.product, PortMap.getIO]
          rewrite [AssocList.append_find_right, AssocList.find?_mapVal, AssocList.append_find_right, AssocList.find?_mapVal, h3]; rfl
          · rewrite [AssocList.find?_mapVal, h2]; rfl
          · rewrite [AssocList.find?_mapVal, h1]; rfl
        have spec : ((imod.product smod).product jmod).outputs.getIO ident = liftR rule' := by
          dsimp [Module.product, PortMap.getIO]
          rewrite [AssocList.append_find_right, AssocList.find?_mapVal, h3]; rfl
          rewrite [AssocList.find?_mapVal, AssocList.append_find_right, AssocList.find?_mapVal, h2]; rfl
          rewrite [AssocList.find?_mapVal, h1]; rfl
        rewrite [PortMap.rw_rule_execution (by rw [spec])]
        rewrite [PortMap.rw_rule_execution (by rw [imp])] at rule
        dsimp [liftR] at *
        obtain ⟨⟨rule, r2⟩, r3⟩ := rule; subst_vars
        constructor <;> try rfl
        convert rule; simp
    · rename_i rule'
      have imp : (imod.product (smod.product jmod)).outputs.getIO ident = liftR (liftL rule') := by
        dsimp [Module.product, PortMap.getIO]
        rewrite [AssocList.append_find_right, AssocList.find?_mapVal, AssocList.append_find_left]; rfl
        · rewrite [AssocList.find?_mapVal, h2]; rfl
        · rewrite [AssocList.find?_mapVal, h1]; rfl
      have spec : ((imod.product smod).product jmod).outputs.getIO ident = liftL (liftR rule') := by
        dsimp [Module.product, PortMap.getIO]
        rewrite [AssocList.append_find_left]; rfl
        rewrite [AssocList.find?_mapVal, AssocList.append_find_right, AssocList.find?_mapVal, h2]; rfl
        rewrite [AssocList.find?_mapVal, h1]; rfl
      rewrite [PortMap.rw_rule_execution (by rw [spec])]
      rewrite [PortMap.rw_rule_execution (by rw [imp])] at rule
      dsimp [liftR] at *
      obtain ⟨⟨rule, r2⟩, r3⟩ := rule; subst_vars
      constructor <;> try rfl
      convert rule; simp
  · rename_i rule'
    have imp : (imod.product (smod.product jmod)).outputs.getIO ident = liftL rule' := by
      dsimp [Module.product, PortMap.getIO]
      rewrite [AssocList.append_find_left]; rfl
      rewrite [AssocList.find?_mapVal, h1]; rfl
    have spec : ((imod.product smod).product jmod).outputs.getIO ident = liftL (liftL rule') := by
      dsimp [Module.product, PortMap.getIO]
      rewrite [AssocList.append_find_left]; rfl
      rewrite [AssocList.find?_mapVal, AssocList.append_find_left]; rfl
      rewrite [AssocList.find?_mapVal, h1]; rfl
    rewrite [PortMap.rw_rule_execution (by rw [spec])]
    rewrite [PortMap.rw_rule_execution (by rw [imp])] at rule
    dsimp [liftR, liftL] at *
    obtain ⟨rule, r3⟩ := rule; subst_vars
    cases r3
    constructor <;> try rfl
    convert rule; simp

omit mm in
theorem rule_product_associative'_input {J} (jmod : Module Ident J) {i₁ i₂ i₃} {new_i new_s new_j} {ident} {v}:
  (((imod.product smod).product jmod).inputs.getIO ident).snd ((i₁, i₂), i₃) v ((new_i, new_s), new_j) →
  ((imod.product (smod.product jmod)).inputs.getIO ident).snd (i₁, i₂, i₃) ((MatchInterface.input_types ident).mp v) (new_i, new_s, new_j) := by
  intro rule
  cases h1 : imod.inputs.find? ident
  · cases h2 : smod.inputs.find? ident
    · cases h3 : jmod.inputs.find? ident
      · have := PortMap.getIO_not_contained_false rule
          (by
            intro hcont
            dsimp [Module.product] at hcont
            simp only [AssocList.contains_append, AssocList.contains_mapval] at hcont
            rw [AssocList.contains_find?_none_iff] at h1 h2 h3
            rw [h1, h2, h3] at hcont
            contradiction
          )
        contradiction
      · rename_i rule'
        have imp : (imod.product (smod.product jmod)).inputs.getIO ident = liftR (liftR rule') := by
          dsimp [Module.product, PortMap.getIO]
          rewrite [AssocList.append_find_right, AssocList.find?_mapVal, AssocList.append_find_right, AssocList.find?_mapVal, h3]; rfl
          · rewrite [AssocList.find?_mapVal, h2]; rfl
          · rewrite [AssocList.find?_mapVal, h1]; rfl
        have spec : ((imod.product smod).product jmod).inputs.getIO ident = liftR rule' := by
          dsimp [Module.product, PortMap.getIO]
          rewrite [AssocList.append_find_right, AssocList.find?_mapVal, h3]; rfl
          rewrite [AssocList.find?_mapVal, AssocList.append_find_right, AssocList.find?_mapVal, h2]; rfl
          rewrite [AssocList.find?_mapVal, h1]; rfl
        rewrite [PortMap.rw_rule_execution (by rw [imp])]
        rewrite [PortMap.rw_rule_execution (by rw [spec])] at rule
        dsimp [liftR, liftL] at *
        obtain ⟨rule, r3⟩ := rule; subst_vars; cases r3
        constructor <;> try rfl
        convert rule; simp
    · rename_i rule'
      have imp : (imod.product (smod.product jmod)).inputs.getIO ident = liftR (liftL rule') := by
        dsimp [Module.product, PortMap.getIO]
        rewrite [AssocList.append_find_right, AssocList.find?_mapVal, AssocList.append_find_left]; rfl
        · rewrite [AssocList.find?_mapVal, h2]; rfl
        · rewrite [AssocList.find?_mapVal, h1]; rfl
      have spec : ((imod.product smod).product jmod).inputs.getIO ident = liftL (liftR rule') := by
        dsimp [Module.product, PortMap.getIO]
        rewrite [AssocList.append_find_left]; rfl
        rewrite [AssocList.find?_mapVal, AssocList.append_find_right, AssocList.find?_mapVal, h2]; rfl
        rewrite [AssocList.find?_mapVal, h1]; rfl
      rewrite [PortMap.rw_rule_execution (by rw [imp])]
      rewrite [PortMap.rw_rule_execution (by rw [spec])] at rule
      dsimp [liftR, liftL] at *
      obtain ⟨⟨rule, r2⟩, r3⟩ := rule; subst_vars
      constructor <;> try rfl
      convert rule; simp
  · rename_i rule'
    have imp : (imod.product (smod.product jmod)).inputs.getIO ident = liftL rule' := by
      dsimp [Module.product, PortMap.getIO]
      rewrite [AssocList.append_find_left]; rfl
      rewrite [AssocList.find?_mapVal, h1]; rfl
    have spec : ((imod.product smod).product jmod).inputs.getIO ident = liftL (liftL rule') := by
      dsimp [Module.product, PortMap.getIO]
      rewrite [AssocList.append_find_left]; rfl
      rewrite [AssocList.find?_mapVal, AssocList.append_find_left]; rfl
      rewrite [AssocList.find?_mapVal, h1]; rfl
    rewrite [PortMap.rw_rule_execution (by rw [imp])]
    rewrite [PortMap.rw_rule_execution (by rw [spec])] at rule
    dsimp [liftR, liftL] at *
    obtain ⟨⟨rule, r2⟩, r3⟩ := rule; subst_vars
    constructor <;> try rfl
    convert rule; simp

omit mm in
theorem rule_product_associative'_output {J} (jmod : Module Ident J) {i₁ i₂ i₃} {new_i new_s new_j} {ident} {v}:
  (((imod.product smod).product jmod).outputs.getIO ident).snd ((i₁, i₂), i₃) v ((new_i, new_s), new_j) →
  ((imod.product (smod.product jmod)).outputs.getIO ident).snd (i₁, i₂, i₃) ((MatchInterface.output_types ident).mp v) (new_i, new_s, new_j) := by
  intro rule
  cases h1 : imod.outputs.find? ident
  · cases h2 : smod.outputs.find? ident
    · cases h3 : jmod.outputs.find? ident
      · have := PortMap.getIO_not_contained_false rule
          (by
            intro hcont
            dsimp [Module.product] at hcont
            simp only [AssocList.contains_append, AssocList.contains_mapval] at hcont
            rw [AssocList.contains_find?_none_iff] at h1 h2 h3
            rw [h1, h2, h3] at hcont
            contradiction
          )
        contradiction
      · rename_i rule'
        have imp : (imod.product (smod.product jmod)).outputs.getIO ident = liftR (liftR rule') := by
          dsimp [Module.product, PortMap.getIO]
          rewrite [AssocList.append_find_right, AssocList.find?_mapVal, AssocList.append_find_right, AssocList.find?_mapVal, h3]; rfl
          · rewrite [AssocList.find?_mapVal, h2]; rfl
          · rewrite [AssocList.find?_mapVal, h1]; rfl
        have spec : ((imod.product smod).product jmod).outputs.getIO ident = liftR rule' := by
          dsimp [Module.product, PortMap.getIO]
          rewrite [AssocList.append_find_right, AssocList.find?_mapVal, h3]; rfl
          rewrite [AssocList.find?_mapVal, AssocList.append_find_right, AssocList.find?_mapVal, h2]; rfl
          rewrite [AssocList.find?_mapVal, h1]; rfl
        rewrite [PortMap.rw_rule_execution (by rw [imp])]
        rewrite [PortMap.rw_rule_execution (by rw [spec])] at rule
        dsimp [liftR, liftL] at *
        obtain ⟨rule, r3⟩ := rule; subst_vars; cases r3
        constructor <;> try rfl
        convert rule; simp
    · rename_i rule'
      have imp : (imod.product (smod.product jmod)).outputs.getIO ident = liftR (liftL rule') := by
        dsimp [Module.product, PortMap.getIO]
        rewrite [AssocList.append_find_right, AssocList.find?_mapVal, AssocList.append_find_left]; rfl
        · rewrite [AssocList.find?_mapVal, h2]; rfl
        · rewrite [AssocList.find?_mapVal, h1]; rfl
      have spec : ((imod.product smod).product jmod).outputs.getIO ident = liftL (liftR rule') := by
        dsimp [Module.product, PortMap.getIO]
        rewrite [AssocList.append_find_left]; rfl
        rewrite [AssocList.find?_mapVal, AssocList.append_find_right, AssocList.find?_mapVal, h2]; rfl
        rewrite [AssocList.find?_mapVal, h1]; rfl
      rewrite [PortMap.rw_rule_execution (by rw [imp])]
      rewrite [PortMap.rw_rule_execution (by rw [spec])] at rule
      dsimp [liftR, liftL] at *
      obtain ⟨⟨rule, r2⟩, r3⟩ := rule; subst_vars
      constructor <;> try rfl
      convert rule; simp
  · rename_i rule'
    have imp : (imod.product (smod.product jmod)).outputs.getIO ident = liftL rule' := by
      dsimp [Module.product, PortMap.getIO]
      rewrite [AssocList.append_find_left]; rfl
      rewrite [AssocList.find?_mapVal, h1]; rfl
    have spec : ((imod.product smod).product jmod).outputs.getIO ident = liftL (liftL rule') := by
      dsimp [Module.product, PortMap.getIO]
      rewrite [AssocList.append_find_left]; rfl
      rewrite [AssocList.find?_mapVal, AssocList.append_find_left]; rfl
      rewrite [AssocList.find?_mapVal, h1]; rfl
    rewrite [PortMap.rw_rule_execution (by rw [imp])]
    rewrite [PortMap.rw_rule_execution (by rw [spec])] at rule
    dsimp [liftR, liftL] at *
    obtain ⟨⟨rule, r2⟩, r3⟩ := rule; subst_vars
    constructor <;> try rfl
    convert rule; simp

omit mm in
theorem rule_product_commutative_input {i₁ i₂} {mid_i mid_s} {ident} {v} (h : Disjoint imod smod) :
  have _ := MatchInterface_product_commutative h
  ((imod.product smod).inputs.getIO ident).snd (i₁, i₂) v (mid_i, mid_s) →
  ((smod.product imod).inputs.getIO ident).snd (i₂, i₁) ((MatchInterface.input_types ident).mp v) (mid_s, mid_i) := by
  intro _ rule
  cases h1 : imod.inputs.find? ident
  · cases h2 : smod.inputs.find? ident
    · have := PortMap.getIO_not_contained_false rule
                (by
                  intro hcont
                  dsimp [Module.product] at hcont
                  simp only [AssocList.contains_append, AssocList.contains_mapval] at hcont
                  rw [AssocList.contains_find?_none_iff] at h1 h2
                  rw [h1, h2] at hcont
                  contradiction
                )
      contradiction
    · rename_i rule'
      have imp : (imod.product smod).inputs.getIO ident = liftR rule' := by
        dsimp [Module.product, PortMap.getIO]
        rewrite [AssocList.append_find_right, AssocList.find?_mapVal, h2]; rfl
        rewrite [AssocList.find?_mapVal, h1]; rfl
      have spec : (smod.product imod).inputs.getIO ident = liftL rule' := by
        dsimp [Module.product, PortMap.getIO]
        rewrite [AssocList.append_find_left]; rfl
        rewrite [AssocList.find?_mapVal, h2]; rfl
      rewrite [PortMap.rw_rule_execution (by rw [spec])]
      rewrite [PortMap.rw_rule_execution (by rw [imp])] at rule
      dsimp [liftR, liftL] at *
      obtain ⟨rule, r3⟩ := rule; subst_vars
      constructor <;> try rfl
      convert rule; simp
  · rename_i rule'
    have hsmod := AssocList.disjoint_keys_find_some h.1 h1
    have imp : (imod.product smod).inputs.getIO ident = liftL rule' := by
      dsimp [Module.product, PortMap.getIO]
      rewrite [AssocList.append_find_left]; rfl
      rewrite [AssocList.find?_mapVal, h1]; rfl
    have spec : (smod.product imod).inputs.getIO ident = liftR rule' := by
      dsimp [Module.product, PortMap.getIO]
      rewrite [AssocList.append_find_right, AssocList.find?_mapVal, h1]; rfl
      rewrite [AssocList.find?_mapVal, hsmod]; rfl
    rewrite [PortMap.rw_rule_execution (by rw [spec])]
    rewrite [PortMap.rw_rule_execution (by rw [imp])] at rule
    dsimp [liftR, liftL] at *
    obtain ⟨rule, r3⟩ := rule; subst_vars
    constructor <;> try rfl
    convert rule; simp

omit mm in
theorem rule_product_commutative_output {i₁ i₂} {mid_i mid_s} {ident} {v} (h : Disjoint imod smod) :
  have _ := MatchInterface_product_commutative h
  ((imod.product smod).outputs.getIO ident).snd (i₁, i₂) v (mid_i, mid_s) →
  ((smod.product imod).outputs.getIO ident).snd (i₂, i₁) ((MatchInterface.output_types ident).mp v) (mid_s, mid_i) := by
  intro _ rule
  cases h1 : imod.outputs.find? ident
  · cases h2 : smod.outputs.find? ident
    · have := PortMap.getIO_not_contained_false rule
                (by
                  intro hcont
                  dsimp [Module.product] at hcont
                  simp only [AssocList.contains_append, AssocList.contains_mapval] at hcont
                  rw [AssocList.contains_find?_none_iff] at h1 h2
                  rw [h1, h2] at hcont
                  contradiction
                )
      contradiction
    · rename_i rule'
      have imp : (imod.product smod).outputs.getIO ident = liftR rule' := by
        dsimp [Module.product, PortMap.getIO]
        rewrite [AssocList.append_find_right, AssocList.find?_mapVal, h2]; rfl
        rewrite [AssocList.find?_mapVal, h1]; rfl
      have spec : (smod.product imod).outputs.getIO ident = liftL rule' := by
        dsimp [Module.product, PortMap.getIO]
        rewrite [AssocList.append_find_left]; rfl
        rewrite [AssocList.find?_mapVal, h2]; rfl
      rewrite [PortMap.rw_rule_execution (by rw [spec])]
      rewrite [PortMap.rw_rule_execution (by rw [imp])] at rule
      dsimp [liftR, liftL] at *
      obtain ⟨rule, r3⟩ := rule; subst_vars
      constructor <;> try rfl
      convert rule; simp
  · rename_i rule'
    have hsmod := AssocList.disjoint_keys_find_some h.2 h1
    have imp : (imod.product smod).outputs.getIO ident = liftL rule' := by
      dsimp [Module.product, PortMap.getIO]
      rewrite [AssocList.append_find_left]; rfl
      rewrite [AssocList.find?_mapVal, h1]; rfl
    have spec : (smod.product imod).outputs.getIO ident = liftR rule' := by
      dsimp [Module.product, PortMap.getIO]
      rewrite [AssocList.append_find_right, AssocList.find?_mapVal, h1]; rfl
      rewrite [AssocList.find?_mapVal, hsmod]; rfl
    rewrite [PortMap.rw_rule_execution (by rw [spec])]
    rewrite [PortMap.rw_rule_execution (by rw [imp])] at rule
    dsimp [liftR, liftL] at *
    obtain ⟨rule, r3⟩ := rule; subst_vars
    constructor <;> try rfl
    convert rule; simp

def refines_φ (φ : I → S → Prop) :=
  ∀ (init_i : I) (init_s : S),
    φ init_i init_s →
     comp_refines imod smod φ init_i init_s

def refines'_φ (φ : I → S → Prop) :=
  ∀ (init_i : I) (init_s : S),
    φ init_i init_s →
     comp_refines' imod smod φ init_i init_s

notation:40 x " ⊑_{" φ "} " y:40 => refines_φ x y φ
notation:40 x " ⊑'_{" φ "} " y:40 => refines'_φ x y φ

theorem refines_φ_reflexive : imod ⊑_{Eq} imod := by
  intro init_i init_s heq; subst_vars
  constructor
  · intro ident mid_i v hrule
    refine ⟨ mid_i, mid_i, hrule, existSR.done _, rfl ⟩
  · intro ident mid_i v hrule
    refine ⟨ init_s, mid_i, existSR.done _, hrule, rfl ⟩
  · intro ident mid_i hcont hrule
    refine ⟨ mid_i, ?_, rfl ⟩
    constructor <;> try assumption
    exact .done _

theorem refines_φ_reflexive_ext imod' (h : imod.EqExt imod') (mm := MatchInterface_EqExt h) :
    imod ⊑_{Eq} imod' := by
  intro init_i init_s heq; subst_vars
  let ⟨Hl, Hr, Hint, Hinit⟩ := h; clear h
  constructor
  · intro ident mid_i v hrule
    rw [PortMap.rw_rule_execution (PortMap.EqExt_getIO Hl ident)] at *
    refine ⟨ mid_i, mid_i, hrule, existSR.done _, rfl ⟩
  · intro ident mid_i v hrule
    rw [PortMap.rw_rule_execution (PortMap.EqExt_getIO Hr ident)] at *
    refine ⟨ init_s, mid_i, existSR.done _, hrule, rfl ⟩
  · intro ident mid_i hcont hrule
    have : ident ∈ imod'.internals := by
      simp_all only [List.Perm.mem_iff Hint]
    refine ⟨mid_i, ?_, rfl⟩
    constructor <;> try assumption
    exact .done _

theorem refines_φ_multistep :
    ∀ φ, imod ⊑_{φ} smod →
    ∀ i_init s_init,
      φ i_init s_init →
      ∀ i_mid, existSR imod.internals i_init i_mid →
      ∃ s_mid,
        existSR smod.internals s_init s_mid
        ∧ φ i_mid s_mid := by
  intros φ Href i_init s_init Hphi i_mid Hexist
  induction Hexist generalizing s_init
  · exists s_init; and_intros; constructor; assumption
  · rename I → I → Prop => rule
    rename ∀ _, _ => iH
    unfold refines_φ at Href
    rcases Href _ _ Hphi with ⟨ Hinp, Hout, Hint ⟩
    rcases Hint _ _ ‹_› ‹_› with ⟨ s_mid, Hexist, Hphi' ⟩
    rcases iH _ Hphi' with ⟨ s_mid', Hexists, Hphi ⟩
    exists s_mid'
    all_goals solve_by_elim [existSR_transitive]

theorem existsSR_mid {φ} (H : imod ⊑_{φ} smod) init_i init_s:
    φ init_i init_s →
    ∀ mid_i,
      existSR imod.internals init_i mid_i →
      ∃ mid_s, existSR smod.internals init_s mid_s ∧ φ mid_i mid_s := by
  intros Hφ mid_i Hsteps
  induction Hsteps generalizing init_s
  · exists init_s
    and_intros
    · constructor
    · assumption
  · rename_i init mid final rule HruleIn Hrule H1 H2
    obtain ⟨ _, _, hint ⟩ := H _ _ Hφ
    specialize hint rule _ HruleIn Hrule
    obtain ⟨ mid_s, Hmid_s1, Hmid_s2 ⟩ := hint
    obtain ⟨ mid_s', Hmid_s'1, Hmid_s'2 ⟩ := H2 mid_s Hmid_s2
    exists mid_s'
    and_intros <;> try simpa
    apply existSR_transitive _ _ _ _ Hmid_s1 Hmid_s'1

theorem refines_φ_transitive {J} (smod' : Module Ident J) {φ₁ φ₂}
  [MatchInterface imod smod']
  [MatchInterface smod' smod]:
    imod ⊑_{φ₁} smod' →
    smod' ⊑_{φ₂} smod →
    imod ⊑_{λ a b => ∃ c, φ₁ a c ∧ φ₂ c b} smod := by
  intros h1 h2
  intro init_i init_s ⟨ init_j, Hφ₁, Hφ₂ ⟩
  obtain ⟨ h1inp, h1out, h1int ⟩ := h1 _ _ Hφ₁
  obtain ⟨ h2inp, h2out, h2int ⟩ := h2 _ _ Hφ₂
  constructor
  · clear h1out h2out h1int h2int
    intro ident mid_i v Hrule
    specialize h1inp _ _ _ Hrule
    obtain ⟨ mid_mid_j, mid_j, hrule₁, hexists₁, hphi₁ ⟩ := h1inp
    obtain Htmp := existsSR_mid _ _ h2 init_j init_s
    specialize h2inp _ _ _ hrule₁
    obtain ⟨ mid_mid_s, mid_s, hrule₂, hexists₂, hphi₂ ⟩ := h2inp
    obtain ⟨ mid_s₃, hexists₃, hphi₃ ⟩ := refines_φ_multistep _ _ _ h2 _ _ hphi₂ _ hexists₁
    refine ⟨ ?_, mid_s₃, ?inp.and1, ?inp.and2, mid_j, ?_, ?_ ⟩
    case and1 => convert hrule₂; simp
    case and2 => solve_by_elim [existSR_transitive]
    all_goals assumption
  · clear h1inp h2inp h1int h2int h2out
    intro ident mid_i v Hrule
    specialize h1out _ _ _ Hrule
    obtain ⟨ mid_mid_j, mid_j, hexists₁, hrule₁, hphi₁ ⟩ := h1out
    obtain ⟨ almost_mid_s, Halmost1, Halmost2 ⟩ := existsSR_mid _ _ h2 init_j init_s Hφ₂ _ hexists₁
    obtain ⟨ h2inp, h2out, h2int ⟩ := h2 _ _ Halmost2
    specialize h2out _ _ _ hrule₁
    obtain ⟨ mid_mid_s, mid_s, hexists₂, hrule₂, hphi₂ ⟩ := h2out
    apply Exists.intro mid_mid_s
    apply Exists.intro mid_s
    and_intros
    · apply existSR_transitive _ _ _ _ Halmost1 hexists₂
    · simp at hrule₂; simpa
    · exists mid_j
  · clear h1inp h1out h2inp h2out
    intro rule mid_i ruleIn Hrule
    specialize h1int rule mid_i ruleIn Hrule
    rcases h1int with ⟨ mid_j, hexist₁, hphi₁ ⟩
    have Href := refines_φ_multistep _ _ _ h2 _ _ Hφ₂ _ hexist₁
    rcases Href with ⟨ mid_s, hexist₂, hphi₂ ⟩
    refine ⟨ mid_s, hexist₂, ?_, by exact hphi₁, by exact hphi₂ ⟩

end Refinementφ

section Refinement

variable {I : Type _}
variable {S : Type _}
variable {Ident : Type _}
variable [DecidableEq Ident]

variable (imod : Module Ident I)
variable (smod : Module Ident S)

def refines_initial [mm : MatchInterface imod smod] (φ : I → S → Prop) :=
  ∀ i, imod.init_state i → ∃ s, smod.init_state s ∧ φ i s

theorem refines_initial_reflexive_ext
  imod' (h : imod.EqExt imod') (mm := MatchInterface_EqExt h) φ (Hφ : ∀ i, φ i i):
    refines_initial imod imod' φ := by
  intros i Hi; exists i
  obtain ⟨_, _, _, h⟩ := h
  and_intros <;> simpa [←h, Hφ]

def refines :=
  ∃ (mm : MatchInterface imod smod) (φ : I → S → Prop),
    (imod ⊑_{φ} smod) ∧ refines_initial imod smod (fun x y => φ x y)

notation:40 x " ⊒ " y:40 => refines y x
notation:40 x " ⊑ " y:40 => refines x y

def equivalent :=
    imod ⊑ smod
  ∧ imod ⊒ smod

notation:40 x " ≡ " y:40 => equivalent x y

variable {imod smod}

theorem refines_reflexive : imod ⊑ imod := by
  exists inferInstance, Eq; intros; subst_vars
  and_intros; simpa [refines_φ_reflexive]
  unfold refines_initial; intro i imod; exists i

theorem refines_reflexive_ext imod' (h : imod.EqExt imod') : imod ⊑ imod' := by
  have _ := MatchInterface_EqExt h
  exists inferInstance, Eq; intros; subst_vars; and_intros
  all_goals solve_by_elim [refines_φ_reflexive_ext, refines_initial_reflexive_ext]

theorem refines_transitive {J} (imod' : Module Ident J):
    imod ⊑ imod' →
    imod' ⊑ smod →
    imod ⊑ smod := by
  intro h1 h2
  rcases h1 with ⟨ mm1, R1, h11, h12 ⟩
  rcases h2 with ⟨ mm2, R2, h21, h22 ⟩
  have mm3 := MatchInterface_transitive imod' mm1 mm2
  constructor <;> try assumption
  exists (fun a b => ∃ c, R1 a c ∧ R2 c b); dsimp
  and_intros
  · apply refines_φ_transitive imod smod imod'
    assumption; assumption
  · intros _ Hi; dsimp;
    obtain ⟨i', Hi', _⟩ := h12 _ Hi
    obtain ⟨s, _, _⟩ := h22 _ Hi'
    exists s
    and_intros <;> try assumption
    exists i'

theorem liftL'_rule_eq {A B} {rule' init_i init_i₂ mid_i₁ mid_i₂}:
  @liftL' A B rule' (init_i, init_i₂) (mid_i₁, mid_i₂) →
  rule' init_i mid_i₁ ∧ init_i₂ = mid_i₂ := by simp [liftL']

theorem liftR'_rule_eq {A B} {rule' init_i init_i₂ mid_i₁ mid_i₂}:
  @liftR' A B rule' (init_i, init_i₂) (mid_i₁, mid_i₂) →
  rule' init_i₂ mid_i₂ ∧ init_i = mid_i₁ := by simp [liftR']

theorem existSR_product_l {A B} {rulel ruler} {l₁ l₂ r} (H: existSR rulel l₁ l₂) :
  existSR (List.map (@liftL' A B) rulel ++ ruler) (l₁, r) (l₂, r) := by
  induction H with
  | done => constructor
  | step l₁₁ l₁₂ l₁₃ rule Hcontains Hrule H6 H7 =>
    apply existSR_transitive _ _ _ _ _ H7
    apply existSR.step _ (l₁₂, r) _ (liftL' rule)
    · simp only [List.mem_append, List.mem_map]; left; exists rule
    · simpa [liftL']
    · constructor

theorem existSR_product_r {A B} {rulel ruler} {l r₁ r₂} (H: existSR ruler r₁ r₂) :
  existSR (rulel ++ List.map (@liftR' A B) ruler) (l, r₁) (l, r₂) := by
  induction H with
  | done => constructor
  | step r₁₁ r₁₂ r₁₃ rule Hcontains Hrule H6 H7 =>
    apply existSR_transitive _ _ _ _ _ H7
    apply existSR.step _ (l, r₁₂) _ (liftR' rule)
    · simp only [List.mem_append, List.mem_map]; right; exists rule
    · simpa [liftR']
    · constructor

theorem refines_φ_product {J K} {imod₂ : Module Ident J} {smod₂ : Module Ident K}
  [MatchInterface imod smod]
  [MatchInterface imod₂ smod₂] {φ₁ φ₂} :
    imod ⊑_{φ₁} smod →
    imod₂ ⊑_{φ₂} smod₂ →
    imod.product imod₂ ⊑_{λ a b => φ₁ a.1 b.1 ∧ φ₂ a.2 b.2} smod.product smod₂ := by
  intro href₁ href₂
  have mm_prod : MatchInterface (imod.product imod₂) (smod.product smod₂) := inferInstance
  unfold refines_φ at *
  intro ⟨init_i, init_i₂⟩ ⟨init_s,init_s₂⟩ hφ
  specialize href₁ init_i init_s hφ.left
  specialize href₂ init_i₂ init_s₂ hφ.right
  constructor
  · intro ident ⟨mid_i, mid_i₂⟩ hgetio hrule
    have hcontains := PortMap.rule_contains hrule
    rcases Option.isSome_iff_exists.mp (AssocList.contains_some hcontains) with ⟨rule, hruleIn⟩
    rcases AssocList.append_find?2 hruleIn with hruleIn' | hruleIn'
    case inl =>
      rw [AssocList.find?_mapVal] at hruleIn'
      cases h : AssocList.find? ident imod.inputs; rw [h] at hruleIn'; injection hruleIn'
      rename_i rule'; rw [h] at hruleIn'; simp at hruleIn'; subst_vars
      have cast2 : ((imod.product imod₂).inputs.getIO ident).fst = (imod.inputs.getIO ident).fst := by
        dsimp [PortMap.getIO]; rw [hruleIn,h,liftL]; rfl
      have cast_rule : (imod.product imod₂).inputs.getIO ident = liftL (imod.inputs.getIO ident) := by
        dsimp [PortMap.getIO]; rw [hruleIn,h]; rfl
      rw [PortMap.rw_rule_execution cast_rule] at hrule
      dsimp [liftL] at hrule; rcases hrule with ⟨hrule⟩; subst_vars
      rcases href₁ with ⟨href_in, -, -⟩
      have hcontains₂ : AssocList.contains ident imod.inputs := by
        apply AssocList.contains_some2; rw [h]; rfl
      have hrule₂ : (imod.inputs.getIO ident).snd init_i (cast2.mp hgetio) mid_i := by
        have : imod.inputs.getIO ident = rule' := by
          dsimp [PortMap.getIO]; rw [h]; rfl
        rw [PortMap.rw_rule_execution this]
        simp; convert hrule; exact this.symm
        simp [cast]
      specialize href_in ident mid_i (cast2.mp hgetio) hrule₂
      rcases href_in with ⟨almost_mid_s, mid_s, hrule₃, hexists, hφ₃⟩
      refine ⟨ (almost_mid_s, ‹_›), (mid_s, ‹_›), ?_, ?_, ?_, ?_ ⟩
      · have : ∃ y, smod.inputs.find? ident = some y := by
          have := ‹MatchInterface imod smod›.inputs_present ident
          rw [h] at this
          simp [-AssocList.find?_eq] at this
          exact Option.isSome_iff_exists.mp this
        rcases this with ⟨Srule, HSrule⟩
        have : (AssocList.mapVal (fun x => liftL) smod.inputs).find? ident = some (@liftL _ K Srule) := by
          rw [←AssocList.find?_map_comm]; rw [HSrule]; rfl
        have s : (smod.product smod₂).inputs.getIO ident = liftL (smod.inputs.getIO ident) := by
          skip; dsimp [Module.product, PortMap.getIO]; rw [AssocList.append_find_left this]
          rw [HSrule]; rfl
        rw [PortMap.rw_rule_execution s]
        dsimp [liftL]; refine ⟨?_, rfl⟩; convert hrule₃; simp
      · solve_by_elim [existSR_append_left, existSR_liftL']
      · assumption
      · apply hφ.right
    case inr =>
      rcases hruleIn' with ⟨hruleIn'none, hruleIn'⟩
      rw [AssocList.find?_mapVal] at hruleIn'
      cases h : AssocList.find? ident imod₂.inputs; rw [h] at hruleIn'; injection hruleIn'
      rename_i rule'; rw [h] at hruleIn'; simp at hruleIn'; subst_vars
      have cast2 : ((imod.product imod₂).inputs.getIO ident).fst = (imod₂.inputs.getIO ident).fst := by
        dsimp [PortMap.getIO]; rw [hruleIn,h,liftR]; rfl
      have cast_rule : (imod.product imod₂).inputs.getIO ident = liftR (imod₂.inputs.getIO ident) := by
        dsimp [PortMap.getIO]; rw [hruleIn,h]; rfl
      rw [PortMap.rw_rule_execution cast_rule] at hrule
      dsimp [liftL] at hrule; rcases hrule with ⟨hrule⟩; subst_vars
      rcases href₂ with ⟨href_in, -, -⟩
      have hcontains₂ : AssocList.contains ident imod₂.inputs := by
        apply AssocList.contains_some2; rw [h]; rfl
      have hrule₂ : (imod₂.inputs.getIO ident).snd init_i₂ (cast2.mp hgetio) mid_i₂ := by
        have : imod₂.inputs.getIO ident = rule' := by
          dsimp [PortMap.getIO]; rw [h]; rfl
        rw [PortMap.rw_rule_execution this]
        simp; convert hrule; exact this.symm
        simp [cast]
      specialize href_in ident mid_i₂ (cast2.mp hgetio) hrule₂
      rcases href_in with ⟨almost_mid_s, mid_s, hrule₃, hexists, hφ₃⟩
      refine ⟨ (‹_›, almost_mid_s), (‹_›, mid_s), ?_, ?_, ?_, ?_ ⟩
      · have : ∃ y, smod₂.inputs.find? ident = some y := by
          have := ‹MatchInterface imod₂ smod₂›.inputs_present ident
          rw [h] at this
          simp [-AssocList.find?_eq] at this
          exact Option.isSome_iff_exists.mp this
        rcases this with ⟨Srule, HSrule⟩
        have : smod.inputs.find? ident = none := by
          have := ‹MatchInterface imod smod›.inputs_present ident
          rw [AssocList.find?_mapVal] at hruleIn'none
          cases h : AssocList.find? ident imod.inputs; rw [h] at hruleIn'none
          rw [h] at this; simp [-AssocList.find?_eq] at this; assumption
          rw [h] at this; rw [h] at hruleIn'none; injection hruleIn'none
        have hrule_another : (AssocList.mapVal (fun x => @liftL S K) smod.inputs).find? ident = none := by
          rw [←AssocList.find?_map_comm]; simp only [*]; rfl
        have : (AssocList.mapVal (fun x => liftR) smod₂.inputs).find? ident = some (@liftR S _ Srule) := by
          rw [←AssocList.find?_map_comm]; rw [HSrule]; rfl
        have s : (smod.product smod₂).inputs.getIO ident = liftR (smod₂.inputs.getIO ident) := by
          skip; dsimp [Module.product, PortMap.getIO];
          rw [AssocList.append_find_right, this]
          · rw [HSrule]; rfl
          · rw [hrule_another]
        rw [PortMap.rw_rule_execution s]
        dsimp [liftL]; refine ⟨?_, rfl⟩; convert hrule₃; simp
      · solve_by_elim [existSR_append_right, existSR_liftR']
      · apply hφ.left
      · assumption
  · intro ident ⟨mid_i, mid_i₂⟩ hgetio hrule
    have hcontains := PortMap.rule_contains hrule
    rcases Option.isSome_iff_exists.mp (AssocList.contains_some hcontains) with ⟨rule, hruleIn⟩
    rcases AssocList.append_find?2 hruleIn with hruleIn' | hruleIn'
    case inl =>
      rw [AssocList.find?_mapVal] at hruleIn'
      cases h : AssocList.find? ident imod.outputs; rw [h] at hruleIn'; injection hruleIn'
      rename_i rule'; rw [h] at hruleIn'; simp at hruleIn'; subst_vars
      have cast2 : ((imod.product imod₂).outputs.getIO ident).fst = (imod.outputs.getIO ident).fst := by
        dsimp [PortMap.getIO]; rw [hruleIn,h,liftL]; rfl
      have cast_rule : (imod.product imod₂).outputs.getIO ident = liftL (imod.outputs.getIO ident) := by
        dsimp [PortMap.getIO]; rw [hruleIn,h]; rfl
      rw [PortMap.rw_rule_execution cast_rule] at hrule
      dsimp [liftL] at hrule; rcases hrule with ⟨hrule⟩; subst_vars
      rcases href₁ with ⟨-, href_out, -⟩
      have hcontains₂ : AssocList.contains ident imod.outputs := by
        apply AssocList.contains_some2; rw [h]; rfl
      have hrule₂ : (imod.outputs.getIO ident).snd init_i (cast2.mp hgetio) mid_i := by
        have : imod.outputs.getIO ident = rule' := by
          dsimp [PortMap.getIO]; rw [h]; rfl
        rw [PortMap.rw_rule_execution this]
        simp; convert hrule; exact this.symm
        simp [cast]
      specialize href_out ident mid_i (cast2.mp hgetio) hrule₂
      rcases href_out with ⟨almost_mid_s, mid_s, hstep, hrule₃, hφ₃⟩
      refine ⟨ (almost_mid_s, ‹_›), (mid_s, ‹_›), ?_, ?_, ?_, ?_ ⟩
      · dsimp [Module.product]
        apply existSR_product_l hstep
      · have : ∃ y, smod.outputs.find? ident = some y := by
          have := ‹MatchInterface imod smod›.outputs_present ident
          rw [h] at this
          simp [-AssocList.find?_eq] at this
          exact Option.isSome_iff_exists.mp this
        rcases this with ⟨Srule, HSrule⟩
        have : (AssocList.mapVal (fun x => liftL) smod.outputs).find? ident = some (@liftL _ K Srule) := by
          rw [←AssocList.find?_map_comm]; rw [HSrule]; rfl
        have s : (smod.product smod₂).outputs.getIO ident = liftL (smod.outputs.getIO ident) := by
          skip; dsimp [Module.product, PortMap.getIO]; rw [AssocList.append_find_left this]
          rw [HSrule]; rfl
        rw [PortMap.rw_rule_execution s]
        dsimp [liftL]; refine ⟨?_, rfl⟩; convert hrule₃; simp
      · assumption
      · apply hφ.right
    case inr =>
      rcases hruleIn' with ⟨hruleIn'none, hruleIn'⟩
      rw [AssocList.find?_mapVal] at hruleIn'
      cases h : AssocList.find? ident imod₂.outputs; rw [h] at hruleIn'; injection hruleIn'
      rename_i rule'; rw [h] at hruleIn'; simp at hruleIn'; subst_vars
      have cast2 : ((imod.product imod₂).outputs.getIO ident).fst = (imod₂.outputs.getIO ident).fst := by
        dsimp [PortMap.getIO]; rw [hruleIn,h,liftR]; rfl
      have cast_rule : (imod.product imod₂).outputs.getIO ident = liftR (imod₂.outputs.getIO ident) := by
        dsimp [PortMap.getIO]; rw [hruleIn,h]; rfl
      rw [PortMap.rw_rule_execution cast_rule] at hrule
      dsimp [liftL] at hrule; rcases hrule with ⟨hrule⟩; subst_vars
      rcases href₂ with ⟨-, href_out, -⟩
      have hcontains₂ : AssocList.contains ident imod₂.outputs := by
        apply AssocList.contains_some2; rw [h]; rfl
      have hrule₂ : (imod₂.outputs.getIO ident).snd init_i₂ (cast2.mp hgetio) mid_i₂ := by
        have : imod₂.outputs.getIO ident = rule' := by
          dsimp [PortMap.getIO]; rw [h]; rfl
        rw [PortMap.rw_rule_execution this]
        simp; convert hrule; exact this.symm
        simp [cast]
      specialize href_out ident mid_i₂ (cast2.mp hgetio) hrule₂
      rcases href_out with ⟨almost_mid_s, mid_s, hstep, hrule₃, hφ₃⟩
      refine ⟨ (‹_›, almost_mid_s), (‹_›, mid_s), ?_, ?_, ?_, ?_ ⟩
      · dsimp [Module.product]
        apply existSR_product_r hstep
      · have : ∃ y, smod₂.outputs.find? ident = some y := by
          have := ‹MatchInterface imod₂ smod₂›.outputs_present ident
          rw [h] at this
          simp [-AssocList.find?_eq] at this
          exact Option.isSome_iff_exists.mp this
        rcases this with ⟨Srule, HSrule⟩
        have : smod.outputs.find? ident = none := by
          have := ‹MatchInterface imod smod›.outputs_present ident
          rw [AssocList.find?_mapVal] at hruleIn'none
          cases h : AssocList.find? ident imod.outputs; rw [h] at hruleIn'none
          rw [h] at this; simp [-AssocList.find?_eq] at this; assumption
          rw [h] at this; rw [h] at hruleIn'none; injection hruleIn'none
        have hrule_another : (AssocList.mapVal (fun x => @liftL S K) smod.outputs).find? ident = none := by
          rw [←AssocList.find?_map_comm]; simp only [*]; rfl
        have : (AssocList.mapVal (fun x => liftR) smod₂.outputs).find? ident = some (@liftR S _ Srule) := by
          rw [←AssocList.find?_map_comm]; rw [HSrule]; rfl
        have s : (smod.product smod₂).outputs.getIO ident = liftR (smod₂.outputs.getIO ident) := by
          skip; dsimp [Module.product, PortMap.getIO];
          rw [AssocList.append_find_right, this]
          · rw [HSrule]; rfl
          · rw [hrule_another]
        rw [PortMap.rw_rule_execution s]
        dsimp [liftL]; refine ⟨?_, rfl⟩; convert hrule₃; simp
      · apply hφ.left
      · assumption
  · intro rule ⟨mid_i₁, mid_i₂⟩ hruleIn hRule
    dsimp [Module.product, PortMap.getIO] at hruleIn
    simp at hruleIn
    rcases hruleIn with ⟨ rule', hruleIn, hruleEq ⟩ | ⟨ rule', hruleIn, hruleEq ⟩ <;> subst_vars
    · rcases href₁ with ⟨-, -, href_int⟩
      obtain ⟨a, b⟩ := liftL'_rule_eq hRule; subst_vars
      specialize href_int _ mid_i₁ hruleIn a
      rcases href_int with ⟨mid_s, Hexists, hphi⟩
      apply Exists.intro (_, _); and_intros
      · dsimp [Module.product]; solve_by_elim [existSR_append_left, existSR_liftL']
      · assumption
      · apply hφ.right
    · rcases href₂ with ⟨-, -, href_int⟩
      obtain ⟨a, b⟩ := liftR'_rule_eq hRule; subst_vars
      specialize href_int _ mid_i₂ hruleIn a
      rcases href_int with ⟨mid_s, Hexists, hphi⟩
      apply Exists.intro (_, _); and_intros
      · dsimp [Module.product]; solve_by_elim [existSR_append_right, existSR_liftR']
      · apply hφ.left
      · assumption

theorem refines_product {J K} (imod₂ : Module Ident J) (smod₂ : Module Ident K):
    imod ⊑ smod →
    imod₂ ⊑ smod₂ →
    imod.product imod₂ ⊑ smod.product smod₂ := by
  intro href₁ href₂
  rcases href₁ with ⟨_, R, Href, Hinit⟩
  rcases href₂ with ⟨_, R2, Href₂, Hinit₂⟩
  refine ⟨inferInstance, (λ a b => R a.1 b.1 ∧ R2 a.2 b.2), ?_, ?_⟩
  and_intros
  · apply refines_φ_product <;> assumption
  · intro _ ⟨Hi, Hj⟩
    obtain ⟨s1, _, _⟩ := Hinit _ Hi
    obtain ⟨s2, _, _⟩ := Hinit₂ _ Hj
    exists ⟨s1, s2⟩

theorem refines_φ_product_associative {J} (jmod : Module Ident J):
    imod.product (smod.product jmod) ⊑_{fun | (i₁, i₂, i₃), ((s₁, s₂), s₃) => i₁ = s₁ ∧ i₂ = s₂ ∧ i₃ = s₃} (imod.product smod).product jmod := by
  intro (i_init, s_init, j_init) ((i_init', s_init'), j_init') hphi
  dsimp at hphi; repeat1 cases ‹_ ∧ _›; subst_vars
  constructor
  · intro ident (mid_i, mid_s, mid_j) v rule
    refine ⟨((mid_i, mid_s), mid_j), ((mid_i, mid_s), mid_j), ?_, existSR.done _, ⟨rfl, rfl, rfl⟩⟩
    solve_by_elim [rule_product_associative_input]
  · intro ident (mid_i, mid_s, mid_j) v rule
    refine ⟨_, ((mid_i, mid_s), mid_j), existSR.done _, ?_, ⟨rfl, rfl, rfl⟩⟩
    solve_by_elim [rule_product_associative_output]
  · intro r (mid_i, mid_s, mid_j) hrule rule
    exists ((mid_i, mid_s), mid_j)
    and_intros <;> try rfl
    dsimp [Module.product] at hrule ⊢; simp at hrule ⊢
    rcases hrule with ⟨rule', hrule, heq⟩ | ⟨rule', hrule, heq⟩ | ⟨rule', hrule, heq⟩ <;> subst_vars
    · apply existSR.step (mid := ((mid_i, mid_s), mid_j)) (rule := liftL' (liftL' rule'))
      · simp only [List.mem_append, List.mem_map]; grind
      · dsimp [liftL', liftR'] at *; cases rule.2; simp [*]
      · apply existSR.done
    · apply existSR.step (mid := ((mid_i, mid_s), mid_j)) (rule := liftL' (liftR' rule'))
      · simp only [List.mem_append, List.mem_map]; grind
      · dsimp [liftL', liftR'] at *; simp [*]
      · apply existSR.done
    · apply existSR.step (mid := ((mid_i, mid_s), mid_j)) (rule := liftR' rule')
      · simp only [List.mem_append, List.mem_map]; grind
      · dsimp [liftL', liftR'] at *; cases rule.2; simp [*]
      · apply existSR.done

theorem refines_φ_product_associative' {J} (jmod : Module Ident J):
    (imod.product smod).product jmod ⊑_{fun | ((i₁, i₂), i₃), (s₁, s₂, s₃) => i₁ = s₁ ∧ i₂ = s₂ ∧ i₃ = s₃} imod.product (smod.product jmod) := by
  intro ((i_init, s_init), j_init) (i_init', s_init', j_init') hphi
  dsimp at hphi; repeat1 cases ‹_ ∧ _›; subst_vars
  constructor
  · intro ident ((mid_i, mid_s), mid_j) v rule
    refine ⟨(mid_i, mid_s, mid_j), (mid_i, mid_s, mid_j), ?_, existSR.done _, ⟨rfl, rfl, rfl⟩⟩
    solve_by_elim [rule_product_associative'_input]
  · intro ident ((mid_i, mid_s), mid_j) v rule
    refine ⟨_, (mid_i, mid_s, mid_j), existSR.done _, ?_, ⟨rfl, rfl, rfl⟩⟩
    solve_by_elim [rule_product_associative'_output]
  · intro r ((mid_i, mid_s), mid_j) hrule rule
    exists (mid_i, mid_s, mid_j)
    and_intros <;> try rfl
    dsimp [Module.product] at hrule ⊢; simp at hrule ⊢
    rcases hrule with ⟨rule', hrule, heq⟩ | ⟨rule', hrule, heq⟩ | ⟨rule', hrule, heq⟩ <;> subst_vars
    · apply existSR.step (mid := (mid_i, mid_s, mid_j)) (rule := liftL' rule')
      · simp only [List.mem_append, List.mem_map]; grind
      · dsimp [liftL', liftR'] at *; cases rule.2; simp [*]
      · apply existSR.done
    · apply existSR.step (mid := (mid_i, mid_s, mid_j)) (rule := liftR' (liftL' rule'))
      · simp only [List.mem_append, List.mem_map]; grind
      · dsimp [liftL', liftR'] at *; simp [*]
      · apply existSR.done
    · apply existSR.step (mid := (mid_i, mid_s, mid_j)) (rule := liftR' (liftR' rule'))
      · simp only [List.mem_append, List.mem_map]; grind
      · dsimp [liftL', liftR'] at *; cases rule.2; simp [*]
      · apply existSR.done

theorem refines_product_associative {J} {jmod : Module Ident J} :
  imod.product (smod.product jmod) ⊑ (imod.product smod).product jmod := by
  refine ⟨inferInstance, fun | (i₁, i₂, i₃), ((s₁, s₂), s₃) => i₁ = s₁ ∧ i₂ = s₂ ∧ i₃ = s₃, refines_φ_product_associative _, ?_⟩
  dsimp [refines_initial]; intro (i_init, s_init, j_init) hprod
  unfold Module.product at *; dsimp at *; simp [*]

theorem refines_product_associative' {J} {jmod : Module Ident J} :
  (imod.product smod).product jmod ⊑ imod.product (smod.product jmod) := by
  refine ⟨inferInstance, fun | ((i₁, i₂), i₃), (s₁, s₂, s₃) => i₁ = s₁ ∧ i₂ = s₂ ∧ i₃ = s₃, refines_φ_product_associative' _, ?_⟩
  dsimp [refines_initial]; intro ((i_init, s_init), j_init) hprod
  unfold Module.product at *; dsimp at *; simp [*]

theorem refines_φ_product_commutative (h : Disjoint imod smod) :
  have _ := MatchInterface_product_commutative h
  (imod.product smod) ⊑_{fun | (i₁, i₂), (s₁, s₂) => i₁ = s₂ ∧ i₂ = s₁} (smod.product imod) := by
  intro _ (i_init, s_init) (i_init', s_init') hphi
  dsimp at hphi; repeat1 cases ‹_ ∧ _›; subst_vars
  constructor
  · intro ident (mid_i, mid_s) v rule
    refine ⟨(mid_s, mid_i), (mid_s, mid_i), ?_, existSR.done _, ⟨rfl, rfl⟩⟩
    solve_by_elim [rule_product_commutative_input]
  · intro ident (mid_i, mid_s) v rule
    refine ⟨_, (mid_s, mid_i), existSR.done _, ?_, ⟨rfl, rfl⟩⟩
    solve_by_elim [rule_product_commutative_output]
  · intro r (mid_i, mid_s) hrule rule
    exists (mid_s, mid_i)
    and_intros <;> try rfl
    dsimp [Module.product] at hrule ⊢; simp at hrule ⊢
    rcases hrule with ⟨rule', hrule, heq⟩ | ⟨rule', hrule, heq⟩ <;> subst_vars
    · apply existSR.step (mid := (mid_s, mid_i)) (rule := liftR' rule')
      · simp only [List.mem_append, List.mem_map]; grind
      · dsimp [liftL', liftR'] at *; cases rule.2; simp [*]
      · apply existSR.done
    · apply existSR.step (mid := (mid_s, mid_i)) (rule := liftL' rule')
      · simp only [List.mem_append, List.mem_map]; grind
      · dsimp [liftL', liftR'] at *; simp [*]
      · apply existSR.done

theorem refines_product_commutative (h : Disjoint imod smod) :
  (imod.product smod) ⊑ smod.product imod := by
  refine ⟨MatchInterface_product_commutative h, fun | (i₁, i₂), (s₁, s₂) => i₁ = s₂ ∧ i₂ = s₁, refines_φ_product_commutative h, ?_⟩
  dsimp [refines_initial]; intro (i_init, s_init) hprod
  unfold Module.product at *; dsimp at *; simp [*]

theorem refines_φ_connect [MatchInterface imod smod] {φ i o} :
    imod ⊑_{φ} smod → imod.connect' o i ⊑_{φ} smod.connect' o i := by
  intro href
  unfold refines_φ at *
  intro init_i init_s hphi
  constructor
  · specialize href _ _ hphi
    rcases href with ⟨href_in, -, -⟩
    intro ident mid_i v hrule
    have hcont := PortMap.rule_contains hrule
    rcases Option.isSome_iff_exists.mp (AssocList.contains_some hcont) with ⟨rule, hruleIn⟩
    dsimp [Module.connect'] at hcont hruleIn; have hcont' := AssocList.contains_eraseAll hcont
    have getIO_eq : (imod.connect' o i).inputs.getIO ident = imod.inputs.getIO ident := by
      dsimp [Module.connect', PortMap.getIO]; rw [hruleIn, AssocList.find?_eraseAll hruleIn]
    specialize href_in ident mid_i ((PortMap.cast_first getIO_eq).mp v) ((PortMap.rw_rule_execution getIO_eq).mp hrule)
    rcases href_in with ⟨a_mid_s, mid_s, hrule_s, hexists, hphi'⟩
    have : AssocList.contains ident ((smod.connect' o i).inputs) := by
      rwa [← match_interface_inputs_contains (imod := imod.connect' o i)]
    have : ((smod.connect' o i).inputs.getIO ident) = (smod.inputs.getIO ident) := by
      dsimp [connect', PortMap.getIO] at *
      simp only [←AssocList.contains_find?_iff] at this
      rcases this with ⟨x, hin⟩
      rw [hin, AssocList.find?_eraseAll hin]
    refine ⟨a_mid_s, mid_s, ?_, ?_, ?_⟩
    · rw [PortMap.rw_rule_execution this]; convert hrule_s; simp
    · apply existSR_cons; assumption
    · assumption
  · specialize href _ _ hphi
    rcases href with ⟨-, href_out, -⟩
    intro ident mid_i v hrule
    have hcont := PortMap.rule_contains hrule
    rcases Option.isSome_iff_exists.mp (AssocList.contains_some hcont) with ⟨rule, hruleIn⟩
    dsimp [Module.connect'] at hcont hruleIn; have hcont' := AssocList.contains_eraseAll hcont
    have getIO_eq : (imod.connect' o i).outputs.getIO ident = imod.outputs.getIO ident := by
      dsimp [Module.connect', PortMap.getIO]; rw [hruleIn, AssocList.find?_eraseAll hruleIn]
    specialize href_out ident mid_i ((PortMap.cast_first getIO_eq).mp v) ((PortMap.rw_rule_execution getIO_eq).mp hrule)
    rcases href_out with ⟨almost_mid_s, mid_s, hstep, hrule_s, hphi'⟩
    have : AssocList.contains ident ((smod.connect' o i).outputs) := by
      rwa [← match_interface_outputs_contains (imod := imod.connect' o i)]
    have : ((smod.connect' o i).outputs.getIO ident) = (smod.outputs.getIO ident) := by
      dsimp [connect', PortMap.getIO] at *
      simp only [←AssocList.contains_find?_iff] at this
      rcases this with ⟨x, hin⟩
      rw [hin, AssocList.find?_eraseAll hin]
    refine ⟨almost_mid_s, mid_s, ?_, ?_, ?_⟩
    · apply existSR_cons; assumption
    · rw [PortMap.rw_rule_execution this]; convert hrule_s; simp
    · assumption
  · intro rule mid_i hrulein hrule
    dsimp [connect', connect''] at hrulein
    cases hrulein
    unfold connect'' at hrule
    rcases Classical.em ((imod.outputs.getIO o).fst = (imod.inputs.getIO i).fst) with HEQ | HEQ
    · rcases hrule with ⟨hrule, _⟩
      rcases hrule HEQ with ⟨cons, outp, hrule1, hrule2⟩
      rcases href init_i init_s ‹_› with ⟨-, hout, -⟩
      specialize hout o cons outp ‹_›
      rcases hout with ⟨almost_mid_s_o, mid_s_o, hstep_o, hrule_s_o, hphi_o⟩
      specialize href _ _ hphi_o
      rcases href with ⟨href_in, -, -⟩
      specialize href_in i mid_i (HEQ.mp outp) ‹_›
      rcases href_in with ⟨alm_mid_s, mid_s_i, instep, exstep, hphi_i⟩
      exists mid_s_i; and_intros <;> try assumption
      apply existSR_transitive;
      · unfold connect'; dsimp;
        apply existSR_transitive;
        · apply existSR_cons; assumption
        · apply existSR.step; constructor; unfold connect''
          and_intros
          · intros _
            constructor; constructor
            and_intros
            exact hrule_s_o
            simp only [eq_mp_eq_cast, cast_cast] at instep
            simp only [eq_mp_eq_cast, cast_cast]
            exact instep
          · intro h; exfalso; apply h;
            rw [← ‹MatchInterface imod smod›.input_types]
            rw [← ‹MatchInterface imod smod›.output_types]
            assumption
          · apply existSR_cons; assumption
      · constructor
    · rcases hrule with ⟨_, hrule⟩
      cases hrule HEQ
    · specialize href _ _ hphi; rcases href with ⟨-, -, href⟩
      specialize href _ _ ‹_› hrule
      rcases href with ⟨mid_s, _, _⟩
      exists mid_s; solve_by_elim [existSR_cons]

theorem refines_connect {o i} :
    imod ⊑ smod →
    imod.connect' o i ⊑ smod.connect' o i := by
  intro href₁
  rcases href₁ with ⟨_, R, Href, Hinit⟩
  unfold refines at *
  refine ⟨inferInstance, R, ?_, ?_⟩
  · intro init_i init_s Hphi
    solve_by_elim [refines_φ_connect]
  · simpa[Hinit]

theorem refines_φ_mapInputPorts {I S} {imod : Module Ident I} {smod : Module Ident S}
  [MatchInterface imod smod] {f φ} {h : Function.Bijective f} :
  have _ := MatchInterface_mapInputPorts (imod := imod) (smod := smod) h
  imod ⊑_{φ} smod →
  imod.mapInputPorts f ⊑_{φ} smod.mapInputPorts f := by
  intro hinj href
  unfold refines_φ at *
  intro init_i init_s hphi
  specialize href _ _ hphi
  constructor
  · rcases href with ⟨hinp, -, -⟩
    intro ident mid_i v hrule
    have := Function.bijective_iff_existsUnique f |>.mp h ident
    rcases this with ⟨ident', mapIdent, uniq⟩
    subst ident
    have : (imod.mapInputPorts f).inputs.getIO (f ident') = imod.inputs.getIO ident' := by
      unfold mapInputPorts PortMap.getIO; dsimp
      rw [AssocList.mapKey_find?]; exact h.injective
    have hrule' := (PortMap.rw_rule_execution this).mp hrule
    specialize hinp ident' mid_i _ hrule'
    rcases hinp with ⟨alm_mid_s, mid_s, hrule_s, hexist, hphi'⟩
    refine ⟨ alm_mid_s, mid_s, ?_, ?_, ‹_› ⟩
    . have : (smod.mapInputPorts f).inputs.getIO (f ident') = smod.inputs.getIO ident' := by
        unfold mapInputPorts PortMap.getIO; dsimp
        rw [AssocList.mapKey_find?]; exact h.injective
      rw [PortMap.rw_rule_execution this]; convert hrule_s; simp
    · assumption
  · apply href.outputs
  · apply href.internals

theorem refines_mapInputPorts {I S} {imod : Module Ident I} {smod : Module Ident S} {f}
  (h : Function.Bijective f) :
  imod ⊑ smod →
  imod.mapInputPorts f ⊑ smod.mapInputPorts f := by
  intro href; rcases href with ⟨_, R, Href, Hinit⟩
  refine ⟨MatchInterface_mapInputPorts (imod := imod) (smod := smod) h, R, ?_, ?_⟩
  · solve_by_elim [refines_φ_mapInputPorts]
  · simpa [Hinit]

theorem refines_φ_mapOutputPorts {I S} {imod : Module Ident I} {smod : Module Ident S}
  [MatchInterface imod smod] {f φ} {h : Function.Bijective f} :
  have _ := MatchInterface_mapOutputPorts (imod := imod) (smod := smod) h
  imod ⊑_{φ} smod →
  imod.mapOutputPorts f ⊑_{φ} smod.mapOutputPorts f := by
  intro hinj href
  unfold refines_φ at *
  intro init_i init_s hphi
  specialize href _ _ hphi
  constructor
  · apply href.inputs
  · rcases href with ⟨-, hout, -⟩
    intro ident mid_i v hrule
    have := Function.bijective_iff_existsUnique f |>.mp h ident
    rcases this with ⟨ident', mapIdent, uniq⟩
    subst ident
    have : (imod.mapOutputPorts f).outputs.getIO (f ident') = imod.outputs.getIO ident' := by
      unfold mapOutputPorts PortMap.getIO; dsimp
      rw [AssocList.mapKey_find?]; exact h.injective
    have hrule' := (PortMap.rw_rule_execution this).mp hrule
    specialize hout ident' mid_i _ hrule'
    rcases hout with ⟨almost_mid_s, mid_s, hstep, hrule_s, hphi'⟩
    refine ⟨ almost_mid_s, mid_s, ?_, ?_, ‹_› ⟩
    · assumption
    . have : (smod.mapOutputPorts f).outputs.getIO (f ident') = smod.outputs.getIO ident' := by
        unfold mapOutputPorts PortMap.getIO; dsimp
        rw [AssocList.mapKey_find?]; exact h.injective
      rw [PortMap.rw_rule_execution this]; convert hrule_s; simp
  · apply href.internals

theorem refines_mapOutputPorts {I S} {imod : Module Ident I} {smod : Module Ident S} {f}
  (h : Function.Bijective f) :
  imod ⊑ smod →
  imod.mapOutputPorts f ⊑ smod.mapOutputPorts f := by
  intro href; rcases href with ⟨_, R, Href, Hinit⟩
  refine ⟨MatchInterface_mapOutputPorts (imod := imod) (smod := smod) h, R, ?_, ?_⟩
  · solve_by_elim [refines_φ_mapOutputPorts]
  · simpa [Hinit]

theorem refines_mapPorts {I S} {imod : Module Ident I} {smod : Module Ident S} {f} (h : Function.Bijective f) :
  imod ⊑ smod →
  imod.mapPorts f ⊑ smod.mapPorts f := by
  intro Href; unfold mapPorts
  solve_by_elim [refines_mapOutputPorts, refines_mapInputPorts]

theorem refines_mapPorts2 {I S} {imod : Module Ident I} {smod : Module Ident S} {f g}
  (h : Function.Bijective f) (h : Function.Bijective g) :
  imod ⊑ smod →
  imod.mapPorts2 f g ⊑ smod.mapPorts2 f g := by
  intro Href; unfold mapPorts2
  solve_by_elim [refines_mapOutputPorts, refines_mapInputPorts]

theorem refines_renamePorts {I S} {imod : Module Ident I} {smod : Module Ident S} {p} :
  imod ⊑ smod →
  imod.renamePorts p ⊑ smod.renamePorts p := by
  intro Href; unfold renamePorts
  solve_by_elim [refines_mapPorts2, AssocList.bijectivePortRenaming_bijective]

theorem refines_eq' {imod : TModule Ident} {smod : TModule Ident} :
  imod = smod → imod.snd ⊑ smod.snd := by
  intro heq; subst imod; apply refines_reflexive

theorem refines_eq {imod : Module Ident I} {smod : Module Ident S} :
  Sigma.mk _ imod = Sigma.mk _ smod → imod ⊑ smod := refines_eq'

theorem refines_eq_relax {I' S'} {imod : Module Ident I} {imod' : Module Ident I'} {smod : Module Ident S} {smod' : Module Ident S'} :
  Sigma.mk _ imod = Sigma.mk _ imod' → Sigma.mk _ smod = Sigma.mk _ smod' → imod' ⊑ smod' → imod ⊑ smod := by
  intro ha hb hc
  apply Module.refines_transitive
  apply refines_eq; assumption
  apply Module.refines_transitive; assumption
  apply refines_eq; apply hb.symm

theorem refines_eq_equiv {imod smod : TModule Ident} :
  imod = smod → imod.snd ≡ smod.snd := by
  intro heq; subst imod; constructor <;> apply refines_reflexive

theorem equivalent_reflexive {I} {imod : Module Ident I} : imod ≡ imod := by
  constructor <;> apply refines_reflexive

end Refinement

variable {Ident}
variable {α : Type _}
variable {β : Type _ → Type _}

@[simp]
abbrev dep_foldr (acc : Σ S, β S) (l : List α) (f : α → Type _ → Type _)
  (g : (i : α) → (acc : Σ S, β S) → β (f i acc.1)) : Σ S, β S :=
  List.foldr (λ i acc => ⟨f i acc.1, g i acc⟩) acc l

theorem dep_foldr_1 {acc} {l} {f : α → Type _ → Type _} {g : (i : α) → (acc : Σ S, β S) → β (f i acc.1)} :
  (dep_foldr acc l f g).1 = List.foldr f acc.1 l := by
    induction l generalizing acc with
    | nil => rfl
    | cons x xs ih => dsimp [dep_foldr]; rw [ih]

theorem dep_foldr_β {acc l} {f : α → Type _ → Type _} {g : (i : α) → (acc : Σ S, β S) → β (f i acc.1)} :
  β (dep_foldr acc l f g).1 = β (List.foldr f acc.1 l) := by
    rw [dep_foldr_1]

@[simp]
abbrev dep_foldl (acc : Σ S, β S) (l : List α) (f : Type _ → α → Type _)
  (g : (acc : Σ S, β S) → (i : α) → β (f acc.1 i)) : Σ S, β S :=
  List.foldl (λ acc i => ⟨f acc.1 i, g acc i⟩) acc l

theorem dep_foldl_1 acc l (f : Type _ → α → Type _) (g : (acc : Σ S, β S) → (i : α) → β (f acc.1 i)) :
  (dep_foldl acc l f g).1 = List.foldl f acc.1 l := by
    induction l generalizing acc with
    | nil => rfl
    | cons x xs ih => dsimp [dep_foldl] at *; rw [ih]

theorem dep_foldl_β {acc l} {f : Type _ → α → Type _} {g : (acc : Σ S, β S) → (i : α) → β (f acc.1 i)} :
  β (dep_foldl acc l f g).1 = β (List.foldl f acc.1 l) := by
    rw [dep_foldl_1]

abbrev acc_int (S : Type _) := List (RelInt S)
abbrev acc_io (S : Type _) := PortMap Ident (RelIO S)
abbrev acc_init (S : Type _) := S → Prop

@[simp] abbrev foldl_int {α} := dep_foldl (α := α) (β := acc_int)
@[simp] abbrev foldl_io {α} := dep_foldl (α := α) (β := @acc_io Ident)
@[simp] abbrev foldl_init {α} := dep_foldl (α := α) (β := acc_init)

theorem foldl_acc_plist_2 (acc : TModule Ident) (l : List α) (f : Type _ → α → Type _)
  (g_inputs : (acc : Σ S, acc_io S) → (i : α) → (acc_io (f acc.1 i)))
  (g_outputs : (acc : Σ S, acc_io S) → (i : α) → (acc_io (f acc.1 i)))
  (g_internals : (acc : Σ S, acc_int S) → (i : α) → (acc_int (f acc.1 i)))
  (g_init_state : (acc : Σ S, acc_init S) → (i : α) → (acc_init (f acc.1 i)))
  :
  (List.foldl (λ acc i =>
    ⟨
      f acc.1 i,
      {
        inputs := g_inputs ⟨acc.1, acc.2.inputs⟩ i
        outputs := g_outputs ⟨acc.1, acc.2.outputs⟩ i
        internals := g_internals ⟨acc.1, acc.2.internals⟩ i
        init_state := g_init_state ⟨acc.1, acc.2.init_state⟩ i
      }
    ⟩) acc l)
  =
    ⟨
      List.foldl f acc.1 l,
      {
        inputs := dep_foldl_β.mp (foldl_io ⟨acc.1, acc.2.inputs⟩ l f g_inputs).2
        outputs := dep_foldl_β.mp (foldl_io ⟨acc.1, acc.2.outputs⟩ l f g_outputs).2
        internals := dep_foldl_β.mp (foldl_int ⟨acc.1, acc.2.internals⟩ l f g_internals).2
        init_state := dep_foldl_β.mp (foldl_init ⟨acc.1, acc.2.init_state⟩ l f g_init_state).2
      }
    ⟩ := by
      induction l generalizing acc with
      | nil => rfl
      | cons hd tl HR => simpa [HR]

@[simp] abbrev foldr_int {α} := dep_foldr (α := α) (β := acc_int)
@[simp] abbrev foldr_io {α} := dep_foldr (α := α) (β := @acc_io Ident)
@[simp] abbrev foldr_init {α} := dep_foldr (α := α) (β := acc_init)

theorem foldr_acc_plist_2 (acc : TModule Ident) (l : List α) (f : α → Type _ → Type _)
  (g_inputs : (i : α) → (acc : Σ S, acc_io S) → (acc_io (f i acc.1)))
  (g_outputs : (i : α) → (acc : Σ S, acc_io S) → (acc_io (f i acc.1)))
  (g_internals : (i : α) → (acc : Σ S, acc_int S) → (acc_int (f i acc.1)))
  (g_init_state : (i : α) → (acc : Σ S, acc_init S) → (acc_init (f i acc.1)))
  :
    dep_foldr acc l f
      (λ i acc =>
        {
          inputs := g_inputs i ⟨acc.1, acc.2.inputs⟩
          outputs := g_outputs i ⟨acc.1, acc.2.outputs⟩
          internals := g_internals i ⟨acc.1, acc.2.internals⟩
          init_state := g_init_state i ⟨acc.1, acc.2.init_state⟩
        }
      )
  =
    ⟨
      List.foldr f acc.1 l,
      {
        -- FIXME: For a foldr, the cast should probably be inside of the fold in
        -- some way, which means that `f` must be casting maybe?
        inputs := dep_foldr_β.mp (foldr_io ⟨acc.1, acc.2.inputs⟩ l f g_inputs).2
        outputs := dep_foldr_β.mp (foldr_io ⟨acc.1, acc.2.outputs⟩ l f g_outputs).2
        internals := dep_foldr_β.mp (foldr_int ⟨acc.1, acc.2.internals⟩ l f g_internals).2
        init_state := dep_foldr_β.mp (foldr_init ⟨acc.1, acc.2.init_state⟩ l f g_init_state).2
      }
    ⟩ := by
      induction l with
      | nil => rfl
      | cons hd tl HR =>
        dsimp at ⊢ HR; rw [HR]; dsimp; congr
        -- FIXME: This is false
        · simp; sorry
        · sorry
        · sorry
        · sorry

variable [DecidableEq Ident]

theorem erase_decide_map {Ident δ S} [DecidableEq Ident] {l : PortMap Ident (RelIO S)} {f : δ → (InternalPort Ident)}
  {hd : δ} {tl : List δ} {hdup : (hd :: tl).Nodup} {hfInj : Function.Injective f} :
  (PortMap.getIO (AssocList.eraseAllP (λ k v => decide (k ∈ List.map f tl)) l) (f hd))
  = PortMap.getIO l (f hd)
  := by
    unfold PortMap.getIO
    rw [AssocList.find?_eraseAllP_false]
    intro _
    simp only [List.mem_map, decide_eq_false_iff_not, not_exists, not_and]
    intro x Hx Heq
    have hEqHd := hfInj Heq
    subst x
    rw [List.nodup_cons] at hdup
    obtain ⟨hdup1, hdup2⟩ := hdup
    contradiction

theorem foldr_connect' (l : List α) (acc : TModule Ident) (f g : α → InternalPort Ident)
  (hfInj : Function.Injective f) (hgInj : Function.Injective g) (Hdup : l.Nodup) :
  List.foldr (λ i acc => ⟨acc.1, acc.snd.connect' (f i) (g i)⟩) acc l
  = ⟨
      acc.1,
      {
        inputs := AssocList.eraseAllP (λ k v => k ∈ List.map g l) acc.2.inputs,
        outputs := AssocList.eraseAllP (λ k v => k ∈ List.map f l) acc.2.outputs,
        internals :=
          List.foldr
            (λ i acc' => connect'' (acc.2.outputs.getIO (f i)).2 (acc.2.inputs.getIO (g i)).2 :: acc')
            acc.2.internals l,
        init_state := acc.2.init_state,
      }
    ⟩ := by
    induction l generalizing acc with
    | nil => simpa
    | cons hd tl HR =>
      dsimp; rw [HR]; dsimp [Module.connect']; congr 2
      · rw [AssocList.eraseAll_eraseAllP]
        simp only [List.mem_cons, Bool.decide_or]
        congr
      · rw [AssocList.eraseAll_eraseAllP]
        simp only [List.mem_cons, Bool.decide_or]
        congr
      · rw [erase_decide_map, erase_decide_map]; repeat assumption
      · simp at Hdup; simpa [Hdup]

@[simp]
theorem renamePorts_inputs {Ident S} [DecidableEq Ident] {m : Module Ident S} {i}:
  (m.renamePorts i).inputs = m.inputs.mapKey i.input.bijectivePortRenaming := rfl

@[simp]
theorem renamePorts_outputs {Ident S} [DecidableEq Ident] {m : Module Ident S} {i}:
  (m.renamePorts i).outputs = m.outputs.mapKey i.output.bijectivePortRenaming := rfl

end Module

end Graphiti
