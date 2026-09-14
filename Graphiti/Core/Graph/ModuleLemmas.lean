/-
Copyright (c) 2024, 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

module

public import Graphiti.Core.Graph.Module
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

private theorem option_map_fst_eq_iff {A B} {a : Option (RelIO A)} {b : Option (RelIO B)} :
    a.map Sigma.fst = b.map Sigma.fst ↔
      a.isSome = b.isSome ∧ (a.getD ⟨PUnit, fun _ _ _ => False⟩).1 = (b.getD ⟨PUnit, fun _ _ _ => False⟩).1 := by
  cases a <;> cases b <;> simp

theorem MatchInterface_simpler {imod : Module Ident I} {smod : Module Ident S} :
  (∀ ident, (imod.inputs.mapVal (λ _ => Sigma.fst)).find? ident = (smod.inputs.mapVal (λ _ => Sigma.fst)).find? ident) →
  (∀ ident, (imod.outputs.mapVal (λ _ => Sigma.fst)).find? ident = (smod.outputs.mapVal (λ _ => Sigma.fst)).find? ident) →
  MatchInterface imod smod := by
  intro h1 h2
  simp only [AssocList.find?_mapVal, option_map_fst_eq_iff] at h1 h2
  refine ⟨fun i => (h1 i).1, fun i => (h2 i).1, fun i => (h1 i).2, fun i => (h2 i).2⟩

theorem MatchInterface_simpler2 {imod : Module Ident I} {smod : Module Ident S} {ident} :
  MatchInterface imod smod →
  (imod.inputs.mapVal (λ _ => Sigma.fst)).find? ident = (smod.inputs.mapVal (λ _ => Sigma.fst)).find? ident
  ∧ (imod.outputs.mapVal (λ _ => Sigma.fst)).find? ident = (smod.outputs.mapVal (λ _ => Sigma.fst)).find? ident := by
  rintro ⟨h1, h2, h3, h4⟩
  simp only [PortMap.getIO] at h3 h4
  simp only [AssocList.find?_mapVal, option_map_fst_eq_iff]
  grind

theorem MatchInterface_simpler_iff {imod : Module Ident I} {smod : Module Ident S} :
  MatchInterface imod smod ↔
  (∀ ident, (imod.inputs.mapVal (λ _ => Sigma.fst)).find? ident = (smod.inputs.mapVal (λ _ => Sigma.fst)).find? ident
  ∧ (imod.outputs.mapVal (λ _ => Sigma.fst)).find? ident = (smod.outputs.mapVal (λ _ => Sigma.fst)).find? ident) := by
  constructor
  · intro h ident; apply MatchInterface_simpler2 h
  · intro ha; apply MatchInterface_simpler (fun i => (ha i).1) (fun i => (ha i).2)

instance : MatchInterface (@Module.empty Ident S) (Module.empty I) :=
  ⟨ fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl ⟩

instance {m : Module Ident S} : MatchInterface m m :=
  ⟨ fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl ⟩

theorem MatchInterface_EqExt {S} {imod imod' : Module Ident S} :
  imod.EqExt imod' → MatchInterface imod imod' := by
  rintro ⟨Hinp, Hout, -, -⟩
  constructor <;> intro i <;> simp only [PortMap.getIO, Hinp i, Hout i]

theorem MatchInterface_transitive {I J S} {imod : Module Ident I} {smod : Module Ident S} (jmod : Module Ident J) :
  MatchInterface imod jmod →
  MatchInterface jmod smod →
  MatchInterface imod smod := by
  intro ⟨i, j, a, b⟩ ⟨k, w, c, d⟩
  constructor <;> intro x <;> simp only [*]

theorem MatchInterface_symmetric {I S} {imod : Module Ident I} (smod : Module Ident S) :
  MatchInterface imod smod →
  MatchInterface smod imod := by
  intro ⟨i, j, a, b⟩
  constructor <;> intro x <;> simp only [*]

-- theorem MatchInterface_Disjoint {I J S K} {imod : Module Ident I} {smod : Module Ident S} {imod' : Module Ident J} {smod' : Module Ident K}
--   [MatchInterface imod smod]
--   [MatchInterface imod' smod'] :
--   Disjoint imod imod' →
--   Disjoint smod smod' := by sorry

instance MatchInterface_connect {I S} {o i} {imod : Module Ident I} {smod : Module Ident S}
         [mm : MatchInterface imod smod]
         : MatchInterface (imod.connect' o i) (smod.connect' o i) := by
  simp only [MatchInterface_simpler_iff] at *
  intro ident
  simp only [Module.connect', AssocList.eraseAll_map_comm]
  by_cases h1 : ident = i <;> by_cases h2 : ident = o <;> simp_all [AssocList.find?_eraseAll_neq, -AssocList.find?_eq]

private theorem getIO_mapVal_append_liftL {S S'} {a : PortMap Ident (RelIO S)} {b : PortMap Ident (RelIO S')} {ident}
    (h : a.contains ident) :
    PortMap.getIO (a.mapVal (fun _ => Module.liftL) ++ b.mapVal (fun _ => Module.liftR)) ident = Module.liftL (a.getIO ident) := by
  obtain ⟨x, hx⟩ := AssocList.contains_find?_iff.mpr h
  simp [PortMap.getIO, AssocList.append_find_left, AssocList.find?_mapVal, hx, -AssocList.find?_eq, -AssocList.find?_map_comm]

private theorem getIO_mapVal_append_liftR {S S'} {a : PortMap Ident (RelIO S)} {b : PortMap Ident (RelIO S')} {ident}
    (h : ¬ a.contains ident) :
    PortMap.getIO (a.mapVal (fun _ => Module.liftL) ++ b.mapVal (fun _ => Module.liftR)) ident = Module.liftR (b.getIO ident) := by
  unfold PortMap.getIO
  rw [AssocList.append_find_right _ _ (by simp only [AssocList.find?_mapVal, AssocList.contains_none h, Option.map_none])]
  simp only [AssocList.find?_mapVal]
  cases b.find? ident <;> simp [Module.liftR]

private theorem getIO_mapVal_append_fst {S S'} {a : PortMap Ident (RelIO S)} {b : PortMap Ident (RelIO S')} {ident} :
    (PortMap.getIO (a.mapVal (fun _ => Module.liftL) ++ b.mapVal (fun _ => Module.liftR)) ident).fst =
      if a.contains ident then (a.getIO ident).fst else (b.getIO ident).fst := by
  split <;> simp [getIO_mapVal_append_liftL, getIO_mapVal_append_liftR, Module.liftL, Module.liftR, *, -AssocList.contains_eq]

private theorem find?_isSome_eq_contains {α β} [DecidableEq α] {m : AssocList α β} {k} :
    (m.find? k).isSome = m.contains k :=
  Bool.eq_iff_iff.mpr AssocList.contains_find?_isSome_iff

theorem MatchInterface_product {I J S T} {imod : Module Ident I} {tmod : Module Ident T}
         {smod : Module Ident S} (jmod : Module Ident J) [inst1 : MatchInterface imod tmod]
         [inst2 : MatchInterface smod jmod] :
         MatchInterface (imod.product smod) (tmod.product jmod) := by
  obtain ⟨i1, o1, it1, ot1⟩ := inst1
  obtain ⟨i2, o2, it2, ot2⟩ := inst2
  simp only [find?_isSome_eq_contains] at i1 o1 i2 o2
  constructor <;> intro ident <;> simp only [Module.product, AssocList.lift_append, find?_isSome_eq_contains,
    AssocList.contains_append, AssocList.contains_mapval, getIO_mapVal_append_fst, *]

instance MatchInterface_product_instance {I J S T} {imod : Module Ident I} {tmod : Module Ident T}
         {smod : Module Ident S} (jmod : Module Ident J) [MatchInterface imod tmod]
         [MatchInterface smod jmod] :
         MatchInterface (imod.product smod) (tmod.product jmod) := by apply MatchInterface_product

theorem match_interface_inputs_contains {I S} {imod : Module Ident I} {smod : Module Ident S}
  [MatchInterface imod smod] {k}:
  imod.inputs.contains k ↔ smod.inputs.contains k := by
  simp only [← AssocList.contains_find?_isSome_iff, ‹MatchInterface imod smod›.inputs_present k]

theorem match_interface_outputs_contains {I S} {imod : Module Ident I} {smod : Module Ident S}
  [MatchInterface imod smod] {k}:
  imod.outputs.contains k ↔ smod.outputs.contains k := by
  simp only [← AssocList.contains_find?_isSome_iff, ‹MatchInterface imod smod›.outputs_present k]

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

instance MatchInterface_product_associative {I S J} {imod : Module Ident I} {smod : Module Ident S} {jmod : Module Ident J} : MatchInterface (imod.product (smod.product jmod)) ((imod.product smod).product jmod) := by
  constructor <;> intro ident <;> simp only [Module.product, AssocList.lift_append, find?_isSome_eq_contains,
    AssocList.contains_append, AssocList.contains_mapval, getIO_mapVal_append_fst, Bool.or_assoc]
  all_goals repeat' split
  all_goals simp_all [-AssocList.contains_eq]

instance MatchInterface_product_associative' {I S J} {imod : Module Ident I} {smod : Module Ident S} {jmod : Module Ident J}
  : MatchInterface ((imod.product smod).product jmod) (imod.product (smod.product jmod))
  := MatchInterface_symmetric _ MatchInterface_product_associative

private theorem disjoint_keys_contains {α β γ} [DecidableEq α] {a : AssocList α β} {b : AssocList α γ} {i}
    (h : a.disjoint_keys b) (ha : a.contains i) : ¬ b.contains i := by
  obtain ⟨x, hx⟩ := AssocList.contains_find?_iff.mpr ha
  simp [← AssocList.contains_find?_isSome_iff, AssocList.disjoint_keys_find_some h hx, -AssocList.contains_eq, -AssocList.find?_eq]

private theorem getIO_fst_of_not_contains {S} {m : PortMap Ident (RelIO S)} {ident} (h : ¬ m.contains ident) :
    (m.getIO ident).fst = PUnit := by
  simp [PortMap.getIO_none _ _ (AssocList.contains_none h)]

theorem MatchInterface_product_commutative {I S} {imod : Module Ident I} {smod : Module Ident S}
  (h : Disjoint imod smod)
  : MatchInterface (imod.product smod) (smod.product imod) := by
  obtain ⟨hl, hr⟩ := h
  constructor <;> intro ident <;> simp only [Module.product, AssocList.lift_append, find?_isSome_eq_contains,
    AssocList.contains_append, AssocList.contains_mapval, getIO_mapVal_append_fst, Bool.or_comm]
  all_goals split <;> split <;>
    simp_all [disjoint_keys_contains hl, disjoint_keys_contains hr, getIO_fst_of_not_contains, -AssocList.contains_eq]

end Match

theorem existSR_reflexive {S} {rules : List (RelInt S)} {s} :
  existSR rules s s := existSR.done s

theorem existSR_transitive {S} (rules : List (RelInt S)) :
  ∀ s₁ s₂ s₃,
    existSR rules s₁ s₂ →
    existSR rules s₂ s₃ →
    existSR rules s₁ s₃ := by
  intro s₁ s₂ s₃ He1 He2
  induction He1 with
  | done => grind
  | step _ _ _ _ hmem hr _ ih => grind [existSR.step]

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
  | done => apply existSR.done
  | step _ mid _ rule hmem hr _ ih => apply existSR.step _ (mid, t₁) _ (Module.liftL' rule) (List.mem_map_of_mem hmem) (by simp_all [Module.liftL']) ih

theorem existSR_liftR' {S T} (rules : List (RelInt S)) :
  ∀ s₁ s₂ (t₁ : T),
    existSR rules s₁ s₂ →
    existSR (rules.map Module.liftR') (t₁, s₁) (t₁, s₂) := by
  intro s₁ s₂ t₁ hrule
  induction hrule with
  | done => apply existSR.done
  | step _ mid _ rule hmem hr _ ih => apply existSR.step _ (t₁, mid) _ (Module.liftR' rule) (List.mem_map_of_mem hmem) (by simp_all [Module.liftR']) ih

theorem existSR_cons {S} {r} {rules : List (RelInt S)} :
  ∀ s₁ s₂,
    existSR rules s₁ s₂ →
    existSR (r :: rules) s₁ s₂ := by
  intro s₁ s₂ hrule
  induction hrule with
  | done => apply existSR.done
  | step _ _ _ _ hmem hr _ ih => grind [existSR.step]

theorem existSR_single_step {S : Type _} (rules : List (S → S → Prop)):
  ∀ s s', ∀ rule ∈ rules, rule s s' → existSR rules s s' := by
  intro s₁ s₂ rule hmem hr; apply existSR.step _ _ _ _ hmem hr (.done _)

theorem existSR_single_step' {S : Type _} (rules : List (S → S → Prop)):
  ∀ s₁ s₂, (∃ r ∈ rules, r s₁ s₂) → existSR rules s₁ s₂ := by
  intro s₁ s₂ ⟨r, hmem, hr⟩; apply existSR.step _ _ _ _ hmem hr (.done _)

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

private theorem product_inputs_getIO_left_fst {J K} {m₁ : Module Ident J} {m₂ : Module Ident K} {ident}
    (h : m₁.inputs.contains ident) : ((m₁.product m₂).inputs.getIO ident).fst = (m₁.inputs.getIO ident).fst :=
  congrArg Sigma.fst (getIO_mapVal_append_liftL h)

private theorem product_inputs_getIO_right_fst {J K} {m₁ : Module Ident J} {m₂ : Module Ident K} {ident}
    (h : ¬ m₁.inputs.contains ident) : ((m₁.product m₂).inputs.getIO ident).fst = (m₂.inputs.getIO ident).fst :=
  congrArg Sigma.fst (getIO_mapVal_append_liftR h)

private theorem product_outputs_getIO_left_fst {J K} {m₁ : Module Ident J} {m₂ : Module Ident K} {ident}
    (h : m₁.outputs.contains ident) : ((m₁.product m₂).outputs.getIO ident).fst = (m₁.outputs.getIO ident).fst :=
  congrArg Sigma.fst (getIO_mapVal_append_liftL h)

private theorem product_outputs_getIO_right_fst {J K} {m₁ : Module Ident J} {m₂ : Module Ident K} {ident}
    (h : ¬ m₁.outputs.contains ident) : ((m₁.product m₂).outputs.getIO ident).fst = (m₂.outputs.getIO ident).fst :=
  congrArg Sigma.fst (getIO_mapVal_append_liftR h)

/-- Executing an input rule of a product executes the rule of the module that owns the port. -/
private theorem product_inputs_getIO_snd {J K} {m₁ : Module Ident J} {m₂ : Module Ident K} {ident} {s s' : J × K} {v} :
    ((m₁.product m₂).inputs.getIO ident).snd s v s' ↔
      if h : m₁.inputs.contains ident then
        (m₁.inputs.getIO ident).snd s.1 (cast (product_inputs_getIO_left_fst h) v) s'.1 ∧ s.2 = s'.2
      else
        (m₂.inputs.getIO ident).snd s.2 (cast (product_inputs_getIO_right_fst h) v) s'.2 ∧ s.1 = s'.1 := by
  split
  · rw [PortMap.rw_rule_execution (a := (m₁.product m₂).inputs.getIO ident) (getIO_mapVal_append_liftL ‹_›)]; rfl
  · rw [PortMap.rw_rule_execution (a := (m₁.product m₂).inputs.getIO ident) (getIO_mapVal_append_liftR ‹_›)]; rfl

/-- Executing an output rule of a product executes the rule of the module that owns the port. -/
private theorem product_outputs_getIO_snd {J K} {m₁ : Module Ident J} {m₂ : Module Ident K} {ident} {s s' : J × K} {v} :
    ((m₁.product m₂).outputs.getIO ident).snd s v s' ↔
      if h : m₁.outputs.contains ident then
        (m₁.outputs.getIO ident).snd s.1 (cast (product_outputs_getIO_left_fst h) v) s'.1 ∧ s.2 = s'.2
      else
        (m₂.outputs.getIO ident).snd s.2 (cast (product_outputs_getIO_right_fst h) v) s'.2 ∧ s.1 = s'.1 := by
  split
  · rw [PortMap.rw_rule_execution (a := (m₁.product m₂).outputs.getIO ident) (getIO_mapVal_append_liftL ‹_›)]; rfl
  · rw [PortMap.rw_rule_execution (a := (m₁.product m₂).outputs.getIO ident) (getIO_mapVal_append_liftR ‹_›)]; rfl

private theorem product_inputs_contains {J K} {m₁ : Module Ident J} {m₂ : Module Ident K} {ident} :
    (m₁.product m₂).inputs.contains ident = (m₁.inputs.contains ident || m₂.inputs.contains ident) := by
  simp only [product, AssocList.lift_append, AssocList.contains_append, AssocList.contains_mapval]

private theorem product_outputs_contains {J K} {m₁ : Module Ident J} {m₂ : Module Ident K} {ident} :
    (m₁.product m₂).outputs.contains ident = (m₁.outputs.contains ident || m₂.outputs.contains ident) := by
  simp only [product, AssocList.lift_append, AssocList.contains_append, AssocList.contains_mapval]

omit mm in
theorem rule_product_associative_input {J} (jmod : Module Ident J) {i₁ i₂ i₃} {new_i new_s new_j} {ident} {v}:
  ((imod.product (smod.product jmod)).inputs.getIO ident).snd (i₁, i₂, i₃) v (new_i, new_s, new_j) →
  (((imod.product smod).product jmod).inputs.getIO ident).snd ((i₁, i₂), i₃) ((MatchInterface.input_types ident).mp v) ((new_i, new_s), new_j) := by
  by_cases h1 : imod.inputs.contains ident <;> by_cases h2 : smod.inputs.contains ident <;>
    simp_all [product_inputs_getIO_snd, product_inputs_contains, -AssocList.contains_eq]

omit mm in
theorem rule_product_associative_output {J} (jmod : Module Ident J) {i₁ i₂ i₃} {new_i new_s new_j} {ident} {v}:
  ((imod.product (smod.product jmod)).outputs.getIO ident).snd (i₁, i₂, i₃) v (new_i, new_s, new_j) →
  (((imod.product smod).product jmod).outputs.getIO ident).snd ((i₁, i₂), i₃) ((MatchInterface.output_types ident).mp v) ((new_i, new_s), new_j) := by
  by_cases h1 : imod.outputs.contains ident <;> by_cases h2 : smod.outputs.contains ident <;>
    simp_all [product_outputs_getIO_snd, product_outputs_contains, -AssocList.contains_eq]

omit mm in
theorem rule_product_associative'_input {J} (jmod : Module Ident J) {i₁ i₂ i₃} {new_i new_s new_j} {ident} {v}:
  (((imod.product smod).product jmod).inputs.getIO ident).snd ((i₁, i₂), i₃) v ((new_i, new_s), new_j) →
  ((imod.product (smod.product jmod)).inputs.getIO ident).snd (i₁, i₂, i₃) ((MatchInterface.input_types ident).mp v) (new_i, new_s, new_j) := by
  by_cases h1 : imod.inputs.contains ident <;> by_cases h2 : smod.inputs.contains ident <;>
    simp_all [product_inputs_getIO_snd, product_inputs_contains, -AssocList.contains_eq]

omit mm in
theorem rule_product_associative'_output {J} (jmod : Module Ident J) {i₁ i₂ i₃} {new_i new_s new_j} {ident} {v}:
  (((imod.product smod).product jmod).outputs.getIO ident).snd ((i₁, i₂), i₃) v ((new_i, new_s), new_j) →
  ((imod.product (smod.product jmod)).outputs.getIO ident).snd (i₁, i₂, i₃) ((MatchInterface.output_types ident).mp v) (new_i, new_s, new_j) := by
  by_cases h1 : imod.outputs.contains ident <;> by_cases h2 : smod.outputs.contains ident <;>
    simp_all [product_outputs_getIO_snd, product_outputs_contains, -AssocList.contains_eq]

omit mm in
theorem rule_product_commutative_input {i₁ i₂} {mid_i mid_s} {ident} {v} (h : Disjoint imod smod) :
  have _ := MatchInterface_product_commutative h
  ((imod.product smod).inputs.getIO ident).snd (i₁, i₂) v (mid_i, mid_s) →
  ((smod.product imod).inputs.getIO ident).snd (i₂, i₁) ((MatchInterface.input_types ident).mp v) (mid_s, mid_i) := by
  intro _ rule
  simp only [product_inputs_getIO_snd] at rule ⊢
  by_cases h1 : imod.inputs.contains ident
  · have h2 := disjoint_keys_contains h.1 h1
    simp only [h1, h2, ↓reduceDIte, Bool.false_eq_true] at rule ⊢
    simpa [cast_cast] using rule
  · simp only [h1, ↓reduceDIte, Bool.false_eq_true] at rule ⊢
    by_cases h2 : smod.inputs.contains ident
    · simp only [h2, ↓reduceDIte]
      simpa [cast_cast] using rule
    · grind [PortMap.getIO_not_contained_false]

omit mm in
theorem rule_product_commutative_output {i₁ i₂} {mid_i mid_s} {ident} {v} (h : Disjoint imod smod) :
  have _ := MatchInterface_product_commutative h
  ((imod.product smod).outputs.getIO ident).snd (i₁, i₂) v (mid_i, mid_s) →
  ((smod.product imod).outputs.getIO ident).snd (i₂, i₁) ((MatchInterface.output_types ident).mp v) (mid_s, mid_i) := by
  intro _ rule
  simp only [product_outputs_getIO_snd] at rule ⊢
  by_cases h1 : imod.outputs.contains ident
  · have h2 := disjoint_keys_contains h.2 h1
    simp only [h1, h2, ↓reduceDIte, Bool.false_eq_true] at rule ⊢
    simpa [cast_cast] using rule
  · simp only [h1, ↓reduceDIte, Bool.false_eq_true] at rule ⊢
    by_cases h2 : smod.outputs.contains ident
    · simp only [h2, ↓reduceDIte]
      simpa [cast_cast] using rule
    · grind [PortMap.getIO_not_contained_false]

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
  intro init_i init_s rfl
  refine ⟨fun _ mid_i _ h => ⟨mid_i, mid_i, h, .done _, rfl⟩, fun _ mid_i _ h => ⟨_, mid_i, .done _, h, rfl⟩,
    fun _ mid_i hr h => ⟨mid_i, .step _ _ _ _ hr h (.done _), rfl⟩⟩

theorem refines_φ_reflexive_ext imod' (h : imod.EqExt imod') (mm := MatchInterface_EqExt h) :
    imod ⊑_{Eq} imod' := by
  intro init_i init_s rfl
  obtain ⟨Hl, Hr, Hint, -⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro ident mid_i v hrule
    rw [PortMap.rw_rule_execution (PortMap.EqExt_getIO Hl ident)] at hrule
    refine ⟨mid_i, mid_i, hrule, .done _, rfl⟩
  · intro ident mid_i v hrule
    rw [PortMap.rw_rule_execution (PortMap.EqExt_getIO Hr ident)] at hrule
    refine ⟨init_i, mid_i, .done _, hrule, rfl⟩
  · intro r mid_i hr hrule
    refine ⟨mid_i, .step _ _ _ _ (Hint.mem_iff.mp hr) hrule (.done _), rfl⟩

theorem refines_φ_multistep :
    ∀ φ, imod ⊑_{φ} smod →
    ∀ i_init s_init,
      φ i_init s_init →
      ∀ i_mid, existSR imod.internals i_init i_mid →
      ∃ s_mid,
        existSR smod.internals s_init s_mid
        ∧ φ i_mid s_mid := by
  intro φ Href i_init s_init Hphi i_mid Hexist
  induction Hexist generalizing s_init with
  | done => grind [existSR.done]
  | step _ _ _ rule hmem hrule _ ih =>
    obtain ⟨s_mid, hex, hφ⟩ := (Href _ _ Hphi).internals rule _ hmem hrule
    grind [existSR_transitive]

theorem existsSR_mid {φ} (H : imod ⊑_{φ} smod) init_i init_s:
    φ init_i init_s →
    ∀ mid_i,
      existSR imod.internals init_i mid_i →
      ∃ mid_s, existSR smod.internals init_s mid_s ∧ φ mid_i mid_s := by
  apply refines_φ_multistep _ _ _ H

theorem refines_φ_transitive {J} (smod' : Module Ident J) {φ₁ φ₂}
  [MatchInterface imod smod']
  [MatchInterface smod' smod]:
    imod ⊑_{φ₁} smod' →
    smod' ⊑_{φ₂} smod →
    imod ⊑_{λ a b => ∃ c, φ₁ a c ∧ φ₂ c b} smod := by
  intro h1 h2 init_i init_s ⟨init_j, Hφ₁, Hφ₂⟩
  obtain ⟨in₁, out₁, int₁⟩ := h1 _ _ Hφ₁
  refine ⟨?_, ?_, ?_⟩
  · intro ident mid_i v Hrule
    obtain ⟨a_j, m_j, hr₁, hex₁, hφ₁⟩ := in₁ _ _ _ Hrule
    obtain ⟨a_s, m_s, hr₂, hex₂, hφ₂⟩ := (h2 _ _ Hφ₂).inputs _ _ _ hr₁
    obtain ⟨m_s', hex₃, hφ₃⟩ := refines_φ_multistep _ _ _ h2 _ _ hφ₂ _ hex₁
    refine ⟨a_s, m_s', by simpa using hr₂, existSR_transitive _ _ _ _ hex₂ hex₃, m_j, hφ₁, hφ₃⟩
  · intro ident mid_i v Hrule
    obtain ⟨a_j, m_j, hex₁, hr₁, hφ₁⟩ := out₁ _ _ _ Hrule
    obtain ⟨a_s, hex₂, hφa⟩ := refines_φ_multistep _ _ _ h2 _ _ Hφ₂ _ hex₁
    obtain ⟨a_s', m_s, hex₃, hr₂, hφ₂⟩ := (h2 _ _ hφa).outputs _ _ _ hr₁
    refine ⟨a_s', m_s, existSR_transitive _ _ _ _ hex₂ hex₃, by simpa using hr₂, m_j, hφ₁, hφ₂⟩
  · intro rule mid_i ruleIn Hrule
    obtain ⟨m_j, hex₁, hφ₁⟩ := int₁ rule mid_i ruleIn Hrule
    obtain ⟨m_s, hex₂, hφ₂⟩ := refines_φ_multistep _ _ _ h2 _ _ Hφ₂ _ hex₁
    refine ⟨m_s, hex₂, m_j, hφ₁, hφ₂⟩

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
  refine ⟨inferInstance, Eq, refines_φ_reflexive imod, fun i hi => ⟨i, hi, rfl⟩⟩

theorem refines_reflexive_ext imod' (h : imod.EqExt imod') : imod ⊑ imod' := by
  have _ := MatchInterface_EqExt h
  refine ⟨inferInstance, Eq, refines_φ_reflexive_ext imod imod' h, refines_initial_reflexive_ext imod imod' h (φ := Eq) (Hφ := fun _ => rfl)⟩

theorem refines_transitive {J} (imod' : Module Ident J):
    imod ⊑ imod' →
    imod' ⊑ smod →
    imod ⊑ smod := by
  intro ⟨mm1, R1, h11, h12⟩ ⟨mm2, R2, h21, h22⟩
  have mm3 := MatchInterface_transitive imod' mm1 mm2
  refine ⟨mm3, fun a b => ∃ c, R1 a c ∧ R2 c b, refines_φ_transitive imod smod imod' h11 h21, ?_⟩
  intro i hi
  obtain ⟨i', hi', hR1⟩ := h12 _ hi
  obtain ⟨s, hs, hR2⟩ := h22 _ hi'
  refine ⟨s, hs, i', hR1, hR2⟩

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
  intro href₁ href₂ ⟨i₁, i₂⟩ ⟨s₁, s₂⟩ ⟨hφ₁, hφ₂⟩
  obtain ⟨in₁, out₁, int₁⟩ := href₁ _ _ hφ₁
  obtain ⟨in₂, out₂, int₂⟩ := href₂ _ _ hφ₂
  refine ⟨?_, ?_, ?_⟩
  · intro ident ⟨m₁, m₂⟩ v hrule
    simp only [product_inputs_getIO_snd] at hrule ⊢
    by_cases hc : imod.inputs.contains ident
    · have hc' : smod.inputs.contains ident := match_interface_inputs_contains.mp hc
      simp only [hc, hc', ↓reduceDIte] at hrule ⊢
      obtain ⟨hr, rfl⟩ := hrule
      obtain ⟨a, b, hsa, hex, hφ⟩ := in₁ ident m₁ _ hr
      refine ⟨(a, s₂), (b, s₂), ⟨by simpa [cast_cast] using hsa, rfl⟩, existSR_product_l hex, hφ, hφ₂⟩
    · have hc' : ¬ smod.inputs.contains ident := fun h => hc (match_interface_inputs_contains.mpr h)
      simp only [hc, hc', ↓reduceDIte, Bool.false_eq_true] at hrule ⊢
      obtain ⟨hr, rfl⟩ := hrule
      obtain ⟨a, b, hsa, hex, hφ⟩ := in₂ ident m₂ _ hr
      refine ⟨(s₁, a), (s₁, b), ⟨by simpa [cast_cast] using hsa, rfl⟩, existSR_product_r hex, hφ₁, hφ⟩
  · intro ident ⟨m₁, m₂⟩ v hrule
    simp only [product_outputs_getIO_snd] at hrule ⊢
    by_cases hc : imod.outputs.contains ident
    · have hc' : smod.outputs.contains ident := match_interface_outputs_contains.mp hc
      simp only [hc, hc', ↓reduceDIte] at hrule ⊢
      obtain ⟨hr, rfl⟩ := hrule
      obtain ⟨a, b, hex, hsb, hφ⟩ := out₁ ident m₁ _ hr
      refine ⟨(a, s₂), (b, s₂), existSR_product_l hex, ⟨by simpa [cast_cast] using hsb, rfl⟩, hφ, hφ₂⟩
    · have hc' : ¬ smod.outputs.contains ident := fun h => hc (match_interface_outputs_contains.mpr h)
      simp only [hc, hc', ↓reduceDIte, Bool.false_eq_true] at hrule ⊢
      obtain ⟨hr, rfl⟩ := hrule
      obtain ⟨a, b, hex, hsb, hφ⟩ := out₂ ident m₂ _ hr
      refine ⟨(s₁, a), (s₁, b), existSR_product_r hex, ⟨by simpa [cast_cast] using hsb, rfl⟩, hφ₁, hφ⟩
  · intro rule ⟨m₁, m₂⟩ hmem hrule
    simp only [product, List.mem_append, List.mem_map] at hmem
    obtain ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ := hmem
    · obtain ⟨hr', rfl⟩ := liftL'_rule_eq hrule
      obtain ⟨s, hex, hφ⟩ := int₁ r m₁ hr hr'
      refine ⟨(s, s₂), existSR_product_l hex, hφ, hφ₂⟩
    · obtain ⟨hr', rfl⟩ := liftR'_rule_eq hrule
      obtain ⟨s, hex, hφ⟩ := int₂ r m₂ hr hr'
      refine ⟨(s₁, s), existSR_product_r hex, hφ₁, hφ⟩

theorem refines_product {J K} (imod₂ : Module Ident J) (smod₂ : Module Ident K):
    imod ⊑ smod →
    imod₂ ⊑ smod₂ →
    imod.product imod₂ ⊑ smod.product smod₂ := by
  intro ⟨_, R, Href, Hinit⟩ ⟨_, R2, Href₂, Hinit₂⟩
  refine ⟨inferInstance, fun a b => R a.1 b.1 ∧ R2 a.2 b.2, refines_φ_product Href Href₂, ?_⟩
  intro ⟨i₁, i₂⟩ ⟨Hi, Hj⟩
  obtain ⟨s1, hs1, hR1⟩ := Hinit _ Hi
  obtain ⟨s2, hs2, hR2⟩ := Hinit₂ _ Hj
  refine ⟨(s1, s2), ⟨hs1, hs2⟩, hR1, hR2⟩

theorem refines_φ_product_associative {J} (jmod : Module Ident J):
    imod.product (smod.product jmod) ⊑_{fun | (i₁, i₂, i₃), ((s₁, s₂), s₃) => i₁ = s₁ ∧ i₂ = s₂ ∧ i₃ = s₃} (imod.product smod).product jmod := by
  intro (i_init, s_init, j_init) ((i_init', s_init'), j_init') ⟨rfl, rfl, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · intro ident (mid_i, mid_s, mid_j) v rule
    refine ⟨((mid_i, mid_s), mid_j), ((mid_i, mid_s), mid_j), rule_product_associative_input _ _ _ rule, existSR.done _, rfl, rfl, rfl⟩
  · intro ident (mid_i, mid_s, mid_j) v rule
    refine ⟨_, ((mid_i, mid_s), mid_j), existSR.done _, rule_product_associative_output _ _ _ rule, rfl, rfl, rfl⟩
  · intro r (mid_i, mid_s, mid_j) hrule rule
    refine ⟨((mid_i, mid_s), mid_j), ?_, rfl, rfl, rfl⟩
    simp only [product, List.map_append, List.map_map, List.mem_append, List.mem_map, Function.comp_apply] at hrule
    obtain ⟨r', hr', rfl⟩ | ⟨r', hr', rfl⟩ | ⟨r', hr', rfl⟩ := hrule
    · apply existSR_single_step _ _ _ (liftL' (liftL' r')) (by simp [product]; grind) (by simp_all [liftL'])
    · apply existSR_single_step _ _ _ (liftL' (liftR' r')) (by simp [product]; grind) (by simp_all [liftL', liftR'])
    · apply existSR_single_step _ _ _ (liftR' r') (by simp [product]; grind) (by simp_all [liftL', liftR'])

theorem refines_φ_product_associative' {J} (jmod : Module Ident J):
    (imod.product smod).product jmod ⊑_{fun | ((i₁, i₂), i₃), (s₁, s₂, s₃) => i₁ = s₁ ∧ i₂ = s₂ ∧ i₃ = s₃} imod.product (smod.product jmod) := by
  intro ((i_init, s_init), j_init) (i_init', s_init', j_init') ⟨rfl, rfl, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · intro ident ((mid_i, mid_s), mid_j) v rule
    refine ⟨(mid_i, mid_s, mid_j), (mid_i, mid_s, mid_j), rule_product_associative'_input _ _ _ rule, existSR.done _, rfl, rfl, rfl⟩
  · intro ident ((mid_i, mid_s), mid_j) v rule
    refine ⟨_, (mid_i, mid_s, mid_j), existSR.done _, rule_product_associative'_output _ _ _ rule, rfl, rfl, rfl⟩
  · intro r ((mid_i, mid_s), mid_j) hrule rule
    refine ⟨(mid_i, mid_s, mid_j), ?_, rfl, rfl, rfl⟩
    simp only [product, List.map_append, List.map_map, List.mem_append, List.mem_map, Function.comp_apply] at hrule
    obtain (⟨r', hr', rfl⟩ | ⟨r', hr', rfl⟩) | ⟨r', hr', rfl⟩ := hrule
    · apply existSR_single_step _ _ _ (liftL' r') (by simp [product]; grind) (by simp_all [liftL'])
    · apply existSR_single_step _ _ _ (liftR' (liftL' r')) (by simp [product]; grind) (by simp_all [liftL', liftR'])
    · apply existSR_single_step _ _ _ (liftR' (liftR' r')) (by simp [product]; grind) (by simp_all [liftL', liftR'])

theorem refines_product_associative {J} {jmod : Module Ident J} :
  imod.product (smod.product jmod) ⊑ (imod.product smod).product jmod := by
  refine ⟨inferInstance, fun | (i₁, i₂, i₃), ((s₁, s₂), s₃) => i₁ = s₁ ∧ i₂ = s₂ ∧ i₃ = s₃, refines_φ_product_associative _, ?_⟩
  intro (i, s, j) ⟨hi, hs, hj⟩
  refine ⟨((i, s), j), ⟨⟨hi, hs⟩, hj⟩, rfl, rfl, rfl⟩

theorem refines_product_associative' {J} {jmod : Module Ident J} :
  (imod.product smod).product jmod ⊑ imod.product (smod.product jmod) := by
  refine ⟨inferInstance, fun | ((i₁, i₂), i₃), (s₁, s₂, s₃) => i₁ = s₁ ∧ i₂ = s₂ ∧ i₃ = s₃, refines_φ_product_associative' _, ?_⟩
  intro ((i, s), j) ⟨⟨hi, hs⟩, hj⟩
  refine ⟨(i, s, j), ⟨hi, hs, hj⟩, rfl, rfl, rfl⟩

theorem refines_φ_product_commutative (h : Disjoint imod smod) :
  have _ := MatchInterface_product_commutative h
  (imod.product smod) ⊑_{fun | (i₁, i₂), (s₁, s₂) => i₁ = s₂ ∧ i₂ = s₁} (smod.product imod) := by
  intro _ (i_init, s_init) (i_init', s_init') ⟨rfl, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · intro ident (mid_i, mid_s) v rule
    refine ⟨(mid_s, mid_i), (mid_s, mid_i), rule_product_commutative_input _ _ h rule, existSR.done _, rfl, rfl⟩
  · intro ident (mid_i, mid_s) v rule
    refine ⟨_, (mid_s, mid_i), existSR.done _, rule_product_commutative_output _ _ h rule, rfl, rfl⟩
  · intro r (mid_i, mid_s) hrule rule
    refine ⟨(mid_s, mid_i), ?_, rfl, rfl⟩
    simp only [product, List.mem_append, List.mem_map] at hrule
    obtain ⟨r', hr', rfl⟩ | ⟨r', hr', rfl⟩ := hrule
    · apply existSR_single_step _ _ _ (liftR' r') (by simp [product]; grind) (by simp_all [liftL', liftR'])
    · apply existSR_single_step _ _ _ (liftL' r') (by simp [product]; grind) (by simp_all [liftL', liftR'])

theorem refines_product_commutative (h : Disjoint imod smod) :
  (imod.product smod) ⊑ smod.product imod := by
  refine ⟨MatchInterface_product_commutative h, fun | (i₁, i₂), (s₁, s₂) => i₁ = s₂ ∧ i₂ = s₁, refines_φ_product_commutative h, ?_⟩
  intro (i, s) ⟨hi, hs⟩
  refine ⟨(s, i), ⟨hs, hi⟩, rfl, rfl⟩

theorem refines_φ_connect [MatchInterface imod smod] {φ i o} :
    imod ⊑_{φ} smod → imod.connect' o i ⊑_{φ} smod.connect' o i := by
  intro href init_i init_s hphi
  obtain ⟨hin, hout, hint⟩ := href _ _ hphi
  refine ⟨?_, ?_, ?_⟩
  · intro ident mid_i v hrule
    by_cases h : ident = i
    · exfalso; apply PortMap.getIO_not_contained_false hrule
      simpa [connect', h] using AssocList.eraseAll_not_contains2 imod.inputs i
    · rw [PortMap.rw_rule_execution (a := (imod.connect' o i).inputs.getIO ident) (PortMap.getIO_eraseAll_neq h)] at hrule
      obtain ⟨a, b, hsa, hex, hφ⟩ := hin _ _ _ hrule
      refine ⟨a, b, ?_, existSR_cons _ _ hex, hφ⟩
      rw [PortMap.rw_rule_execution (a := (smod.connect' o i).inputs.getIO ident) (PortMap.getIO_eraseAll_neq h)]
      simpa [cast_cast] using hsa
  · intro ident mid_i v hrule
    by_cases h : ident = o
    · exfalso; apply PortMap.getIO_not_contained_false hrule
      simpa [connect', h] using AssocList.eraseAll_not_contains2 imod.outputs o
    · rw [PortMap.rw_rule_execution (a := (imod.connect' o i).outputs.getIO ident) (PortMap.getIO_eraseAll_neq h)] at hrule
      obtain ⟨a, b, hex, hsb, hφ⟩ := hout _ _ _ hrule
      refine ⟨a, b, existSR_cons _ _ hex, ?_, hφ⟩
      rw [PortMap.rw_rule_execution (a := (smod.connect' o i).outputs.getIO ident) (PortMap.getIO_eraseAll_neq h)]
      simpa [cast_cast] using hsb
  · intro rule mid_i hmem hrule
    simp only [connect', List.mem_cons] at hmem
    obtain rfl | hmem := hmem
    · obtain ⟨hrule, hwf⟩ := hrule
      have HEQ := Classical.not_not.mp hwf
      obtain ⟨cons, out, h1, h2⟩ := hrule HEQ
      obtain ⟨a_o, m_o, hex_o, hrs_o, hφ_o⟩ := hout o cons out h1
      obtain ⟨a_i, m_i, hrs_i, hex_i, hφ_i⟩ := (href _ _ hφ_o).inputs i mid_i _ h2
      refine ⟨m_i, existSR_transitive _ _ _ _ (existSR_cons _ _ hex_o) (.step _ a_i _ (connect'' (smod.outputs.getIO o).2 (smod.inputs.getIO i).2) (by simp [connect']) ?_ (existSR_cons _ _ hex_i)), hφ_i⟩
      refine ⟨fun _ => ⟨m_o, _, hrs_o, by simpa [cast_cast] using hrs_i⟩, fun hne => hne ?_⟩
      simpa [‹MatchInterface imod smod›.input_types, ‹MatchInterface imod smod›.output_types] using HEQ
    · obtain ⟨s, hex, hφ⟩ := hint _ _ hmem hrule
      refine ⟨s, existSR_cons _ _ hex, hφ⟩

theorem refines_connect {o i} :
    imod ⊑ smod →
    imod.connect' o i ⊑ smod.connect' o i := by
  intro ⟨_, R, Href, Hinit⟩
  refine ⟨inferInstance, R, refines_φ_connect Href, by simpa [refines_initial, connect'] using Hinit⟩

theorem refines_φ_mapInputPorts {I S} {imod : Module Ident I} {smod : Module Ident S}
  [MatchInterface imod smod] {f φ} {h : Function.Bijective f} :
  have _ := MatchInterface_mapInputPorts (imod := imod) (smod := smod) h
  imod ⊑_{φ} smod →
  imod.mapInputPorts f ⊑_{φ} smod.mapInputPorts f := by
  intro _ href init_i init_s hphi
  obtain ⟨hin, hout, hint⟩ := href _ _ hphi
  refine ⟨?_, hout, hint⟩
  intro ident mid_i v hrule
  obtain ⟨ident', rfl⟩ := h.surjective ident
  have hi : (imod.mapInputPorts f).inputs.getIO (f ident') = imod.inputs.getIO ident' := by
    simp only [mapInputPorts, PortMap.getIO, AssocList.mapKey_find? h.injective]
  have hs : (smod.mapInputPorts f).inputs.getIO (f ident') = smod.inputs.getIO ident' := by
    simp only [mapInputPorts, PortMap.getIO, AssocList.mapKey_find? h.injective]
  rw [PortMap.rw_rule_execution hi] at hrule
  obtain ⟨a, b, hsa, hex, hφ⟩ := hin _ _ _ hrule
  refine ⟨a, b, ?_, hex, hφ⟩
  rw [PortMap.rw_rule_execution hs]; simpa [cast_cast] using hsa

theorem refines_mapInputPorts {I S} {imod : Module Ident I} {smod : Module Ident S} {f}
  (h : Function.Bijective f) :
  imod ⊑ smod →
  imod.mapInputPorts f ⊑ smod.mapInputPorts f := by
  intro ⟨_, R, Href, Hinit⟩
  refine ⟨MatchInterface_mapInputPorts (imod := imod) (smod := smod) h, R, refines_φ_mapInputPorts (h := h) Href, by simpa [refines_initial, mapInputPorts] using Hinit⟩

theorem refines_φ_mapOutputPorts {I S} {imod : Module Ident I} {smod : Module Ident S}
  [MatchInterface imod smod] {f φ} {h : Function.Bijective f} :
  have _ := MatchInterface_mapOutputPorts (imod := imod) (smod := smod) h
  imod ⊑_{φ} smod →
  imod.mapOutputPorts f ⊑_{φ} smod.mapOutputPorts f := by
  intro _ href init_i init_s hphi
  obtain ⟨hin, hout, hint⟩ := href _ _ hphi
  refine ⟨hin, ?_, hint⟩
  intro ident mid_i v hrule
  obtain ⟨ident', rfl⟩ := h.surjective ident
  have hi : (imod.mapOutputPorts f).outputs.getIO (f ident') = imod.outputs.getIO ident' := by
    simp only [mapOutputPorts, PortMap.getIO, AssocList.mapKey_find? h.injective]
  have hs : (smod.mapOutputPorts f).outputs.getIO (f ident') = smod.outputs.getIO ident' := by
    simp only [mapOutputPorts, PortMap.getIO, AssocList.mapKey_find? h.injective]
  rw [PortMap.rw_rule_execution hi] at hrule
  obtain ⟨a, b, hex, hsb, hφ⟩ := hout _ _ _ hrule
  refine ⟨a, b, hex, ?_, hφ⟩
  rw [PortMap.rw_rule_execution hs]; simpa [cast_cast] using hsb

theorem refines_mapOutputPorts {I S} {imod : Module Ident I} {smod : Module Ident S} {f}
  (h : Function.Bijective f) :
  imod ⊑ smod →
  imod.mapOutputPorts f ⊑ smod.mapOutputPorts f := by
  intro ⟨_, R, Href, Hinit⟩
  refine ⟨MatchInterface_mapOutputPorts (imod := imod) (smod := smod) h, R, refines_φ_mapOutputPorts (h := h) Href, by simpa [refines_initial, mapOutputPorts] using Hinit⟩

theorem refines_mapPorts {I S} {imod : Module Ident I} {smod : Module Ident S} {f} (h : Function.Bijective f) :
  imod ⊑ smod →
  imod.mapPorts f ⊑ smod.mapPorts f := by
  intro Href; apply refines_mapOutputPorts h (refines_mapInputPorts h Href)

theorem refines_mapPorts2 {I S} {imod : Module Ident I} {smod : Module Ident S} {f g}
  (h : Function.Bijective f) (h : Function.Bijective g) :
  imod ⊑ smod →
  imod.mapPorts2 f g ⊑ smod.mapPorts2 f g := by
  intro Href; unfold mapPorts2; grind [refines_mapOutputPorts, refines_mapInputPorts]

theorem refines_renamePorts {I S} {imod : Module Ident I} {smod : Module Ident S} {p} :
  imod ⊑ smod →
  imod.renamePorts p ⊑ smod.renamePorts p := by
  intro Href; apply refines_mapPorts2 AssocList.bijectivePortRenaming_bijective AssocList.bijectivePortRenaming_bijective Href

theorem refines_eq' {imod : TModule Ident} {smod : TModule Ident} :
  imod = smod → imod.snd ⊑ smod.snd := by
  intro heq; subst imod; apply refines_reflexive

theorem refines_eq {imod : Module Ident I} {smod : Module Ident S} :
  Sigma.mk _ imod = Sigma.mk _ smod → imod ⊑ smod := refines_eq'

theorem refines_eq_relax {I' S'} {imod : Module Ident I} {imod' : Module Ident I'} {smod : Module Ident S} {smod' : Module Ident S'} :
  Sigma.mk _ imod = Sigma.mk _ imod' → Sigma.mk _ smod = Sigma.mk _ smod' → imod' ⊑ smod' → imod ⊑ smod := by
  intro ha hb hc
  apply refines_transitive _ (refines_eq ha) (refines_transitive _ hc (refines_eq hb.symm))

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
      | cons hd tl HR => simp only [List.foldl_cons, HR]

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
  simp only [List.mem_map, decide_eq_false_iff_not, not_exists, not_and]
  intro _ x hx heq
  rw [hfInj heq] at hx
  simp_all [List.nodup_cons]

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
    · rw [AssocList.eraseAll_eraseAllP]; congr; funext k v; grind
    · rw [AssocList.eraseAll_eraseAllP]; congr; funext k v; grind
    · rw [erase_decide_map (hdup := Hdup) (hfInj := hfInj), erase_decide_map (hdup := Hdup) (hfInj := hgInj)]
    · simp at Hdup; simpa [Hdup]

@[simp]
theorem renamePorts_inputs {Ident S} [DecidableEq Ident] {m : Module Ident S} {i}:
  (m.renamePorts i).inputs = m.inputs.mapKey i.input.bijectivePortRenaming := rfl

@[simp]
theorem renamePorts_outputs {Ident S} [DecidableEq Ident] {m : Module Ident S} {i}:
  (m.renamePorts i).outputs = m.outputs.mapKey i.output.bijectivePortRenaming := rfl

end Module

end Graphiti
