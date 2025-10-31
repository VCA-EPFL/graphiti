/-
Copyright (c) 2024, 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Core.ModuleLemmas
import Graphiti.Core.ExprLow
import Graphiti.Core.Environment
import Graphiti.Core.WellTyped

import Mathlib.Tactic
import Mathlib.Data.QPF.Univariate.Basic

open Batteries (AssocList)

namespace Graphiti

def Module.toBaseExprLow {Ident Typ S} (m : Module Ident S) (inst : Ident) (typ : Typ) : ExprLow Ident Typ :=
  .base (m.toPortMapping inst) typ

namespace ExprLow

section ExprLowLowering

variable {Ident Typ}
variable [DecidableEq Ident]

variable (ε : Env Ident Typ)

@[drunfold] def get_types (i : Typ) : Type _ :=
  (ε i) |>.map Sigma.fst |>.getD PUnit

@[drunfold] def ident_list : ExprLow Ident Typ → List Typ
| .base i e => [e]
| .connect _ e => e.ident_list
| .product a b => a.ident_list ++ b.ident_list

abbrev EType (e : ExprLow Ident Typ) := HVector (get_types ε) e.ident_list

@[drunfold] def build_moduleD
    : (e : ExprLow Ident Typ) → Option (Module Ident (EType ε e))
| .base i e =>
  match h : ε e with
  | some mod =>
    have H : mod.1 = get_types ε e := by
      simp_all [get_types]
    some ((H ▸ mod.2).liftD)
  | none => none
| .connect c e' => do
  let e ← e'.build_moduleD
  return e.connect' c.output c.input
| .product a b => do
  let a ← a.build_moduleD;
  let b ← b.build_moduleD;
  return a.productD b

theorem filterId_empty {α} [DecidableEq α] : PortMapping.filterId (Ident := α) ∅ = ∅ := by rfl

@[drunfold] def build_module'
    : (e : ExprLow Ident Typ) → Option (Σ T, Module Ident T)
| .base i e => do
  let mod ← ε e
  return ⟨ _, mod.2.renamePorts i ⟩
| .connect c e' => do
  let e ← e'.build_module'
  return ⟨ _, e.2.connect' c.output c.input ⟩
| .product a b => do
  let a ← a.build_module'
  let b ← b.build_module'
  return ⟨ _, a.2.product b.2 ⟩

inductive type_correct_module : ExprLow Ident Typ → Prop where
| base : ∀ i e, type_correct_module (.base i e)
| connect : ∀ o i e e',
  type_correct_module e →
  e.build_module' ε = some e' →
  (e'.2.outputs.getIO o).1 = (e'.2.inputs.getIO i).1 →
  type_correct_module (.connect { output := o, input := i } e)
| product : ∀ e₁ e₂,
  type_correct_module e₁ →
  type_correct_module e₂ →
  type_correct_module (.product e₁ e₂)

@[drunfold] def build_module_names
    : (e : ExprLow Ident Typ) → List (PortMapping Ident × Typ)
| .base i e => [(i, e)]
| .connect _ e' => e'.build_module_names
| .product a b => a.build_module_names ++ b.build_module_names

@[drunfold] def build_moduleP
    (e : ExprLow Ident Typ)
    (h : (build_module' ε e).isSome = true := by rfl)
    : Σ T, Module Ident T := e.build_module' ε |>.get h

@[drunfold] def build_module
    (e : ExprLow Ident Typ)
    : Σ T, Module Ident T := e.build_module' ε |>.getD ⟨ Unit, Module.empty _ ⟩

@[drunfold] abbrev build_module_expr
    (e : ExprLow Ident Typ)
    : Module Ident (e.build_module ε).1 := (e.build_module ε).2

@[drunfold] abbrev build_module_type
    (e : ExprLow Ident Typ)
    : Type _ := (e.build_module ε).1

notation:max "[e| " e ", " ε " ]" => build_module_expr ε e
notation:max "[T| " e ", " ε " ]" => build_module_type ε e

def wf : ExprLow Ident Typ → Bool := ExprLow.all (λ typ => (ε typ).isSome)

@[drunfold]
def locally_wf : ExprLow Ident Typ → Bool := all' (λ f _ => f.input.invertible ∧ f.output.invertible)

end ExprLowLowering

section ExprLowLemmas

variable {Ident Typ}

variable (ε : Env Ident Typ)

section DecEqIdent

variable [DecidableEq Ident]

/- For now we will ensure this structurally by filtering out keys that are not in the base module. -/
def wf_mapping : ExprLow Ident Typ → Bool
| .base inst typ =>
  match ε typ with
  | .some mod =>
    inst.input.keysList.Perm mod.2.inputs.keysList
    ∧ inst.output.keysList.Perm mod.2.outputs.keysList
    ∧ inst.input.keysList.Nodup
    ∧ inst.output.keysList.Nodup
  | .none => false
| .product e₁ e₂ => e₁.wf_mapping ∧ e₂.wf_mapping
| .connect _ e => e.wf_mapping

def well_formed : ExprLow Ident Typ → Bool
| .base inst typ =>
  match ε typ with
  | .some mod =>
    inst.input.keysList.Perm mod.2.inputs.keysList
    ∧ inst.output.keysList.Perm mod.2.outputs.keysList
    ∧ inst.input.invertible
    ∧ inst.output.invertible
  | .none => false
| .product e₁ e₂ => e₁.well_formed ∧ e₂.well_formed
| .connect _ e => e.well_formed

theorem locally_wf_product {e₁ e₂ : ExprLow Ident Typ} :
  (e₁.product e₂).locally_wf → e₁.locally_wf ∧ e₂.locally_wf := by
  simp +contextual [locally_wf, all']

variable {ε : Env Ident Typ}

theorem wf_mapping_implies_wf {e} :
  wf_mapping ε e → wf ε e := by
  induction e with
  | base map typ =>
    intro hwf
    dsimp [wf, wf_mapping, ExprLow.all] at *
    split at hwf <;> try contradiction
    grind
  | connect c e ih =>
    intro hwf
    dsimp [wf, wf_mapping, ExprLow.all] at *
    solve_by_elim
  | product e₁ e₂ ihe₁ ihe₂ =>
    intro hwf
    dsimp [wf, wf_mapping, ExprLow.all] at *
    grind

theorem well_formed_implies_wf_mapping {e} :
  well_formed ε e → wf_mapping ε e := by
  induction e with
  | base map typ =>
    intro hwf
    dsimp [wf, wf_mapping, ExprLow.all, well_formed] at *
    split at hwf <;> try contradiction
    simp_all [AssocList.invertible]
  | connect c e ih =>
    intro hwf
    dsimp [wf, wf_mapping, ExprLow.all, well_formed] at *
    solve_by_elim
  | product e₁ e₂ ihe₁ ihe₂ =>
    intro hwf
    dsimp [wf, wf_mapping, ExprLow.all, well_formed] at *
    grind

theorem well_formed_implies_wf {e} :
  well_formed ε e → wf ε e := by
  intros; solve_by_elim [wf_mapping_implies_wf, well_formed_implies_wf_mapping]

theorem well_formed_implies_wf_locally {e} :
  well_formed ε e → locally_wf e := by
  induction e with
  | base map typ =>
    intro hwf
    dsimp [wf, wf_mapping, ExprLow.all, well_formed, locally_wf, all'] at *
    split at hwf <;> try contradiction
    simp_all
  | connect c e ih =>
    intro hwf
    dsimp [wf, wf_mapping, ExprLow.all, well_formed] at *
    solve_by_elim
  | product e₁ e₂ ihe₁ ihe₂ =>
    intro hwf
    dsimp [wf, wf_mapping, ExprLow.all, well_formed, locally_wf, all'] at *
    grind

theorem well_formed_product {e₁ e₂}:
  well_formed ε (e₁.product e₂) ↔ (well_formed ε e₁ ∧ well_formed ε e₂) := by
  constructor
  · intro hwf; simp [well_formed] at hwf; assumption
  · intro hwf; simpa [well_formed]

theorem well_formed_connect {e c}:
  well_formed ε (e.connect c) ↔ well_formed ε e := by
  constructor
  · intro hwf; simp [well_formed] at hwf; assumption
  · intro hwf; simpa [well_formed]

theorem wf_builds_module {e} : wf ε e → (e.build_module' ε).isSome := by
  induction e with
  | base inst typ =>
    intro hwf; dsimp [wf, ExprLow.all] at hwf
    simp only [drunfold]
    rw [Option.isSome_iff_exists] at hwf
    simp only [Option.pure_def, Option.bind_eq_bind]; grind
  | connect _ e ih =>
    intro hwf; dsimp [wf, ExprLow.all] at hwf
    specialize ih hwf
    simp only [drunfold]; rw [Option.isSome_iff_exists] at ih; cases ih
    simp only [*]; rfl
  | product e₁ e₂ ihe₁ ihe₂ =>
    intro hwf; dsimp [wf, ExprLow.all] at hwf; rw [Bool.and_eq_true] at hwf; cases hwf; rename_i ha hb
    specialize ihe₁ ha; specialize ihe₂ hb
    simp only [drunfold]; rw [Option.isSome_iff_exists] at ihe₁ ihe₂
    cases ihe₁; cases ihe₂
    simp only [*]; rfl

theorem well_formed_builds_module {e} : well_formed ε e → (e.build_module' ε).isSome := by
  intros; apply wf_builds_module
  apply well_formed_implies_wf
  assumption

theorem build_base_in_env {T inst i mod} :
  ε i = some ⟨ T, mod ⟩ →
  build_module' ε (base inst i) = some ⟨ T, mod.renamePorts inst ⟩ := by
  intro h; dsimp [drunfold]; rw [h]; rfl

theorem build_module_unfold_1 {m r i} :
  ε i = some m →
  build_module ε (.base r i) = ⟨ m.fst, m.snd.renamePorts r ⟩ := by
  intro h; simp only [drunfold]; rw [h]; simp

theorem build_module_unfold_2 {r i} :
  ε i = none →
  build_module' ε (.base r i) = none := by
  intro h; simp only [drunfold]; rw [h]; simp

theorem mapPorts2_unfold_base {e' : ExprLow Ident Typ} {inst typ} {f g} :
  mapPorts2 f g (base inst typ) = some e' →
  e' = base {input := inst.input.mapVal (λ _ => f), output := inst.output.mapVal (λ _ => g)} typ := by
  dsimp [mapPorts2, mapInputPorts, mapOutputPorts]
  intro h
  rw [Option.bind_eq_some'] at h
  obtain ⟨a, h1, h2⟩ := h
  rw [Option.bind_eq_some'] at h1
  obtain ⟨a', h1', h2'⟩ := h1
  cases h2';
  dsimp [mapOutputPorts] at h2
  rw [Option.bind_eq_some'] at h2
  obtain ⟨a'', h1'', h2''⟩ := h2
  cases h2''; rfl

theorem mapPorts2_unfold_connect {e e' : ExprLow Ident Typ} {f g c} :
  mapPorts2 f g (connect c e) = some e' →
  ∃ e'', mapPorts2 f g e = some e'' ∧ e' = connect { output := g c.output, input := f c.input } e'' := by
  intro h
  dsimp [drunfold] at h
  cases h1 : mapInputPorts f e
  · rw [h1] at h; contradiction
  · rename_i v1; rw [h1] at h; dsimp at h
    dsimp [drunfold] at h
    cases h2 : (mapOutputPorts g v1)
    · rw [h2] at h; contradiction
    · rename_i v2; rw [h2] at h; dsimp [drunfold] at h
      cases h; simp
      unfold mapPorts2
      rw [h1]; assumption

theorem mapPorts2_unfold_product {e₁ e₂ e' : ExprLow Ident Typ} {f g} :
  mapPorts2 f g (product e₁ e₂) = some e' →
  ∃ e₁' e₂', mapPorts2 f g e₁ = some e₁' ∧ mapPorts2 f g e₂ = some e₂' ∧ e' = product e₁' e₂' := by
  intro h
  dsimp [drunfold] at h
  cases h1 : mapInputPorts f e₁ <;> rw [h1] at h <;> try contradiction
  cases h1' : mapInputPorts f e₂ <;> rw [h1'] at h <;> try contradiction
  rename_i v1 v2; dsimp [drunfold] at h
  cases h2 : mapOutputPorts g v1 <;> rw [h2] at h <;> try contradiction
  cases h2' : mapOutputPorts g v2 <;> rw [h2'] at h <;> try contradiction
  rename_i v1' v2'
  dsimp at h; cases h
  exists v1', v2'; and_intros <;> try simp [mapPorts2, *]

end DecEqIdent

variable {ε}

theorem wf_product {e₁ e₂}:
  wf ε (e₁.product e₂) ↔ (wf ε e₁ ∧ wf ε e₂) := by
  constructor <;> (intro hwf; simp [wf, ExprLow.all, Module.product] at hwf ⊢; simp [*])

theorem wf_connect {e c}:
  wf ε (e.connect c) ↔ wf ε e := by
  constructor
  · intro hwf; simp [well_formed] at hwf; assumption
  · intro hwf; simpa [well_formed]

end ExprLowLemmas

section ExprLowLemmas

variable {Ident Typ}
variable [DecidableEq Ident]
variable [DecidableEq Typ]

variable {ε : Env Ident Typ}

theorem wf_replace {e e_pat e'} : wf ε e → wf ε e' → wf ε (e.replace e_pat e') := by
  intro h wfe'; revert h
  induction e <;> (intros; simp [replace]; split <;> (try solve_by_elim) <;> simp_all [wf, ExprLow.all])

theorem wf_abstract {e e_pat a b} : wf ε e → (ε b).isSome → wf ε (e.abstract e_pat a b) := by
  unfold abstract; intros wf1 hcont
  apply wf_replace; assumption
  simp only [wf, ExprLow.all]; assumption

omit [DecidableEq Ident] in
theorem wf_modify_expression {e : ExprLow Ident Typ} {i i'}:
  (ε i').isSome →
  e.wf ε →
  (e.modify i i').wf ε := by
  induction e with
  | base inst typ =>
    intro hsome hwf
    dsimp [modify]; split <;> try assumption
  | connect con e ihe =>
    intro hsome hwf
    dsimp [modify, wf, ExprLow.all]
    solve_by_elim
  | product e₁ e₂ he₁ he₂ =>
    intro hsome hwf
    dsimp [modify, wf, ExprLow.all] at *
    simp only [Bool.and_eq_true] at *
    grind

-- TODO: Cleanup this proof.
theorem mapKey_comm2 {α} {m : PortMap Ident α} {inst : PortMap Ident (InternalPort Ident)} {f i}:
  Function.Bijective f →
  (inst.mapVal fun _ => f).invertible →
  inst.invertible →
  inst.contains i →
  (inst.mapVal fun _ => f).bijectivePortRenaming i = (f ∘ inst.bijectivePortRenaming) i := by
  intro hbij hinv1 hinv2 hcont
  unfold AssocList.bijectivePortRenaming
  rw [hinv1, hinv2]; dsimp
  rw [←AssocList.contains_find?_iff] at hcont
  obtain ⟨v, hfind⟩ := hcont
  by_cases h : i = f i
  · rw [h] at hfind ⊢
    by_cases h' : f i = v
    · subst v
      rw [AssocList.append_find_right, AssocList.append_find_right]
      rw [AssocList.filterId_correct, AssocList.filterId_correct]; rw (occs := [2]) [←h]; rfl
      simp [AssocList.invertible, List.empty_eq, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq] at hinv2
      apply hinv2.2.2
      rw [AssocList.inverse_correct]
      simp [AssocList.invertible, List.empty_eq, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq] at hinv2
      apply hinv2.2.2; assumption
      simp [AssocList.invertible, List.empty_eq, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq] at hinv1
      apply hinv1.2.2
      rw [AssocList.inverse_correct]
      simp [AssocList.invertible, List.empty_eq, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq] at hinv1
      apply hinv1.2.2
      rw [←AssocList.find?_map_comm]; rw [hfind]; simp [←h]
      rw [AssocList.filterId_correct]
      simp [AssocList.invertible, List.empty_eq, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq] at hinv2
      apply hinv2.2.1; assumption
      rw [AssocList.filterId_correct]
      simp [AssocList.invertible, List.empty_eq, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq] at hinv1
      apply hinv1.2.1
      rw [←AssocList.find?_map_comm]; rw [hfind]; simp [←h]
    · rw [AssocList.append_find_left (x := f v)]
      rw [AssocList.append_find_left (x := v)]; rfl
      rw [AssocList.filterId_correct2] <;> assumption
      rw [AssocList.filterId_correct2]; rw [←h] at h'; unfold Not at *; intro h''; apply h';
      rwa [←hbij.injective.eq_iff]
      rw [←AssocList.find?_map_comm]
      rw [hfind]; rfl
  · by_cases h' : i = v
    · subst i
      rw [AssocList.append_find_left (x := f v), AssocList.append_find_right]
      rw [AssocList.filterId_correct]; rfl
      simp [AssocList.invertible, List.empty_eq, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq] at hinv2
      apply hinv2.2.2
      rw [AssocList.inverse_correct]
      simp [AssocList.invertible, List.empty_eq, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq] at hinv2
      apply hinv2.2.2
      assumption
      rw [AssocList.filterId_correct]
      simp [AssocList.invertible, List.empty_eq, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq] at hinv2
      apply hinv2.2.1
      assumption
      rw [AssocList.filterId_correct2]; assumption
      rw [←AssocList.find?_map_comm]; rw [hfind]; rfl
    · by_cases h'' : i = f v
      · subst i
        rw [AssocList.append_find_right, AssocList.append_find_left (x := v)]
        dsimp; rw [AssocList.filterId_correct]; rfl
        simp [AssocList.invertible, List.empty_eq, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq] at hinv1
        apply hinv1.2.2
        rw [AssocList.inverse_correct]
        simp [AssocList.invertible, List.empty_eq, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq] at hinv1
        apply hinv1.2.2
        rw [←AssocList.find?_map_comm]; rw [hfind]; rfl
        rw [AssocList.filterId_correct2] <;> assumption
        rw [AssocList.filterId_correct]
        simp [AssocList.invertible, List.empty_eq, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq] at hinv1
        apply hinv1.2.1
        rw [←AssocList.find?_map_comm]; rw [hfind]; rfl
      · rw [AssocList.append_find_left (x := f v), AssocList.append_find_left (x := v)]; rfl
        rw [AssocList.filterId_correct2]; assumption; assumption
        rw [AssocList.filterId_correct2]; assumption
        rw [←AssocList.find?_map_comm]; rw [hfind]; rfl

theorem mapKey_valid_domain {α β γ} [BEq α] [LawfulBEq α] {m : AssocList α β} {f g : α → γ}:
  (∀ i, m.contains i → f i = g i) →
  m.mapKey f = m.mapKey g := by
  induction m with
  | nil => intros; rfl
  | cons k v xs ih =>
    intro h
    simp only [AssocList.mapKey, AssocList.cons.injEq, true_and]; and_intros
    · specialize h k (by simp); assumption
    · apply ih; intro k h'; apply h; simp_all

theorem mapKey_compose {α β γ δ} {m : AssocList α β} {f : α → γ} {g : γ → δ} :
  (m.mapKey f).mapKey g = m.mapKey (g ∘ f) := by
  induction m <;> simpa

/-
Pretty sure these are true based on wf_mapping.  But it also relies on the correctness of bijectivePortRenaming, that it
will actually produce the desired renamings, under the assumption that inst is an invertible map.  It is a bit strange
that the invertibility check needs to be performed twice, once inside of the bijectivePortRenaming function and once
before it to ensure that it will actually perform the renaming correctly.  However, I think this is due to one wanting
to ensure two different properties.  In many cases just having bijectiveness is useful, in others one actually has to
ensure that one is renaming correctly.
-/
theorem mapKey_comm {α} {m : PortMap Ident α} {inst : PortMap Ident (InternalPort Ident)} {f} {hbij : Function.Bijective f}:
  (inst.mapVal (fun _ => f)).invertible →
  inst.invertible →
  (∀ i, AssocList.contains i m → AssocList.contains i inst) →
  m.mapKey ((inst.mapVal fun _ => f).bijectivePortRenaming) = (m.mapKey inst.bijectivePortRenaming).mapKey f := by
  intros; rw [mapKey_valid_domain, mapKey_compose]
  intro i cont; apply mapKey_comm2 <;> solve_by_elim

theorem eraseAll_comm_inputs {S f g i} {Hinj : Function.Injective f} {m : Module Ident S}:
  AssocList.eraseAll (f i) (m.mapPorts2 f g).inputs = AssocList.mapKey f (AssocList.eraseAll i m.inputs) := by
  obtain ⟨min, mout, mint⟩ := m
  unfold Module.mapPorts2 Module.mapInputPorts Module.mapOutputPorts
  exact (AssocList.eraseAll_comm_mapKey (Hinj := Hinj))

theorem eraseAll_comm_outputs {S f g i} {Hinj : Function.Injective g} {m : Module Ident S}:
  AssocList.eraseAll (g i) (m.mapPorts2 f g).outputs = AssocList.mapKey g (AssocList.eraseAll i m.outputs) := by
  obtain ⟨min, mout, mint⟩ := m
  unfold Module.mapPorts2 Module.mapInputPorts Module.mapOutputPorts
  exact (AssocList.eraseAll_comm_mapKey (Hinj := Hinj))

theorem find?_comm_inputs {S f g i} {m : Module Ident S} (inj : Function.Injective f) :
  (AssocList.find? (f i) (m.mapPorts2 f g).inputs) = (AssocList.find? i m.inputs) := by
  obtain ⟨min, mout, mint⟩ := m
  unfold Module.mapPorts2 Module.mapInputPorts Module.mapOutputPorts
  exact AssocList.mapKey_find? inj

theorem find?_comm_outputs {S f g i} {m : Module Ident S} (inj : Function.Injective g):
  (AssocList.find? (g i) (m.mapPorts2 f g).outputs) = (AssocList.find? i m.outputs) := by
  obtain ⟨min, mout, mint⟩ := m
  unfold Module.mapPorts2 Module.mapInputPorts Module.mapOutputPorts
  exact AssocList.mapKey_find? inj

omit [DecidableEq Ident] in
theorem mapPorts2_mapKey_inputs {S} {f g} {m : Module Ident S} :
  (m.mapPorts2 f g).inputs = m.inputs.mapKey f := rfl

omit [DecidableEq Ident] in
theorem mapPorts2_mapKey_outputs {S} {f g} {m : Module Ident S} :
  (m.mapPorts2 f g).outputs = m.outputs.mapKey g := rfl

theorem keysInMap_iff {α β} [DecidableEq α] {m : AssocList α β} {k} : m.contains k ↔ k ∈ m.keysList := by
  constructor <;> intros
  · solve_by_elim [AssocList.keysInMap]
  · by_cases h' : AssocList.contains k m <;> try assumption
    have h := AssocList.keysNotInMap h'
    contradiction

omit [DecidableEq Typ] in
theorem rename_build_module_eq {e e' : ExprLow Ident Typ} {f g} (h : Function.Bijective f) (h' : Function.Bijective g) :
  e.wf_mapping ε →
  e.locally_wf →
  e.mapPorts2 f g = .some e' →
  (e'.build_module' ε) = ((e.build_module' ε).map (·.map id (fun _ y => y.mapPorts2 f g))) := by
  induction e generalizing e' with
  | base map typ =>
    intro hwf_mapping hloc heq
    cases hfind : (ε typ).isSome
    · simp [-AssocList.find?_eq] at hfind
      rw [build_module_unfold_2 hfind]
      simp [drunfold] at heq
      repeat rw [Option.bind_eq_some'] at heq
      obtain ⟨_, h1, heq⟩ := heq
      rw [Option.bind_eq_some] at h1
      obtain ⟨_, h1', heq'⟩ := h1
      cases heq'; simp [drunfold] at heq
      rw [Option.bind_eq_some] at heq
      obtain ⟨_, h1'', heq''⟩ := heq
      cases heq''
      dsimp [drunfold]; rw [hfind]; rfl
    · rw [Option.isSome_iff_exists] at hfind; obtain ⟨m, hfind⟩ := hfind
      rw [build_base_in_env hfind]
      simp [drunfold] at heq
      repeat rw [Option.bind_eq_some'] at heq
      obtain ⟨_, h1, heq⟩ := heq
      rw [Option.bind_eq_some] at h1
      obtain ⟨_, h1', heq'⟩ := h1
      cases heq'; simp [drunfold] at heq
      rw [Option.bind_eq_some] at heq
      obtain ⟨_, h1'', heq''⟩ := heq
      cases heq''
      dsimp [drunfold]; rw [hfind]; dsimp
      obtain ⟨mT, me⟩ := m
      obtain ⟨min, mout, mint⟩ := me; dsimp
      congr
      unfold Module.renamePorts
      dsimp
      unfold Module.mapPorts2
      unfold Module.mapInputPorts Module.mapOutputPorts; dsimp
      congr 1
      · rw [mapKey_comm]
        · rw [Option.guard_eq_some'] at *
          assumption
        · simp [drunfold,all'] at hloc; apply hloc.left
        · unfold wf_mapping at *; rw [hfind] at hwf_mapping; simp at hwf_mapping
          intro i hi
          rw [keysInMap_iff] at hi ⊢
          rwa [List.Perm.mem_iff hwf_mapping.left]
        · assumption
      . rw [mapKey_comm]
        · rw [Option.guard_eq_some'] at *
          assumption
        · simp [drunfold,all'] at hloc; apply hloc.right
        · unfold wf_mapping at *; rw [hfind] at hwf_mapping; simp at hwf_mapping
          intro i hi
          rw [keysInMap_iff] at hi ⊢
          rwa [List.Perm.mem_iff hwf_mapping.right.left]
        · assumption
  | connect c e ih =>
    intro hwf_mapping hloc heq
    dsimp [wf_mapping] at hwf_mapping
    cases hfind : build_module' ε e'
    · obtain ⟨e', heq', e'eq⟩ := mapPorts2_unfold_connect heq; subst_vars
      specialize ih (by assumption) (by assumption) heq'
      dsimp [drunfold] at hfind
      dsimp [drunfold]; rw [Option.bind_eq_none] at hfind
      cases h : build_module' ε e'
      · clear hfind; rw [h] at ih
        symm at ih; rw [Option.map_eq_none'] at ih
        rw [ih]; rfl
      · have := hfind _ h; contradiction
    · obtain ⟨e', heq', e'eq⟩ := mapPorts2_unfold_connect heq; subst_vars
      rename_i val
      specialize ih (by assumption) (by assumption) heq'
      symm at ih; dsimp [drunfold] at hfind; rw [Option.bind_eq_some] at hfind
      obtain ⟨val', hfind', hst⟩ := hfind; cases hst
      rw [hfind'] at ih; rw [Option.map_eq_some'] at ih; obtain ⟨m, hbuild1, hbuild2⟩ := ih
      dsimp [build_module']
      rw [hbuild1]; dsimp [Sigma.map];
      unfold Sigma.map at hbuild2; rename_i val; cases val'; cases m; dsimp at *
      cases hbuild2; congr 3
      · rewrite [eraseAll_comm_inputs (Hinj := h.injective)]; rfl
      · rewrite [eraseAll_comm_outputs (Hinj := h'.injective)]; rfl
      · rewrite [find?_comm_outputs h'.injective, find?_comm_inputs h.injective]; rfl
  | product e₁ e₂ ih₁ ih₂ =>
    intro hwf_mapping hloc heq
    dsimp [wf_mapping] at hwf_mapping; simp at hwf_mapping
    obtain ⟨e'₁, e'₂, h1, h2, h3⟩ := mapPorts2_unfold_product heq; subst_vars
    specialize ih₁ hwf_mapping.1 (locally_wf_product hloc).1 h1
    specialize ih₂ hwf_mapping.2 (locally_wf_product hloc).2 h2
    cases hfind : build_module' ε e'₁ <;> cases hfind₂ : build_module' ε e'₂
    · rw [hfind] at ih₁; rw [hfind₂] at ih₂; symm at ih₁ ih₂; rw [Option.map_eq_none'] at ih₁ ih₂
      dsimp [build_module']; rw [ih₁]; rw [hfind]; rfl
    · rw [hfind] at ih₁; symm at ih₁; rw [Option.map_eq_none'] at ih₁
      dsimp [build_module']; rw [ih₁]; rw [hfind]; rfl
    · rw [hfind] at ih₁; rw [hfind₂] at ih₂; symm at ih₁ ih₂; rw [Option.map_eq_none'] at ih₂
      rw [Option.map_eq_some'] at ih₁; obtain ⟨a, ih₁, hf⟩ := ih₁
      dsimp [build_module']; rw [hfind, hfind₂, ih₁, ih₂]; rfl
    · dsimp [build_module']; rw [hfind,hfind₂]; dsimp
      rw [hfind] at ih₁; rw [hfind₂] at ih₂; symm at ih₁ ih₂;
      rw [Option.map_eq_some'] at ih₁ ih₂
      obtain ⟨m₁, ih1₁, ih2₁⟩ := ih₁
      obtain ⟨m₂, ih1₂, ih2₂⟩ := ih₂
      rw [ih1₂,ih1₁]; dsimp
      unfold Sigma.map at ih2₁ ih2₂ ⊢; dsimp at *
      rename_i val val1; cases val; cases val1
      cases ih2₁; cases ih2₂
      dsimp [Module.product]; congr 3 <;> simp [Module.mapInputPorts, mapPorts2_mapKey_outputs, mapPorts2_mapKey_inputs,AssocList.mapVal_mapKey,AssocList.mapVal_mapKey,AssocList.mapKey_append]

theorem mapVal_keysList
  {α γ β} (f : α → β → γ) (l : AssocList α β) :
  (l.mapVal f).keysList = l.keysList := by simp [AssocList.keysList]

omit [DecidableEq Typ] in
theorem mapPorts2_well_formed {e e' : ExprLow Ident Typ} {f g} (h : Function.Bijective f) (h' : Function.Bijective g) :
  e.well_formed ε →
  e.mapPorts2 f g = .some e' →
  e'.well_formed ε := by
  induction e generalizing e' with
  | base inst typ =>
    intro hwf hmap
    dsimp [well_formed] at hwf
    split at hwf <;> try contradiction
    simp only [Bool.decide_and, Bool.decide_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hwf
    dsimp [mapPorts2, mapInputPorts] at hmap
    rw [Option.bind_eq_some] at hmap
    obtain ⟨e'', hval, hmap⟩ := hmap
    rw [Option.bind_eq_some] at hval
    obtain ⟨e''', hval', hmap'⟩ := hval
    cases hmap'
    dsimp [mapOutputPorts] at hmap; rw [Option.bind_eq_some] at hmap
    obtain ⟨e'''', hval'', hmap⟩ := hmap
    cases hmap
    dsimp [well_formed]
    rw [‹ε typ = _›]; simp
    obtain ⟨ha, hb, hc, hd⟩ := hwf;
    and_intros
    · grind [mapVal_keysList]
    · grind [mapVal_keysList]
    · simp_all
    · simp_all
  | product e₁ e₂ =>
    intro hwf hmap
    obtain ⟨e₁', e₂', hmap1, hmap2, hprod⟩ := mapPorts2_unfold_product hmap
    grind [well_formed_product]
  | connect c e =>
    intro hwf hmap
    obtain ⟨e', hconn, hconn'⟩ := mapPorts2_unfold_connect hmap
    grind [well_formed_connect]

omit [DecidableEq Typ] in
theorem mapPorts2_well_formed2 {e e' : ExprLow Ident Typ} {f g} (h : Function.Bijective f) (h' : Function.Bijective g) :
  e.locally_wf →
  e'.well_formed ε →
  e.mapPorts2 f g = .some e' →
  e.well_formed ε := by
  induction e generalizing e' with
  | base inst typ =>
    intro hloc hwf hmap
    dsimp [mapPorts2, mapInputPorts] at hmap
    rw [Option.bind_eq_some] at hmap
    obtain ⟨e'', hval, hmap⟩ := hmap
    rw [Option.bind_eq_some] at hval
    obtain ⟨e''', hval', hmap'⟩ := hval
    cases hmap'
    dsimp [mapOutputPorts] at hmap; rw [Option.bind_eq_some] at hmap
    obtain ⟨e'''', hval'', hmap⟩ := hmap
    cases hmap
    dsimp [well_formed]
    dsimp [well_formed] at hwf
    split at hwf <;> try contradiction
    dsimp [locally_wf, all'] at hloc
    simp only [Bool.decide_and, Bool.decide_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hloc hwf ⊢
    obtain ⟨ha, hb, hc, hd⟩ := hwf;
    and_intros <;> grind [mapVal_keysList]
  | product e₁ e₂ =>
    intro hloc hwf hmap
    obtain ⟨e₁', e₂', hmap1, hmap2, hprod⟩ := mapPorts2_unfold_product hmap
    dsimp [locally_wf, all'] at *
    grind [well_formed_product]
  | connect c e =>
    intro hloc hwf hmap
    obtain ⟨e', hconn, hconn'⟩ := mapPorts2_unfold_connect hmap
    dsimp [locally_wf, all'] at *
    grind [well_formed_connect]

omit [DecidableEq Typ] in
theorem refines_mapPorts2_1 {e e' f g} :
  Function.Bijective f → Function.Bijective g → e.wf_mapping ε →
  e.locally_wf →
  e.mapPorts2 f g = some e' →
  ([e| e, ε ]).mapPorts2 f g ⊑ ([e| e', ε]) := by
  unfold build_module_expr; intro hbijf hbijg hwf hloc hmapports;
  unfold build_module; rw [rename_build_module_eq (e := e) (e' := e') (g := g) (f := f)]
  any_goals assumption
  unfold Sigma.map; dsimp
  generalize h : (Option.map (fun x : TModule Ident =>
      (⟨x.fst, x.snd.mapPorts2 f g⟩ : TModule Ident)) (build_module' ε e)).getD ⟨Unit, Module.empty Unit⟩ = y
  have : (fun x : TModule Ident => (⟨x.fst, x.snd.mapPorts2 f g⟩ : TModule Ident)) ⟨Unit, Module.empty Unit⟩
    = ⟨Unit, Module.empty Unit⟩ := rfl
  rw [← this, Option.getD_map] at h; subst y
  apply Module.refines_reflexive

omit [DecidableEq Typ] in
theorem refines_mapPorts2_2 {e e' f g} :
  Function.Bijective f → Function.Bijective g → e.wf_mapping ε →
  e.locally_wf →
  e.mapPorts2 f g = some e' →
  ([e| e', ε]) ⊑ ([e| e, ε ]).mapPorts2 f g := by
  unfold build_module_expr; intro hbijf hbijg hwf hloc hmapports;
  unfold build_module; rw [rename_build_module_eq (e := e) (e' := e') (g := g) (f := f)]
  any_goals assumption
  unfold Sigma.map; dsimp
  generalize h : (Option.map (fun x : TModule Ident =>
      (⟨x.fst, x.snd.mapPorts2 f g⟩ : TModule Ident)) (build_module' ε e)).getD ⟨Unit, Module.empty Unit⟩ = y
  have : (fun x : TModule Ident => (⟨x.fst, x.snd.mapPorts2 f g⟩ : TModule Ident)) ⟨Unit, Module.empty Unit⟩
    = ⟨Unit, Module.empty Unit⟩ := rfl
  rw [← this, Option.getD_map] at h; subst y
  apply Module.refines_reflexive

omit [DecidableEq Typ] in
theorem refines_renamePorts_1 {e e' inst} :
  e.wf_mapping ε → e.locally_wf → e.renamePorts inst = some e' → ([e| e, ε ]).renamePorts inst ⊑ ([e| e', ε]) := by
  intro hwf; unfold renamePorts Module.renamePorts
  solve_by_elim [refines_mapPorts2_1, AssocList.bijectivePortRenaming_bijective]

omit [DecidableEq Typ] in
theorem refines_renamePorts_1' {e e' inst} :
  e.well_formed ε → e.renamePorts inst = some e' → ([e| e, ε ]).renamePorts inst ⊑ ([e| e', ε]) := by
  intro ha hb
  apply refines_renamePorts_1 <;> grind [well_formed_implies_wf_mapping, well_formed_implies_wf_locally]

omit [DecidableEq Typ] in
theorem refines_renamePorts_2 {e e' inst} :
  e.wf_mapping ε → e.locally_wf → e.renamePorts inst = some e' → ([e| e', ε]) ⊑ ([e| e, ε ]).renamePorts inst := by
  intro hwf; unfold renamePorts Module.renamePorts
  solve_by_elim [refines_mapPorts2_2, AssocList.bijectivePortRenaming_bijective]

omit [DecidableEq Typ] in
theorem refines_renamePorts_2' {e e' inst} :
  e.well_formed ε → e.renamePorts inst = some e' → ([e| e', ε]) ⊑ ([e| e, ε ]).renamePorts inst := by
  intro ha hb
  apply refines_renamePorts_2 <;> grind [well_formed_implies_wf_mapping, well_formed_implies_wf_locally]

omit [DecidableEq Typ] in
theorem refines_renamePorts_well_formed {e e' : ExprLow Ident Typ} {inst} :
  e.renamePorts inst = some e' → e.well_formed ε → e'.well_formed ε := by
  unfold renamePorts; intro hmap hwf
  apply mapPorts2_well_formed
  any_goals assumption
  all_goals apply AssocList.bijectivePortRenaming_bijective

end ExprLowLemmas

section Refinement

universe v w t

variable {Ident : Type w}
variable {Typ : Type t}
variable [DecidableEq Ident]

variable {S : Type v}
variable (smod : Module Ident S)

theorem refines_product {ε₁ ε₂ : Env Ident Typ} {e₁ e₂ e₁' e₂' : ExprLow Ident Typ} :
    wf ε₁ e₁ → wf ε₁ e₂ → wf ε₂ e₁' → wf ε₂ e₂' →
    [e| e₁, ε₁ ] ⊑ ([e| e₁', ε₂ ]) →
    [e| e₂, ε₁ ] ⊑ ([e| e₂', ε₂ ]) →
    [e| e₁.product e₂, ε₁ ] ⊑ ([e| e₁'.product e₂', ε₂ ]) := by
  intro wf1 wf2 wf3 wf4 ref1 ref2
  simp only [drunfold] at *
  replace wf1 := wf_builds_module wf1
  replace wf2 := wf_builds_module wf2
  replace wf3 := wf_builds_module wf3
  replace wf4 := wf_builds_module wf4
  simp only [Option.isSome_iff_exists] at *
  rcases wf1 with ⟨ m₁, wf1 ⟩
  rcases wf2 with ⟨ m₂, wf2 ⟩
  rcases wf3 with ⟨ m₁', wf3 ⟩
  rcases wf4 with ⟨ m₂', wf4 ⟩
  rw [wf1, wf2, wf3, wf4]
  rw [wf1, wf3] at ref1
  rw [wf2, wf4] at ref2
  solve_by_elim [Module.refines_product]

theorem refines_connect {ε₁ ε₂ : Env Ident Typ} {e e' c} :
    wf ε₁ e → wf ε₂ e' →
    [e| e, ε₁ ] ⊑ ([e| e', ε₂ ]) →
    [e| e.connect c, ε₁ ] ⊑ ([e| e'.connect c, ε₂ ]) := by
  intro wf1 wf2 ref
  replace wf1 := wf_builds_module wf1
  replace wf2 := wf_builds_module wf2
  simp only [Option.isSome_iff_exists] at *
  rcases wf1 with ⟨ m₁, wf1 ⟩
  rcases wf2 with ⟨ m₂, wf2 ⟩
  simp only [build_module_expr, build_module, build_module'] at *
  rw [wf1,wf2] at ref ⊢
  solve_by_elim [Module.refines_connect]

attribute [-drunfold] check_eq
variable {ε : Env Ident Typ}

theorem refines_product_associative {e₁ e₂ e₃} :
    wf ε e₁ → wf ε e₂ → wf ε e₃ →
    [e| e₁.product (e₂.product e₃), ε ] ⊑ ([e| (e₁.product e₂).product e₃, ε ]) := by
  intro wf1 wf2 wf3
  replace wf1 := wf_builds_module wf1
  replace wf2 := wf_builds_module wf2
  replace wf3 := wf_builds_module wf3
  simp only [Option.isSome_iff_exists] at *
  rcases wf1 with ⟨ m₁, wf1 ⟩
  rcases wf2 with ⟨ m₂, wf2 ⟩
  rcases wf3 with ⟨ m₃, wf3 ⟩
  simp only [build_module_expr, build_module, build_module'] at *
  rw [wf1,wf2,wf3] at ⊢
  solve_by_elim [Module.refines_product_associative]

theorem refines_product_associative' {e₁ e₂ e₃} :
    wf ε e₁ → wf ε e₂ → wf ε e₃ →
    [e| (e₁.product e₂).product e₃, ε ] ⊑ ([e| e₁.product (e₂.product e₃), ε ]) := by
  intro wf1 wf2 wf3
  replace wf1 := wf_builds_module wf1
  replace wf2 := wf_builds_module wf2
  replace wf3 := wf_builds_module wf3
  simp only [Option.isSome_iff_exists] at *
  rcases wf1 with ⟨ m₁, wf1 ⟩
  rcases wf2 with ⟨ m₂, wf2 ⟩
  rcases wf3 with ⟨ m₃, wf3 ⟩
  simp only [build_module_expr, build_module, build_module'] at *
  rw [wf1,wf2,wf3] at ⊢
  solve_by_elim [Module.refines_product_associative']

theorem findInput_iff_contains {e T m i} :
  e.well_formed ε →
  build_module' ε e = some ⟨T, m⟩ →
  findInput i e = m.inputs.contains i := by
  induction e generalizing T m i with
  | base inst typ =>
    intro hwf hbuild; dsimp [build_module'] at hbuild
    dsimp [well_formed] at hwf; split at hwf <;> try grind
    rename_i mod h
    rw [h] at hbuild; dsimp at hbuild; cases hbuild
    simp only [Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq] at hwf
    rcases hwf with ⟨hwf1, hwf2, hwf3, hwf4⟩
    simp only [AssocList.invertible, List.empty_eq, Bool.decide_and, Bool.and_eq_true,
      decide_eq_true_eq] at hwf3 hwf4
    rcases hwf3 with ⟨hwf3', hwf3, hwf3''⟩
    rcases hwf4 with ⟨hwf4', hwf4, hwf4''⟩
    by_cases h : findInput i (base inst typ) <;> symm
    · rw [h]
      dsimp [findInput] at *
      simp only [AssocList.any_eq, List.any_eq_true, decide_eq_true_eq, Prod.exists, exists_eq_right] at h
      rcases h with ⟨k, h'⟩
      have hfind := AssocList.find?_in_toList2 hwf3 h'
      have hin' : k ∈ inst.input.keysList := by
        unfold AssocList.keysList; simp [*]; solve_by_elim
      have hin : k ∈ mod.snd.inputs.keysList := by
        unfold AssocList.keysList at *; rw [← List.Perm.mem_iff] <;> assumption
      have : AssocList.bijectivePortRenaming inst.input k = i := by
        apply AssocList.bijectivePortRenaming_eq3 <;> solve | assumption | simp [*, AssocList.invertible]
      rwa [←this,←AssocList.mapKey_contains,AssocList.keysList_contains_iff]
      exact AssocList.bijectivePortRenaming_bijective.injective
    · have h' := h; simp only [Bool.not_eq_true] at h'; rw [h']; clear h'; unfold findInput at h
      simp only [AssocList.any_eq, List.any_eq_true, decide_eq_true_eq,
        Prod.exists, exists_eq_right, not_exists] at h
      suffices ¬ AssocList.contains i (mod.snd.renamePorts inst).inputs by simp only [this]
      intro hcontains
      rw [AssocList.keysList_contains_iff] at hcontains
      simp at hcontains
      unfold AssocList.keysList at hcontains
      rw [AssocList.mapKey_toList] at hcontains
      simp only [List.toList_toAssocList, List.map_map, List.mem_map, Function.comp_apply,
        Prod.exists] at hcontains
      rcases hcontains with ⟨a, b, h1, h2⟩
      subst i
      specialize h a
      apply h; clear h
      simp (disch := solve_by_elim [List.Perm.nodup]) only [AssocList.find?_in_toList_iff] at *
      have hcontains : a ∈ (AssocList.keysList inst.input) := by
        rw [List.Perm.mem_iff hwf1]
        apply AssocList.keysList_find; simp [-AssocList.find?_eq, h1]
      rw [←AssocList.keysList_contains_iff,←AssocList.contains_find?_iff] at hcontains
      obtain ⟨rv, hcontains⟩ := hcontains
      rw [AssocList.bijectivePortRenaming_eq3] <;> solve | assumption | simp [*, AssocList.invertible]
  | product e₁ e₂ he₁ he₂ =>
    intro wf hbuild
    simp only [findInput, Bool.decide_or, Bool.decide_eq_true]
    dsimp [build_module'] at hbuild
    rw [Option.bind_eq_some] at hbuild
    obtain ⟨m1, hbuild1, hrest⟩ := hbuild
    rw [Option.bind_eq_some] at hrest
    obtain ⟨m2, hbuild2, hrest⟩ := hrest
    cases hrest;
    dsimp [Module.product]
    simp only [well_formed, Bool.decide_and, Bool.decide_eq_true, Bool.and_eq_true] at wf
    rw [he₁ wf.1 hbuild1, he₂ wf.2 hbuild2]
    rw [AssocList.contains_append]
    simp only [AssocList.contains_mapval]
  | connect c e ihe =>
    intro wf hbuild
    simp only [findInput, Bool.decide_or, Bool.decide_eq_true]
    dsimp [build_module'] at hbuild
    rw [Option.bind_eq_some] at hbuild
    obtain ⟨m1, hbuild1, hrest⟩ := hbuild
    cases hrest
    dsimp [Module.connect']
    simp only [well_formed, Bool.decide_and, Bool.decide_eq_true, Bool.and_eq_true] at wf
    rw [ihe wf hbuild1]
    simp [-AssocList.find?_eq, -AssocList.contains_eq]
    rw [←AssocList.contains_eraseAll2]
    simp

theorem findOutput_iff_contains {e T m o} :
  e.well_formed ε →
  build_module' ε e = some ⟨T, m⟩ →
  findOutput o e = m.outputs.contains o := by
  induction e generalizing T m o with
  | base inst typ =>
    intro hwf hbuild; dsimp [build_module'] at hbuild
    dsimp [well_formed] at hwf; split at hwf <;> try grind
    rename_i mod h
    rw [h] at hbuild; dsimp at hbuild; cases hbuild
    simp only [Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq] at hwf
    rcases hwf with ⟨hwf1, hwf2, hwf3, hwf4⟩
    simp only [AssocList.invertible, List.empty_eq, Bool.decide_and, Bool.and_eq_true,
      decide_eq_true_eq] at hwf3 hwf4
    rcases hwf3 with ⟨hwf3', hwf3, hwf3''⟩
    rcases hwf4 with ⟨hwf4', hwf4, hwf4''⟩
    by_cases h : findOutput o (base inst typ) <;> symm
    · rw [h]
      dsimp [findOutput] at *
      simp only [AssocList.any_eq, List.any_eq_true, decide_eq_true_eq, Prod.exists, exists_eq_right] at h
      rcases h with ⟨k, h'⟩
      have hfind := AssocList.find?_in_toList2 hwf4 h'
      have hin' : k ∈ inst.output.keysList := by
        unfold AssocList.keysList; simp [*]; solve_by_elim
      have hin : k ∈ mod.snd.outputs.keysList := by
        unfold AssocList.keysList at *; rw [← List.Perm.mem_iff] <;> assumption
      have : AssocList.bijectivePortRenaming inst.output k = o := by
        apply AssocList.bijectivePortRenaming_eq3 <;> solve | assumption | simp [*, AssocList.invertible]
      rwa [←this,←AssocList.mapKey_contains,AssocList.keysList_contains_iff]
      exact AssocList.bijectivePortRenaming_bijective.injective
    · have h' := h; simp only [Bool.not_eq_true] at h'; rw [h']; clear h'; unfold findOutput at h
      simp only [AssocList.any_eq, List.any_eq_true, decide_eq_true_eq,
        Prod.exists, exists_eq_right, not_exists] at h
      suffices ¬ AssocList.contains o (mod.snd.renamePorts inst).outputs by simp only [this]
      intro hcontains
      rw [AssocList.keysList_contains_iff] at hcontains
      simp at hcontains
      unfold AssocList.keysList at hcontains
      rw [AssocList.mapKey_toList] at hcontains
      simp only [List.toList_toAssocList, List.map_map, List.mem_map, Function.comp_apply,
        Prod.exists] at hcontains
      rcases hcontains with ⟨a, b, h1, h2⟩
      subst o
      specialize h a
      apply h; clear h
      simp (disch := solve_by_elim [List.Perm.nodup]) only [AssocList.find?_in_toList_iff] at *
      have hcontains : a ∈ (AssocList.keysList inst.output) := by
        rw [List.Perm.mem_iff hwf2]
        apply AssocList.keysList_find; simp [-AssocList.find?_eq, h1]
      rw [←AssocList.keysList_contains_iff,←AssocList.contains_find?_iff] at hcontains
      obtain ⟨rv, hcontains⟩ := hcontains
      rw [AssocList.bijectivePortRenaming_eq3] <;> solve | assumption | simp [*, AssocList.invertible]
  | product e₁ e₂ he₁ he₂ =>
    intro wf hbuild
    simp only [findOutput, Bool.decide_or, Bool.decide_eq_true]
    dsimp [build_module'] at hbuild
    rw [Option.bind_eq_some] at hbuild
    obtain ⟨m1, hbuild1, hrest⟩ := hbuild
    rw [Option.bind_eq_some] at hrest
    obtain ⟨m2, hbuild2, hrest⟩ := hrest
    cases hrest;
    dsimp [Module.product]
    simp only [well_formed, Bool.decide_and, Bool.decide_eq_true, Bool.and_eq_true] at wf
    rw [he₁ wf.1 hbuild1, he₂ wf.2 hbuild2]
    rw [AssocList.contains_append]
    simp only [AssocList.contains_mapval]
  | connect c e ihe =>
    intro wf hbuild
    simp only [findOutput, Bool.decide_or, Bool.decide_eq_true]
    dsimp [build_module'] at hbuild
    rw [Option.bind_eq_some] at hbuild
    obtain ⟨m1, hbuild1, hrest⟩ := hbuild
    cases hrest
    dsimp [Module.connect']
    simp only [well_formed, Bool.decide_and, Bool.decide_eq_true, Bool.and_eq_true] at wf
    rw [ihe wf hbuild1]
    simp [-AssocList.find?_eq, -AssocList.contains_eq]
    rw [←AssocList.contains_eraseAll2]
    simp

-- TODO: more general commutativity
-- theorem refines_product_commutative {e₁ e₂} :
--     (∀ i, findInput i e₁ → ¬ findInput i e₂) →
--     (∀ i, findInput i e₂ → ¬ findInput i e₁) →
--     (∀ i, findOutput i e₁ → ¬ findOutput i e₂) →
--     (∀ i, findOutput i e₂ → ¬ findOutput i e₁) →
--     well_formed ε e₁ → well_formed ε e₂ →
--     [e| e₁.product e₂, ε ] ⊑ ([e| e₂.product e₁, ε ]) := by
--   intro hf1 hf2 hf3 hf4 wf1' wf2'
--   have wf1 := wf_builds_module (well_formed_implies_wf _ wf1')
--   have wf2 := wf_builds_module (well_formed_implies_wf _ wf2')
--   simp only [Option.isSome_iff_exists] at *
--   rcases wf1 with ⟨ m₁, wf1 ⟩
--   rcases wf2 with ⟨ m₂, wf2 ⟩
--   simp only [build_module_expr, build_module, build_module'] at *
--   rw [wf1,wf2] at ⊢
--   apply Module.refines_product_commutative
--   constructor
--   · simp [AssocList.disjoint_keys, List.inter]

theorem refines_product_commutative {inst typ inst' typ'} :
    inst_disjoint inst inst' →
    well_formed ε (base inst typ) → well_formed ε (base inst' typ') →
    [e| (base inst typ).product (base inst' typ'), ε ] ⊑ ([e| (base inst' typ').product (base inst typ), ε ]) := by
  intro disj wf1' wf2'
  have wf1 := wf_builds_module (well_formed_implies_wf wf1')
  have wf2 := wf_builds_module (well_formed_implies_wf wf2')
  simp only [Option.isSome_iff_exists] at *
  rcases wf1 with ⟨ m₁, wf1 ⟩
  rcases wf2 with ⟨ m₂, wf2 ⟩
  simp only [build_module_expr, build_module, build_module'] at *
  rw [wf1,wf2] at ⊢
  apply Module.refines_product_commutative
  dsimp at wf1 wf2
  rw [Option.bind_eq_some] at wf1 wf2
  obtain ⟨m'₁, hfind₁, heq₁⟩ := wf1
  obtain ⟨m'₂, hfind₂, heq₂⟩ := wf2
  cases heq₂; cases heq₁
  constructor
  · dsimp [well_formed] at wf1' wf2'
    rw [hfind₁] at wf1'
    rw [hfind₂] at wf2'
    simp only [Bool.decide_and, Bool.decide_eq_true, Bool.and_eq_true, decide_eq_true_eq] at wf1' wf2'
    simp only [AssocList.disjoint_keys, List.inter, Module.renamePorts_inputs,
      List.elem_eq_contains, List.contains_eq_mem, List.filter_eq_nil_iff, decide_eq_true_eq]
    intro ident hin hin'
    unfold AssocList.keysList at hin hin'
    rw [AssocList.mapKey_toList2] at hin hin'
    simp only [List.map_map, List.mem_map, Function.comp_apply, Prod.exists] at hin hin'
    obtain ⟨k, r, hin, hbij_eq⟩ := hin
    obtain ⟨k', r', hin', hbij_eq'⟩ := hin'
    subst ident
    -- have hbij_eq := AssocList.bijectivePortRenaming_bijective.injectiv
    obtain ⟨wf1₁, wf1₂, wf1₃, wf1₄⟩ := wf1'
    have wf1₃' := wf1₃
    simp only [AssocList.invertible, List.empty_eq, Bool.decide_and, Bool.and_eq_true,
      decide_eq_true_eq] at wf1₃
    obtain ⟨wf1', wf1'', wf1'''⟩ := wf1₃
    obtain ⟨wf2₁, wf2₂, wf2₃, wf2₄⟩ := wf2'
    have wf2₃' := wf2₃
    simp only [AssocList.invertible, List.empty_eq, Bool.decide_and, Bool.and_eq_true,
      decide_eq_true_eq] at wf2₃
    obtain ⟨wf2', wf2'', wf2'''⟩ := wf2₃
    have hin1' := AssocList.find?_in_toList2 (List.Perm.nodup wf1₁ wf1'') hin
    have hin2' := AssocList.find?_in_toList2 (List.Perm.nodup wf2₁ wf2'') hin'
    have hin1'' := AssocList.keysList_find?_iff.mp (by rw [hin1']; simp)
    have hin2'' := AssocList.keysList_find?_iff.mp (by rw [hin2']; simp)
    rw [List.Perm.mem_iff (wf1₁.symm), ← AssocList.keysList_find?_iff] at hin1''
    rw [List.Perm.mem_iff (wf2₁.symm), ← AssocList.keysList_find?_iff] at hin2''
    obtain ⟨v1, hin1''⟩ := hin1''
    obtain ⟨v2, hin2''⟩ := hin2''
    rw [AssocList.bijectivePortRenaming_eq3 wf1₃' hin1'', AssocList.bijectivePortRenaming_eq3 wf2₃' hin2''] at hbij_eq'
    subst v2;
    have hin1''' := AssocList.keysList_find?_iff.mp (by exists k; exact AssocList.inverse_correct wf1''' hin1'')
    have hin2''' := AssocList.keysList_find?_iff.mp (by exists k'; exact AssocList.inverse_correct wf2''' hin2'')
    rw [AssocList.inverse_keysList] at hin1''' hin2'''
    unfold inst_disjoint at disj
    simp only [Bool.decide_and, Bool.decide_eq_true, Bool.and_eq_true] at disj
    obtain ⟨hl, hr⟩ := disj
    unfold AssocList.disjoint_vals at *
    simp only [List.inter, List.elem_eq_contains, List.contains_eq_mem, List.filter_eq_nil_iff,
      decide_eq_true_eq] at hl hr
    grind
  · dsimp [well_formed] at wf1' wf2'
    rw [hfind₁] at wf1'
    rw [hfind₂] at wf2'
    simp only [Bool.decide_and, Bool.decide_eq_true, Bool.and_eq_true, decide_eq_true_eq] at wf1' wf2'
    simp only [AssocList.disjoint_keys, List.inter, Module.renamePorts_outputs,
      List.elem_eq_contains, List.contains_eq_mem, List.filter_eq_nil_iff, decide_eq_true_eq]
    intro ident hin hin'
    unfold AssocList.keysList at hin hin'
    rw [AssocList.mapKey_toList2] at hin hin'
    simp only [List.map_map, List.mem_map, Function.comp_apply, Prod.exists] at hin hin'
    obtain ⟨k, r, hin, hbij_eq⟩ := hin
    obtain ⟨k', r', hin', hbij_eq'⟩ := hin'
    subst ident
    -- have hbij_eq := AssocList.bijectivePortRenaming_bijective.injectiv
    obtain ⟨wf1₁, wf1₂, wf1₃, wf1₄⟩ := wf1'
    have wf1₄' := wf1₄
    simp only [AssocList.invertible, List.empty_eq, Bool.decide_and, Bool.and_eq_true,
      decide_eq_true_eq] at wf1₄
    obtain ⟨wf1', wf1'', wf1'''⟩ := wf1₄
    obtain ⟨wf2₁, wf2₂, wf2₃, wf2₄⟩ := wf2'
    have wf2₄' := wf2₄
    simp only [AssocList.invertible, List.empty_eq, Bool.decide_and, Bool.and_eq_true,
      decide_eq_true_eq] at wf2₄
    obtain ⟨wf2', wf2'', wf2'''⟩ := wf2₄
    have hin1' := AssocList.find?_in_toList2 (List.Perm.nodup wf1₂ wf1'') hin
    have hin2' := AssocList.find?_in_toList2 (List.Perm.nodup wf2₂ wf2'') hin'
    have hin1'' := AssocList.keysList_find?_iff.mp (by rw [hin1']; simp)
    have hin2'' := AssocList.keysList_find?_iff.mp (by rw [hin2']; simp)
    rw [List.Perm.mem_iff (wf1₂.symm), ← AssocList.keysList_find?_iff] at hin1''
    rw [List.Perm.mem_iff (wf2₂.symm), ← AssocList.keysList_find?_iff] at hin2''
    obtain ⟨v1, hin1''⟩ := hin1''
    obtain ⟨v2, hin2''⟩ := hin2''
    rw [AssocList.bijectivePortRenaming_eq3 wf1₄' hin1'', AssocList.bijectivePortRenaming_eq3 wf2₄' hin2''] at hbij_eq'
    subst v2;
    have hin1''' := AssocList.keysList_find?_iff.mp (by exists k; exact AssocList.inverse_correct wf1''' hin1'')
    have hin2''' := AssocList.keysList_find?_iff.mp (by exists k'; exact AssocList.inverse_correct wf2''' hin2'')
    rw [AssocList.inverse_keysList] at hin1''' hin2'''
    unfold inst_disjoint at disj
    simp only [Bool.decide_and, Bool.decide_eq_true, Bool.and_eq_true] at disj
    obtain ⟨hl, hr⟩ := disj
    unfold AssocList.disjoint_vals at *
    simp only [List.inter, List.elem_eq_contains, List.contains_eq_mem, List.filter_eq_nil_iff,
      decide_eq_true_eq] at hl hr
    grind

theorem wf_comm_connection'_ {e e' : ExprLow Ident Typ} {conn}:
  e.comm_connection'_ conn = .some e' →
  e.well_formed ε →
  e'.well_formed ε := by
  induction e generalizing conn e' with
  | base inst typ => grind [comm_connection'_]
  | connect c e ih =>
    dsimp [comm_connection'_]
    intro hcomm hwf
    repeat' split at hcomm <;> try grind
    · cases hcomm; assumption
    · cases hcomm; simp only [well_formed_product, well_formed_connect] at *; assumption
    · simp only [Option.map_eq_some_iff] at hcomm; obtain ⟨v, hcomm, conn⟩ := hcomm
      subst e'; simp only [well_formed_product, well_formed_connect]
      solve_by_elim
  | product e₁ e₂ ihe₁ ihe₂ =>
    dsimp [comm_connection'_]
    intro hcomm hwf
    split at hcomm <;> cases hcomm <;> simp only [well_formed_product, well_formed_connect] at *
      <;> (cases hwf; and_intros <;> solve_by_elim)

theorem wf_comm_connection'_2 {e e' : ExprLow Ident Typ} {conn}:
  e.comm_connection'_ conn = .some e' →
  e'.well_formed ε →
  e.well_formed ε := by
  induction e generalizing conn e' with
  | base inst typ => grind [comm_connection'_]
  | connect c e ih =>
    dsimp [comm_connection'_]
    intro hcomm hwf
    repeat' split at hcomm <;> try grind
    · cases hcomm; assumption
    · cases hcomm; simp only [well_formed_product, well_formed_connect] at *; assumption
    · simp only [Option.map_eq_some_iff] at hcomm; obtain ⟨v, hcomm, conn⟩ := hcomm
      subst e'; simp only [well_formed_product, well_formed_connect]
      solve_by_elim
  | product e₁ e₂ ihe₁ ihe₂ =>
    dsimp [comm_connection'_]
    intro hcomm hwf
    split at hcomm <;> cases hcomm <;> simp only [well_formed_product, well_formed_connect] at *
      <;> (cases hwf; and_intros <;> solve_by_elim)

theorem wf_comm_connection'_2' {e e' : ExprLow Ident Typ} {conn}:
  e'.well_formed ε →
  e.comm_connection'_ conn = .some e' →
  e.well_formed ε := by grind [wf_comm_connection'_2]

theorem refines_product_connect {e₁ e₂ c} :
  well_formed ε e₁ → well_formed ε e₂ →
  ¬findOutput c.output e₁ →
  ¬findInput c.input e₁ →
  [e| connect c (e₁.product e₂), ε ] ⊑ ([e| e₁.product (connect c e₂), ε ]) := by
  intro wf1 wf2 hfo hfi
  have hbuild₁ := wf_builds_module (well_formed_implies_wf wf1)
  have hbuild₂ := wf_builds_module (well_formed_implies_wf wf2)
  simp only [Option.isSome_iff_exists, Sigma.exists] at hbuild₁ hbuild₂
  obtain ⟨T₁, e₁, hbuild₁⟩ := hbuild₁
  obtain ⟨T₂, e₂, hbuild₂⟩ := hbuild₂
  simp only [build_module_expr, build_module', build_module]
  rw [hbuild₁, hbuild₂]; dsimp
  apply Module.refines_reflexive_ext
  apply Module.EqExt.symm; apply Module.comm_conn_product_EqExt
  · rw [←findOutput_iff_contains] <;> assumption
  · rw [←findInput_iff_contains] <;> assumption

theorem refines_comm_connection'_ {iexpr e' conn} :
  iexpr.well_formed ε → comm_connection'_ conn iexpr = .some e' → [e| e', ε ] ⊑ ([e| iexpr, ε ]) := by
-- Proof
  unfold build_module_expr
  induction iexpr generalizing e' with
  | base inst typ => grind [comm_connection'_]
  | product e₁ e₂ ihe₁ ihe₂ =>
    intro hwell_formed hcomm
    have hwf := well_formed_implies_wf hwell_formed
    have ⟨hwell_formed2, hwell_formed3⟩ := well_formed_product.mp hwell_formed
    have e₁wf : e₁.wf ε := by simp [ExprLow.all, wf] at hwf ⊢; simp [hwf]
    have e₂wf : e₂.wf ε := by simp [ExprLow.all, wf] at hwf ⊢; simp [hwf]
    dsimp [comm_connection'_] at hcomm
    split at hcomm
    · cases hcomm; apply ExprLow.refines_product <;> try solve_by_elim [wf_comm_connection'_, well_formed_implies_wf]
    · cases hcomm; apply ExprLow.refines_product <;> try solve_by_elim [wf_comm_connection'_, Module.refines_reflexive, well_formed_implies_wf]
    · cases hcomm; apply ExprLow.refines_product <;> try solve_by_elim [wf_comm_connection'_, Module.refines_reflexive, well_formed_implies_wf]
    · cases hcomm
  | connect c e ih =>
    intro hwell_formed hcomm
    have hwf := well_formed_implies_wf hwell_formed
    have hwell_formed2 := well_formed_connect.mp hwell_formed
    dsimp [comm_connection'_] at hcomm
    split at hcomm
    · split at hcomm <;> try contradiction
      · (split at hcomm <;> try contradiction); cases hcomm
        dsimp [build_module, build_module']
        simp [wf, ExprLow.all, -AssocList.contains_eq] at hwf
        have hbuild_module₁ := wf_builds_module hwf
        simp [Option.isSome_iff_exists ] at hbuild_module₁
        obtain ⟨T₁, e₁, hbuild₁⟩ := hbuild_module₁
        rw [hbuild₁]; dsimp
        apply Module.refines_reflexive_ext
        repeat cases ‹_ ∧ _›; subst_vars
        apply Module.comm_conn_conn_EqExt <;> (symm; assumption)
      · (repeat' (split at hcomm <;> try contradiction)); cases hcomm
        have ⟨hwell_formed3, hwell_formed4⟩ := well_formed_product.mp hwell_formed2
        dsimp [build_module, build_module']
        simp [wf, ExprLow.all, -AssocList.contains_eq] at hwf; obtain ⟨hwfl, hwfr⟩ := hwf
        have hbuild_module₁ := wf_builds_module hwfl
        have hbuild_module₂ := wf_builds_module hwfr
        simp [Option.isSome_iff_exists ] at hbuild_module₁ hbuild_module₂
        obtain ⟨T₁, e₁, hbuild₁⟩ := hbuild_module₁
        obtain ⟨T₂, e₂, hbuild₂⟩ := hbuild_module₂
        rw [hbuild₁]; rw [hbuild₂]; dsimp
        rename_i hfi
        apply Module.refines_reflexive_ext
        apply Module.comm_conn_product_EqExt
        · rw [←findOutput_iff_contains] <;> solve_by_elim [hfi.2.1]
        · rw [←findInput_iff_contains] <;> solve_by_elim [hfi.1]
    · simp at hcomm; obtain ⟨e'', hcomm, hconn⟩ := hcomm; subst e'
      apply ExprLow.refines_connect <;> solve_by_elim [wf_comm_connection'_, well_formed_implies_wf]

theorem refines_comm_connection'_2 {iexpr e' conn} :
    iexpr.well_formed ε → comm_connection'_ conn iexpr = .some e' → [e| iexpr, ε ] ⊑ [e| e', ε ] := by
-- Proof
  unfold build_module_expr
  induction iexpr generalizing e' with
  | base inst typ => intro hwf₁ hcomm; contradiction
  | product e₁ e₂ ihe₁ ihe₂ =>
    intro hwell_formed hcomm
    have hwf := well_formed_implies_wf hwell_formed
    have ⟨hwell_formed2, hwell_formed3⟩ := well_formed_product.mp hwell_formed
    have e₁wf : e₁.wf ε := by simp [ExprLow.all, wf] at hwf ⊢; simp [hwf]
    have e₂wf : e₂.wf ε := by simp [ExprLow.all, wf] at hwf ⊢; simp [hwf]
    dsimp [comm_connection'_] at hcomm
    split at hcomm
    · cases hcomm; apply ExprLow.refines_product <;> try solve_by_elim [wf_comm_connection'_, well_formed_implies_wf]
    · cases hcomm; apply ExprLow.refines_product <;> try solve_by_elim [wf_comm_connection'_, Module.refines_reflexive, well_formed_implies_wf]
    · cases hcomm; apply ExprLow.refines_product <;> try solve_by_elim [wf_comm_connection'_, Module.refines_reflexive, well_formed_implies_wf]
    · cases hcomm
  | connect c e ih =>
    intro hwell_formed hcomm
    have hwf := well_formed_implies_wf hwell_formed
    have hwell_formed2 := well_formed_connect.mp hwell_formed
    dsimp [comm_connection'_] at hcomm
    split at hcomm
    · split at hcomm <;> try contradiction
      · (split at hcomm <;> try contradiction); cases hcomm
        dsimp [build_module, build_module']
        simp [wf, ExprLow.all, -AssocList.contains_eq] at hwf
        have hbuild_module₁ := wf_builds_module hwf
        simp [Option.isSome_iff_exists ] at hbuild_module₁
        obtain ⟨T₁, e₁, hbuild₁⟩ := hbuild_module₁
        rw [hbuild₁]; dsimp
        apply Module.refines_reflexive_ext
        repeat cases ‹_ ∧ _›; subst_vars
        apply Module.comm_conn_conn_EqExt <;> assumption
      · (repeat' (split at hcomm <;> try contradiction)); cases hcomm
        have ⟨hwell_formed3, hwell_formed4⟩ := well_formed_product.mp hwell_formed2
        dsimp [build_module, build_module']
        simp [wf, ExprLow.all, -AssocList.contains_eq] at hwf; obtain ⟨hwfl, hwfr⟩ := hwf
        have hbuild_module₁ := wf_builds_module hwfl
        have hbuild_module₂ := wf_builds_module hwfr
        simp [Option.isSome_iff_exists ] at hbuild_module₁ hbuild_module₂
        obtain ⟨T₁, e₁, hbuild₁⟩ := hbuild_module₁
        obtain ⟨T₂, e₂, hbuild₂⟩ := hbuild_module₂
        rw [hbuild₁]; rw [hbuild₂]; dsimp
        rename_i hfi
        apply Module.refines_reflexive_ext
        apply Module.EqExt.symm
        apply Module.comm_conn_product_EqExt
        · rw [←findOutput_iff_contains] <;> solve_by_elim [hfi.2.1]
        · rw [←findInput_iff_contains] <;> solve_by_elim [hfi.1]
    · simp at hcomm; obtain ⟨e'', hcomm, hconn⟩ := hcomm; subst e'
      apply ExprLow.refines_connect <;> solve_by_elim [wf_comm_connection'_, well_formed_implies_wf]

variable {wfc : ExprLow Ident Typ → Prop}

theorem refines_fix_point_opt {iexpr e' f n} :
    (∀ e e', wfc e → f e = .some e' → ([e| e', ε ] ⊑ ([e| e, ε ])) ∧ wfc e') →
    [e| e', ε ] ⊑ ([e| iexpr, ε ]) →
    wfc e' →
    [e| fix_point_opt f e' n , ε ] ⊑ ([e| iexpr, ε ]) := by
-- Proof
  induction n generalizing iexpr e' with
  | zero => intros; simp [fix_point_opt]; assumption
  | succ n ih =>
    intro h href hwf
    dsimp [fix_point_opt]
    split <;> simp
    · have hrand := h _ _ ‹_› ‹_›; apply ih; assumption; apply Module.refines_transitive
      apply hrand.1; solve_by_elim; apply hrand.2
    · assumption

theorem refines_fix_point_opt2' {iexpr e' f n} :
    (∀ e e', wfc e → f e = .some e' → ([e| e, ε ] ⊑ ([e| e', ε ])) ∧ wfc e') →
    [e| iexpr, ε ] ⊑ ([e| e', ε ]) →
    wfc e' →
    [e| iexpr, ε ] ⊑ ([e| fix_point_opt f e' n, ε ]) := by
-- Proof
  induction n generalizing iexpr e' with
  | zero => intros; simp [fix_point_opt]; assumption
  | succ n ih =>
    intro h href hwf
    dsimp [fix_point_opt]
    split <;> simp
    · have hrand := h _ _ ‹_› ‹_›; apply ih; assumption; apply Module.refines_transitive
      assumption; apply hrand.1; apply hrand.2
    · assumption

omit [DecidableEq Ident] in
theorem wf_fix_point_opt {iexpr f n} :
    (∀ e e', wfc e → f e = .some e' → wfc e') →
    wfc iexpr →
    wfc (fix_point_opt f iexpr n) := by
-- Proof
  induction n generalizing iexpr with
  | zero => intros; simp [fix_point_opt]; assumption
  | succ n ih =>
    intro h hwf
    dsimp [fix_point_opt]
    split <;> solve_by_elim

variable [DecidableEq Typ]

theorem check_eq_symm {iexpr iexpr' : ExprLow Ident Typ} :
  iexpr.check_eq iexpr' → iexpr'.check_eq iexpr := by
  induction iexpr generalizing iexpr' <;> unfold check_eq <;> cases iexpr' <;> intro heq
  any_goals contradiction
  · simp_all; and_intros <;> (apply AssocList.EqExt.symm; simp only [*])
  · grind
  · grind

theorem check_eq_wf {iexpr iexpr' : ExprLow Ident Typ} :
  iexpr.check_eq iexpr' →
  iexpr.wf ε → iexpr'.wf ε := by
  induction iexpr generalizing iexpr' with
  | base typ inst =>
    intro ih wf
    cases iexpr' <;> try grind [ExprLow.check_eq]
    simp only [check_eq, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq] at ih
    dsimp [ExprLow.wf, ExprLow.all] at *
    cases ih; subst_vars; assumption
  | product e₁ e₂ he₁ he₂ =>
    intro ih wf
    cases iexpr' <;> try grind [ExprLow.check_eq]
    dsimp [ExprLow.check_eq] at ih
    dsimp [ExprLow.wf, ExprLow.all] at *; simp only [Bool.and_eq_true] at wf ⊢
    simp only [Bool.decide_and, Bool.decide_eq_true, Bool.and_eq_true] at ih
    cases ih; cases wf; and_intros <;> solve_by_elim
  | connect c e he =>
    intro ih wf
    cases iexpr' <;> try grind [ExprLow.check_eq]
    dsimp [ExprLow.check_eq] at ih
    dsimp [ExprLow.wf, ExprLow.all] at *
    simp only [Bool.decide_and, Bool.decide_eq_true, Bool.and_eq_true] at ih
    cases ih; and_intros <;> solve_by_elim

theorem check_eq_well_formed {iexpr iexpr' : ExprLow Ident Typ} :
  iexpr.check_eq iexpr' →
  iexpr.well_formed ε → iexpr'.well_formed ε := by
  induction iexpr generalizing iexpr' with
  | base typ inst =>
    intro ih wf
    cases iexpr' <;> try grind [ExprLow.check_eq]
    simp only [check_eq, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq] at ih
    dsimp [ExprLow.well_formed, ExprLow.all] at *
    split at wf <;> try contradiction
    cases ih; subst_vars; rename_i htmp; rw [htmp]; simp at *
    repeat with_reducible cases ‹_ ∧ _›
    and_intros
    · apply List.Perm.trans <;> try assumption
      apply List.Perm.map
      solve_by_elim [AssocList.EqExt_Perm]
    · apply List.Perm.trans <;> try assumption
      apply List.Perm.map
      solve_by_elim [AssocList.EqExt_Perm]
    · apply AssocList.EqExt_invertible
      apply AssocList.EqExt.symm
      all_goals assumption
    · apply AssocList.EqExt_invertible
      apply AssocList.EqExt.symm
      all_goals assumption
  | product e₁ e₂ he₁ he₂ =>
    intro ih wf
    cases iexpr' <;> try grind [ExprLow.check_eq]
    dsimp [ExprLow.check_eq] at ih
    simp [well_formed_product] at *;
    cases ih; cases wf; and_intros <;> solve_by_elim
  | connect c e he =>
    intro ih wf
    cases iexpr' <;> try grind [ExprLow.check_eq]
    dsimp [ExprLow.check_eq] at ih
    simp [well_formed_connect] at *;
    cases ih; and_intros <;> solve_by_elim

theorem check_eq_refines {iexpr iexpr'} :
  iexpr.check_eq iexpr' → iexpr.wf ε →
  [e| iexpr, ε ] ⊑ ([e| iexpr', ε ]) := by
  revert iexpr'
  induction iexpr with
  | base inst typ =>
    intro iexpr' heq hwf
    cases iexpr' <;> try contradiction
    rename_i map' typ'
    unfold check_eq at heq; simp at heq
    obtain ⟨typeq, heq1, heq2, hnodup1, hnodup2, hnodup3, hnodup4⟩ := heq
    dsimp [drunfold]
    subst typ'
    cases h: ε typ with
    | none =>
      apply Module.refines_reflexive
    | some mod =>
      dsimp; rw (occs := .pos [2]) [Module.renamePorts_EqExt (p' := inst)]
      apply Module.refines_reflexive
      any_goals (unfold PortMapping.wf; solve_by_elim)
      cases map'; cases inst; solve_by_elim
  | product e₁ e₂ ih₁ ih₂ =>
    intro iexpr' heq hwf
    have hwf' := check_eq_wf ‹_› ‹_›
    cases iexpr' <;> try contradiction
    rename_i e₁' e₂'
    apply refines_product
    any_goals (unfold wf ExprLow.all at hwf hwf'; unfold wf; grind)
    apply ih₁; dsimp [check_eq] at heq; grind
    unfold wf ExprLow.all at hwf hwf'; unfold wf; grind
    apply ih₂; dsimp [check_eq] at heq; grind
    unfold wf ExprLow.all at hwf hwf'; unfold wf; grind
  | connect c e ih =>
    intro iexpr' heq hwf
    have hwf' := check_eq_wf ‹_› ‹_›
    cases iexpr' <;> try contradiction
    rename_i c' e'
    dsimp [check_eq] at heq; simp at heq
    repeat cases ‹_ ∧ _›; subst_vars
    apply refines_connect
    any_goals (unfold wf ExprLow.all at hwf hwf'; unfold wf; solve_by_elim)
    solve_by_elim

theorem check_eq_refines2 {iexpr iexpr'} :
  iexpr.check_eq iexpr' → iexpr.wf ε →
  [e| iexpr', ε ] ⊑ ([e| iexpr, ε ]) := by
  intro hcheck hwf
  have t1 := check_eq_symm hcheck
  have t2 := check_eq_wf hcheck hwf
  solve_by_elim [check_eq_refines]

theorem abstract_refines {iexpr expr_pat i} :
    ε i = some ⟨ _, [e| expr_pat, ε ] ⟩ →
    iexpr.wf ε →
    [e| iexpr, ε ] ⊑ ([e| iexpr.abstract expr_pat ∅ i, ε ]) := by
  unfold build_module_expr; intro hfind;
  induction iexpr with
  | base inst typ =>
    intro hwf
    dsimp [drunfold, Option.bind, Option.getD] at *
    by_cases h : (ExprLow.base inst typ).check_eq expr_pat
    · rw [h];
      dsimp
      simp [drunfold, Option.bind]
      rw [hfind]; simp
      have : ∃ m, ε typ = some m := by
        simp only [wf, ExprLow.all] at hwf
        simp only [←Option.isSome_iff_exists, Batteries.AssocList.contains_some, hwf]
      let ⟨ m, hb ⟩ := this; clear this; rw [hb]; simp
      cases expr_pat <;> simp [check_eq] at h
      let ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h; clear h
      subst_vars
      dsimp [drunfold, Option.bind] at *
      rw [hb] at hfind ⊢; simp [-AssocList.find?_eq] at *
      rw [Module.renamePorts_empty]
      rename_i m _; cases m
      rw (occs := .pos [2]) [Module.renamePorts_EqExt (p' := inst)]
      · apply Module.refines_reflexive
      · unfold PortMapping.wf AssocList.wf; simp only [*, and_self]
      · unfold PortMapping.wf AssocList.wf; simp only [*, and_self]
      · cases inst; constructor <;> simp only [*]
    · have : (if (base inst typ).check_eq expr_pat = true then base ∅ i else base inst typ) = base inst typ := by
        simp [h]
      rw [this]; clear this
      have : ∃ m, ε typ = some m := by
        simp only [wf, ExprLow.all] at hwf
        simp only [←Option.isSome_iff_exists, Batteries.AssocList.contains_some, hwf]
      cases this; rename_i a ha
      dsimp [drunfold]; rw [ha]; simp [Module.refines_reflexive]
  | product e₁ e₂ ihe₁ ihe₂ =>
    simp [abstract, replace]
    intro hwf
    by_cases h : (e₁.product e₂).check_eq expr_pat
    · subst_vars
      simp only [wf,ExprLow.all,Bool.and_eq_true] at hwf; obtain ⟨hwf1, hwf2⟩ := hwf
      specialize ihe₁ hwf1; specialize ihe₂ hwf2
      rw [h]; dsimp; rw [build_module_unfold_1 hfind]; dsimp
      apply Module.refines_transitive (imod' := (build_module ε expr_pat).snd)
      · apply check_eq_refines; assumption; unfold wf ExprLow.all; grind
      · rw [Module.renamePorts_empty]; apply Module.refines_reflexive
    · unfold abstract at ihe₁ ihe₂
      have : wf ε (e₁.replace expr_pat (base ∅ i)) := by
        apply wf_abstract; simp_all [wf, ExprLow.all]
        grind
      have : wf ε (e₂.replace expr_pat (base ∅ i)) := by
        apply wf_abstract; simp_all [wf, ExprLow.all]
        grind
      have : wf ε e₁ := by simp_all [wf, ExprLow.all]
      have : wf ε e₂ := by simp_all [wf, ExprLow.all]
      simp at h; rw [h]; dsimp
      apply refines_product <;> (try assumption)
      <;> [apply ihe₁ ; apply ihe₂] <;> simp_all [wf, ExprLow.all]
  | connect c e ih =>
    simp [abstract, replace]
    intro hwf
    by_cases h : (connect c e).check_eq expr_pat
    · subst_vars
      simp only [wf,ExprLow.all,Bool.and_eq_true] at hwf
      specialize ih hwf
      rw [h]; dsimp; rw [build_module_unfold_1 hfind]; dsimp
      apply Module.refines_transitive (imod' := (build_module ε expr_pat).snd)
      · apply check_eq_refines; assumption; unfold wf ExprLow.all; grind
      · rw [Module.renamePorts_empty]; apply Module.refines_reflexive
    · have : wf ε (connect c (e.replace expr_pat (base ∅ i))) := by
        simp [wf, ExprLow.all]
        convert_to wf ε (e.replace expr_pat (base ∅ i));
        simp [wf, ExprLow.all]
        apply wf_replace; assumption; simp only [wf, ExprLow.all]
        grind
      simp at h; rw [h]; solve_by_elim [refines_connect]

theorem abstract_refines2 {iexpr expr_pat i} :
    ε i = some ⟨ _, [e| expr_pat, ε ] ⟩ →
    iexpr.wf ε →
    [e| iexpr.abstract expr_pat ∅ i, ε ] ⊑ ([e| iexpr, ε ]) := by
  unfold build_module_expr; intro hfind;
  induction iexpr with
  | base inst typ =>
    intro hwf
    dsimp [drunfold, Option.bind, Option.getD] at *
    by_cases h : (ExprLow.base inst typ).check_eq expr_pat
    · rw [h];
      dsimp
      simp [drunfold, Option.bind]
      rw [hfind]; simp
      have : ∃ m, ε typ = some m := by
        simp only [wf, ExprLow.all] at hwf
        simp only [←Option.isSome_iff_exists, Batteries.AssocList.contains_some, hwf]
      let ⟨ m, hb ⟩ := this; clear this; rw [hb]; simp
      cases expr_pat <;> simp [check_eq] at h
      let ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h; clear h
      subst_vars
      dsimp [drunfold, Option.bind] at *
      rw [hb] at hfind ⊢; simp [-AssocList.find?_eq] at *
      rw [Module.renamePorts_empty]
      rename_i m _; cases m
      rw (occs := .pos [1]) [Module.renamePorts_EqExt (p' := inst)]
      · apply Module.refines_reflexive
      · unfold PortMapping.wf AssocList.wf; simp only [*, and_self]
      · unfold PortMapping.wf AssocList.wf; simp only [*, and_self]
      · cases inst; constructor <;> simp only [*]
    · have : (if (base inst typ).check_eq expr_pat = true then base ∅ i else base inst typ) = base inst typ := by
        simp [h]
      rw [this]; clear this
      have : ∃ m, ε typ = some m := by
        simp only [wf, ExprLow.all] at hwf
        simp only [←Option.isSome_iff_exists, Batteries.AssocList.contains_some, hwf]
      cases this; rename_i a ha
      dsimp [drunfold]; rw [ha]; simp [Module.refines_reflexive]
  | product e₁ e₂ ihe₁ ihe₂ =>
    simp [abstract, replace]
    intro hwf
    by_cases h : (e₁.product e₂).check_eq expr_pat
    · subst_vars
      simp only [wf,ExprLow.all,Bool.and_eq_true] at hwf; obtain ⟨hwf1, hwf2⟩ := hwf
      specialize ihe₁ hwf1; specialize ihe₂ hwf2
      rw [h]; dsimp; rw [build_module_unfold_1 hfind]; dsimp
      apply Module.refines_transitive (imod' := (build_module ε expr_pat).snd)
      · rw [Module.renamePorts_empty]; apply Module.refines_reflexive
      · apply check_eq_refines; apply check_eq_symm; assumption
        apply check_eq_wf; assumption; unfold wf ExprLow.all; grind
    · unfold abstract at ihe₁ ihe₂
      have : wf ε (e₁.replace expr_pat (base ∅ i)) := by
        apply wf_abstract; simp_all [wf, ExprLow.all]
        grind
      have : wf ε (e₂.replace expr_pat (base ∅ i)) := by
        apply wf_abstract; simp_all [wf, ExprLow.all]
        grind
      have : wf ε e₁ := by simp_all [wf, ExprLow.all]
      have : wf ε e₂ := by simp_all [wf, ExprLow.all]
      simp at h; rw [h]; dsimp
      apply refines_product <;> (try assumption)
      <;> [apply ihe₁ ; apply ihe₂] <;> simp_all [wf, ExprLow.all]
  | connect c e ih =>
    simp [abstract, replace]
    intro hwf
    by_cases h : (connect c e).check_eq expr_pat
    · subst_vars
      simp only [wf,ExprLow.all,Bool.and_eq_true] at hwf
      specialize ih hwf
      rw [h]; dsimp; rw [build_module_unfold_1 hfind]; dsimp
      apply Module.refines_transitive (imod' := (build_module ε expr_pat).snd)
      · rw [Module.renamePorts_empty]; apply Module.refines_reflexive
      · apply check_eq_refines; apply check_eq_symm; assumption
        apply check_eq_wf; assumption; unfold wf ExprLow.all; grind
    · have : wf ε (connect c (e.replace expr_pat (base ∅ i))) := by
        simp [wf, ExprLow.all]
        convert_to wf ε (e.replace expr_pat (base ∅ i));
        simp [wf, ExprLow.all]
        apply wf_replace; assumption; simp only [wf, ExprLow.all]
        grind
      simp at h; rw [h]; solve_by_elim [refines_connect]

theorem replacement {iexpr e_new e_pat} :
    iexpr.wf ε → e_new.wf ε →
    [e| e_new, ε ] ⊑ ([e| e_pat, ε ]) →
    [e| iexpr.replace e_pat e_new, ε ] ⊑ ([e| iexpr, ε ]) := by
  unfold build_module_expr
  induction iexpr with
  | base inst typ =>
    intro hwf₁ hwf₂ Href
    by_cases h : (base inst typ).check_eq e_pat
    · dsimp [ExprLow.replace]; rw [h]; dsimp [wf, ExprLow.all] at hwf₁
      apply Module.refines_transitive _ Href
      solve_by_elim [check_eq_refines2]
    · simp at h; dsimp [ExprLow.replace]; rw [h]
      solve_by_elim [Module.refines_reflexive]
  | product e₁ e₂ ihe₁ ihe₂ =>
    intro hwf hf₁ href
    have e₁wf : e₁.wf ε := by simp [ExprLow.all, wf] at hwf ⊢; simp [hwf]
    have e₂wf : e₂.wf ε := by simp [ExprLow.all, wf] at hwf ⊢; simp [hwf]
    dsimp [replace]
    by_cases h : (e₁.product e₂).check_eq e_pat
    · rw [h]; dsimp
      apply Module.refines_transitive _ href
      solve_by_elim [check_eq_refines2]
    · simp at h; rw [h]
      apply refines_product <;> solve_by_elim [wf_modify_expression,wf_replace]
  | connect c e =>
    intro hwf hfind₁ href
    dsimp only [replace]
    have e₁wf : e.wf ε := by simp [ExprLow.all, wf] at hwf ⊢; simp [hwf]
    by_cases h : (connect c e).check_eq e_pat
    · rw [h]; dsimp
      apply Module.refines_transitive _ href
      solve_by_elim [check_eq_refines2]
    · simp at h; rw [h]
      apply refines_connect <;> solve_by_elim [wf_modify_expression,wf_replace]

theorem replacement_well_formed {iexpr e_new e_pat : ExprLow Ident Typ} :
    iexpr.well_formed ε → e_new.well_formed ε →
    (iexpr.replace e_pat e_new).well_formed ε := by
  induction iexpr with
  | base inst typ =>
    intro hwf₁ hwf₂
    by_cases h : (base inst typ).check_eq e_pat
    · dsimp [well_formed] at *;
      split at hwf₁ <;> try contradiction
      simp [replace, h]; assumption
    · simp at h; dsimp [ExprLow.replace]; rw [h]
      assumption
  | product e₁ e₂ ihe₁ ihe₂ =>
    intro hwf hwf₂
    have ⟨hwf1, hwf2⟩ := well_formed_product.mp hwf
    dsimp [replace]
    grind [well_formed_product]
  | connect c e =>
    intro hwf hwf₂
    obtain hwf := well_formed_connect.mp hwf
    dsimp [replace]
    grind [well_formed_connect]

theorem wf_comm_base_ {e e' : ExprLow Ident Typ} {inst typ}:
  e.comm_base_ inst typ = .some e' →
  e.well_formed ε →
  e'.well_formed ε := by
  induction e generalizing e' inst typ with
  | base inst typ => grind [comm_base_]
  | connect c e ih =>
    dsimp [comm_base_]
    intro hcomm hwf
    repeat' split at hcomm <;> try grind
    simp only [Option.map_eq_some_iff] at hcomm
    obtain ⟨v, hcomm, hother⟩ := hcomm
    subst e'; simp only [well_formed_product, well_formed_connect] at *
    solve_by_elim
  | product e₁ e₂ he₁ he₂ =>
    dsimp [comm_base_]
    intro hcomm hwf
    (repeat' split at hcomm) <;> (try cases hcomm) <;> simp only [well_formed_product, well_formed_connect] at *
      <;> (try solve | (repeat cases ‹_ ∧ _›); and_intros <;> solve_by_elim)
    simp only [Option.map_eq_some_iff] at hcomm
    obtain ⟨v, hcomm, hprod⟩ := hcomm; subst e'
    simp only [well_formed_product, well_formed_connect] at *
    cases hwf; and_intros <;> solve_by_elim

theorem refines_comm_base_ {iexpr e' inst typ} :
  iexpr.well_formed ε → comm_base_ inst typ iexpr = .some e' → [e| e', ε ] ⊑ ([e| iexpr, ε ]) := by
  induction iexpr generalizing e' inst typ with
  | base inst' typ' => grind [comm_base_]
  | connect c e ih =>
    intro hwf hcomm
    dsimp [comm_base_] at hcomm
    simp only [Option.map_eq_some_iff] at hcomm
    obtain ⟨v, hcomm, heq⟩ := hcomm; subst e'
    apply refines_connect <;> solve_by_elim [well_formed_implies_wf, wf_comm_base_]
  | product e₁ e₂ ihe₁ ihe₂ =>
    intro hwf hcomm
    dsimp [comm_base_] at hcomm
    repeat' split at hcomm <;> (try contradiction) <;> (try cases hcomm)
    · subst e₁; rw [well_formed_product, well_formed_product] at hwf
      obtain ⟨wf1, wf2, wf3⟩ := hwf
      have hwf1 := well_formed_implies_wf wf1
      have hwf2 := well_formed_implies_wf wf2
      have hwf3 := well_formed_implies_wf wf3
      apply Module.refines_transitive
      apply refines_product_associative <;> assumption
      apply Module.refines_transitive
      rotate_left 1
      apply refines_product_associative' <;> assumption
      apply refines_product; rw [wf_product]; simp [*]; assumption; rw [wf_product]; simp [*]; assumption
      apply refines_product_commutative <;> assumption
      apply Module.refines_reflexive
    · subst e₁; simp only [well_formed_product, well_formed_connect] at *; apply refines_product_connect
      · apply hwf.1
      · apply hwf.2
      · dsimp [findOutput]
        intro hany
        rename_i h; apply h.1
        dsimp [AssocList.valsList]; simp_all
      · dsimp [findInput]
        intro hany
        rename_i h; apply h.2
        dsimp [AssocList.valsList]; simp_all
    · rw [well_formed_product] at hwf; cases hwf
      subst e₁; apply refines_product_commutative <;> assumption
    · simp only [Option.map_eq_some_iff] at hcomm
      obtain ⟨v, hcomm, heq⟩ := hcomm
      simp only [well_formed_product, well_formed_connect] at *; cases hwf
      subst e'; apply refines_product <;> solve_by_elim [well_formed_implies_wf, wf_comm_base_, Module.refines_reflexive]

omit [DecidableEq Typ] in
theorem build_module_build_module_interface {e : ExprLow Ident Typ} {mod} :
  e.build_module' ε = some mod → e.build_module_interface ε = some mod.2.toModuleInterface := by
  induction e generalizing mod with
  | base inst typ =>
    intro hbuild
    dsimp [build_module'] at hbuild
    simp only [Option.bind_eq_some_iff] at hbuild
    obtain ⟨_, _, _⟩ := hbuild
    simp [*, build_module_interface]
    cases ‹some _ = some _›; rfl
  | connect c e ihe =>
    intro hbuild; dsimp [build_module'] at hbuild
    obtain ⟨mod', hbuild', heq⟩ := Option.bind_eq_some_iff.mp hbuild; cases heq
    rw [hbuild'] at hbuild; dsimp at hbuild;
    dsimp [build_module_interface]; rw [ihe] <;> try assumption
    dsimp [Module.toModuleInterface, Module.connect']
    grind [AssocList.eraseAll_map_comm]
  | product e1 e2 he1 he2 =>
    intro hbuild; dsimp [build_module', build_module_interface] at hbuild ⊢
    obtain ⟨a1, hbuild1, hbuild⟩ := Option.bind_eq_some_iff.mp hbuild
    obtain ⟨a2, hbuild2, heq⟩ := Option.bind_eq_some_iff.mp hbuild; cases heq
    rw [he1, he2] <;> try assumption
    dsimp [Module.product, Module.toModuleInterface]
    unfold Module.liftL Module.liftR; dsimp
    simp only [←AssocList.mapVal_append, AssocList.mapVal_mapVal]

omit [DecidableEq Typ] in
theorem build_module_build_module_interface' {e : ExprLow Ident Typ} {mi} :
  e.build_module_interface ε = some mi → ∃ mod, e.build_module' ε = some mod ∧ mi = mod.2.toModuleInterface := by
  induction e generalizing mi with
  | base inst typ =>
    intro hbuild
    dsimp [build_module', build_module_interface] at hbuild ⊢
    simp only [Option.map_eq_some_iff] at hbuild
    obtain ⟨_, _, _⟩ := hbuild
    grind
  | connect c e ihe =>
    intro hbuild; dsimp [build_module', build_module_interface] at hbuild ⊢
    obtain ⟨mod', hbuild', heq⟩ := Option.bind_eq_some_iff.mp hbuild; cases heq
    rw [hbuild'] at hbuild; dsimp at hbuild;
    obtain ⟨mod, hbuild_mod, heq_mod⟩ := ihe hbuild'
    dsimp [Module.toModuleInterface, Module.connect']
    rw [hbuild_mod]; dsimp; cases hbuild; subst_vars
    simp [AssocList.eraseAll_map_comm, Module.connect'', Module.toModuleInterface]
  | product e1 e2 he1 he2 =>
    intro hbuild; dsimp [build_module', build_module_interface] at hbuild ⊢
    obtain ⟨a1, hbuild1, hbuild⟩ := Option.bind_eq_some_iff.mp hbuild
    obtain ⟨a2, hbuild2, heq⟩ := Option.bind_eq_some_iff.mp hbuild; cases heq
    obtain ⟨mod, hbuild_mod, heq_mod⟩ := he1 hbuild1
    obtain ⟨mod2, hbuild_mod2, heq_mod2⟩ := he2 hbuild2
    dsimp [Module.product, Module.toModuleInterface]
    unfold Module.liftL Module.liftR; dsimp
    simp_all only [←AssocList.mapVal_append, AssocList.mapVal_mapVal]
    dsimp at *; cases hbuild; subst_vars
    simp [Module.toModuleInterface, ←AssocList.mapVal_append, AssocList.mapVal_mapVal]

omit [DecidableEq Typ] in
theorem findInput_iff_contains_interface {e m i} :
  e.well_formed ε →
  build_module_interface ε e = some m →
  findInput i e = m.inputs.contains i := by
  intro hwf hbuild
  obtain ⟨mod, hbuild, heq⟩ := build_module_build_module_interface' hbuild
  subst m; dsimp [Module.toModuleInterface]; rw [AssocList.contains_mapval]
  solve_by_elim [findInput_iff_contains]

omit [DecidableEq Typ] in
theorem findOutput_iff_contains_interface {e m i} :
  e.well_formed ε →
  build_module_interface ε e = some m →
  findOutput i e = m.outputs.contains i := by
  intro hwf hbuild
  obtain ⟨mod, hbuild, heq⟩ := build_module_build_module_interface' hbuild
  subst m; dsimp [Module.toModuleInterface]; rw [AssocList.contains_mapval]
  solve_by_elim [findOutput_iff_contains]

omit [DecidableEq Typ] in
theorem build_module_build_module_interface_isSome {e : ExprLow Ident Typ} :
  (e.build_module' ε).isSome → (e.build_module_interface ε).isSome := by
  intros; grind [build_module_build_module_interface, Option.isSome_iff_exists]

omit [DecidableEq Typ] in
theorem well_formed_build_module_interface {e : ExprLow Ident Typ} :
  e.well_formed ε → (e.build_module_interface ε).isSome := by
  solve_by_elim [build_module_build_module_interface_isSome, well_formed_builds_module]

theorem toModuleInterface_inputs_contains {S} {m : Module Ident S} {i} :
  m.inputs.contains i = m.toModuleInterface.inputs.contains i := by
  grind [Module.toModuleInterface, AssocList.contains_mapval]

theorem toModuleInterface_outputs_contains {S} {m : Module Ident S} {i} :
  m.outputs.contains i = m.toModuleInterface.outputs.contains i := by
  grind [Module.toModuleInterface, AssocList.contains_mapval]

omit [DecidableEq Typ] in
theorem well_typed_comm_connection'_ {iexpr e' : ExprLow Ident Typ} {conn} :
  iexpr.well_formed ε → e'.well_typed ε → comm_connection'_ conn iexpr = .some e' → iexpr.well_typed ε := by
  induction iexpr generalizing e' with
  | base inst typ =>
    intro wf wt hcomm
    contradiction
  | connect c e'' ih =>
    intro wf hwt hcomm
    dsimp [comm_connection'_] at hcomm
    by_cases h' : c.output = conn.output ∧ c.input = conn.input
    · simp [h'] at hcomm
      cases e'' with
      | connect c e''' =>
        dsimp at hcomm
        split at hcomm <;> try contradiction
        cases hcomm
        obtain ⟨hwt, h1⟩ := hwt
        obtain ⟨mi, T, hbuild, hf1, hf2⟩ := h1
        obtain ⟨hwt, h2⟩ := hwt
        obtain ⟨mi', T', hbuild', hf1', hf2'⟩ := h2
        dsimp [build_module_interface] at hbuild; rw [hbuild'] at hbuild
        dsimp at hbuild; cases hbuild; dsimp at *
        constructor; constructor
        · assumption
        · constructor; exists T; and_intros
          · assumption
          · rw [AssocList.find?_eraseAll_neq] at hf1 <;> grind
          · rw [AssocList.find?_eraseAll_neq] at hf2 <;> grind
        · constructor; exists T'; and_intros
          · dsimp [build_module_interface]; rw [hbuild']; dsimp
          · grind [AssocList.find?_eraseAll_neq]
          · grind [AssocList.find?_eraseAll_neq]
      | product e1 e2 =>
        dsimp at hcomm; split at hcomm <;> try contradiction
        split at hcomm <;> try contradiction
        cases hcomm
        obtain ⟨hwt1, hwt2⟩ := hwt
        obtain ⟨hwtc, h1⟩ := hwt2
        obtain ⟨mi, T, hbuild, hf1, hf2⟩ := h1
        constructor; constructor; assumption; assumption
        simp only [well_formed_connect, well_formed_product] at wf
        have build_e1 := well_formed_build_module_interface wf.1
        have build_e1' := well_formed_builds_module wf.1
        obtain ⟨⟨Tm, mm⟩, build_e1'⟩ := Option.isSome_iff_exists.mp build_e1'
        obtain ⟨me1, hbuild_e1⟩ := Option.isSome_iff_exists.mp build_e1
        constructor; exists T; and_intros
        · dsimp [build_module_interface]; rw [hbuild, hbuild_e1]; dsimp
        · dsimp; repeat with_reducible cases ‹_ ∧ _›
          rename_i h1 h2 h3 h4 h5 h6 h7 h8 h9
          rw [findInput_iff_contains] at h4 <;> try assumption
          rw [←h9] at h4
          rw [AssocList.append_find_right]; assumption
          apply AssocList.contains_none
          rw [build_module_build_module_interface] at hbuild_e1 <;> try assumption
          cases hbuild_e1; simp [-AssocList.contains_eq, Module.toModuleInterface, AssocList.contains_mapval, h4]
        · dsimp; repeat with_reducible cases ‹_ ∧ _›
          rename_i h1 h2 h3 h4 h5 h6 h7 h8 h9
          rw [findOutput_iff_contains] at h5 <;> try assumption
          rw [←h8] at h5
          rw [AssocList.append_find_right]; assumption
          apply AssocList.contains_none
          rw [build_module_build_module_interface] at hbuild_e1 <;> try assumption
          cases hbuild_e1; simp [-AssocList.contains_eq, Module.toModuleInterface, AssocList.contains_mapval, h5]
      | base inst'' typ'' => contradiction
    · simp [h'] at hcomm; obtain ⟨a, hcomm, hconn⟩ := hcomm; subst_vars; cases hwt; constructor; apply ih <;> assumption
      rename_i hl hr
      rw [well_formed_connect] at wf
      specialize ih wf ‹_› ‹_›
      obtain ⟨mm, -⟩ := refines_comm_connection'_2 wf hcomm
      rw [MatchInterface_simpler_iff] at mm
      obtain ⟨mi, T, hbuild, hf1, hf2⟩ := hr
      unfold build_module_expr at *
      obtain ⟨mmm, hbuild', heq⟩ := build_module_build_module_interface' hbuild
      obtain ⟨mmm', hbuild''⟩ := Option.isSome_iff_exists.mp (well_formed_builds_module wf)
      exists mmm'.2.toModuleInterface, T; and_intros
      · solve_by_elim [build_module_build_module_interface]
      · specialize mm c.input; dsimp [build_module] at mm
        rw [hbuild', hbuild''] at mm; dsimp at mm
        grind [AssocList.find?_map_comm, Module.toModuleInterface]
      · specialize mm c.output; dsimp [build_module] at mm
        rw [hbuild', hbuild''] at mm; dsimp at mm
        grind [AssocList.find?_map_comm, Module.toModuleInterface]
  | product e1 e2 he1 he2 =>
    intro wf hwt hcomm
    dsimp [comm_connection'_] at hcomm
    split at hcomm <;> rename_i hcomm1 hcomm2 <;> (try contradiction) <;> cases hcomm
    · obtain ⟨hwt1, hwt2⟩ := hwt
      obtain ⟨wf1, wf2⟩ := well_formed_product.mp wf
      grind [well_typed]
    · obtain ⟨hwt1, hwt2⟩ := hwt
      obtain ⟨wf1, wf2⟩ := well_formed_product.mp wf
      grind [well_typed]
    · obtain ⟨hwt1, hwt2⟩ := hwt
      obtain ⟨wf1, wf2⟩ := well_formed_product.mp wf
      grind [well_typed]

omit [DecidableEq Typ] in
theorem well_typed_comm_connection'_2 {iexpr e' : ExprLow Ident Typ} {conn} :
  iexpr.well_formed ε → iexpr.well_typed ε → comm_connection'_ conn iexpr = .some e' → e'.well_typed ε := by
  induction iexpr generalizing e' with
  | base => intros; contradiction
  | connect c e ihe =>
    intro hwf hwt hcomm
    dsimp [comm_connection'_] at hcomm
    by_cases h' : c.output = conn.output ∧ c.input = conn.input
    · simp [h'] at hcomm
      cases e with
      | connect c e''' =>
        dsimp at hcomm
        split at hcomm <;> try contradiction
        cases hcomm
        obtain ⟨hwt, h1⟩ := hwt
        obtain ⟨mi, T, hbuild, hf1, hf2⟩ := h1
        obtain ⟨hwt, h2⟩ := hwt
        obtain ⟨mi', T', hbuild', hf1', hf2'⟩ := h2
        dsimp [build_module_interface] at hbuild; rw [hbuild'] at hbuild
        dsimp at hbuild; cases hbuild; dsimp at *
        constructor; constructor
        · assumption
        · constructor; exists T; and_intros
          · assumption
          · rw [AssocList.find?_eraseAll_neq] at hf1 <;> grind
          · rw [AssocList.find?_eraseAll_neq] at hf2 <;> grind
        · constructor; exists T'; and_intros
          · dsimp [build_module_interface]; rw [hbuild']; dsimp
          · grind [AssocList.find?_eraseAll_neq]
          · grind [AssocList.find?_eraseAll_neq]
      | product e1 e2 =>
        dsimp at hcomm; split at hcomm <;> try contradiction
        split at hcomm <;> try contradiction
        cases hcomm
        obtain ⟨hwt1, hwt2⟩ := hwt
        obtain ⟨hwtc, h1⟩ := hwt2
        obtain ⟨T, hbuild, hf1, hf2⟩ := h1
        constructor; dsimp [well_typed] at hwt1; apply hwt1.1
        constructor; apply hwt1.2
        obtain ⟨m1, m2, h1, h2, h3, h4⟩ := build_module_interface_product hbuild
        rw [h3] at hf1; rw [h4] at hf2
        rename_i h
        obtain ⟨fi1, fo1, fi2, fo2⟩ := h
        rw [findInput_iff_contains_interface] at fi1 <;> try assumption
        rw [findOutput_iff_contains_interface] at fo1 <;> try assumption
        all_goals grind [AssocList.contains_none, AssocList.append_find_right, well_formed_connect, well_formed_product]
      | base inst'' typ'' => contradiction
    · simp [h'] at hcomm; obtain ⟨a, hcomm, hconn⟩ := hcomm; subst_vars; cases hwt; constructor; apply ihe <;> assumption
      rename_i hl hr
      rw [well_formed_connect] at hwf
      specialize ihe hwf ‹_› ‹_›
      obtain ⟨mm, -⟩ := refines_comm_connection'_2 hwf hcomm
      rw [MatchInterface_simpler_iff] at mm
      obtain ⟨mi, T, hbuild, hf1, hf2⟩ := hr
      unfold build_module_expr at *
      obtain ⟨mmm, hbuild', heq⟩ := build_module_build_module_interface' hbuild
      obtain ⟨mmm', hbuild''⟩ := Option.isSome_iff_exists.mp (well_formed_builds_module (wf_comm_connection'_ hcomm hwf))
      exists mmm'.2.toModuleInterface, T; and_intros
      · solve_by_elim [build_module_build_module_interface]
      · specialize mm c.input; dsimp [build_module] at mm
        rw [hbuild', hbuild''] at mm; dsimp at mm
        grind [AssocList.find?_map_comm, Module.toModuleInterface]
      · specialize mm c.output; dsimp [build_module] at mm
        rw [hbuild', hbuild''] at mm; dsimp at mm
        grind [AssocList.find?_map_comm, Module.toModuleInterface]
  | product e1 e2 he1 he2 =>
    intro wf hwt hcomm
    dsimp [comm_connection'_] at hcomm
    split at hcomm <;> rename_i hcomm1 hcomm2 <;> (try contradiction) <;> cases hcomm
    · obtain ⟨hwt1, hwt2⟩ := hwt
      obtain ⟨wf1, wf2⟩ := well_formed_product.mp wf
      grind [well_typed]
    · obtain ⟨hwt1, hwt2⟩ := hwt
      obtain ⟨wf1, wf2⟩ := well_formed_product.mp wf
      grind [well_typed]
    · obtain ⟨hwt1, hwt2⟩ := hwt
      obtain ⟨wf1, wf2⟩ := well_formed_product.mp wf
      grind [well_typed]

omit [DecidableEq Typ] in
theorem well_formed_refines_well_typed_mi {e e' : ExprLow Ident Typ} {c} :
  MatchInterface [e| e, ε ] [e| e', ε ] →
  e.well_formed ε →
  e'.well_formed ε →
  (connect c e).well_typed ε →
  e'.well_typed ε →
  (connect c e').well_typed ε := by
  intro ref wf1 wf2 wt1 wt2
  rw [MatchInterface_simpler_iff] at ref
  constructor; assumption
  obtain ⟨-, wt1⟩ := wt1; clear wt2
  obtain ⟨m1, hm1⟩ := Option.isSome_iff_exists.mp (well_formed_builds_module wf1)
  obtain ⟨m2, hm2⟩ := Option.isSome_iff_exists.mp (well_formed_builds_module wf2)
  obtain hc1 := build_module_build_module_interface hm1
  obtain hc2 := build_module_build_module_interface hm2
  have ref' := ref
  replace ref := (ref c.input).1
  replace ref' := (ref' c.output).2
  dsimp [build_module_expr, build_module] at *
  rw [hm1,hm2] at ref ref'; dsimp at *
  obtain ⟨mi, T, hbuild, hf1, hf2⟩ := wt1
  rw [hc1] at hbuild; cases hbuild; dsimp [Module.toModuleInterface] at *
  exists m2.snd.toModuleInterface, T; and_intros <;> try assumption
  · dsimp [Module.toModuleInterface] at *; grind
  · dsimp [Module.toModuleInterface] at *; grind

omit [DecidableEq Typ] in
theorem well_formed_refines_well_typed1 {e e' : ExprLow Ident Typ} {c} :
  [e| e, ε ] ⊑ [e| e', ε ] →
  e.well_formed ε →
  e'.well_formed ε →
  (connect c e).well_typed ε →
  e'.well_typed ε →
  (connect c e').well_typed ε := by
  intro ⟨mm, tmp⟩ wf1 wf2 wt1 wt2; clear tmp
  apply well_formed_refines_well_typed_mi <;> assumption

omit [DecidableEq Typ] in
theorem well_formed_refines_well_typed2 {e e' : ExprLow Ident Typ} {c} :
  [e| e', ε ] ⊑ [e| e, ε ] →
  e.well_formed ε →
  e'.well_formed ε →
  (connect c e).well_typed ε →
  e'.well_typed ε →
  (connect c e').well_typed ε := by
  intro ⟨mm, tmp⟩ wf1 wf2 wt1 wt2; clear tmp
  replace mm := MatchInterface_symmetric _ mm
  apply well_formed_refines_well_typed_mi <;> assumption

omit [DecidableEq Typ] in
theorem well_typed_comm_connect1 {e1 e2 : ExprLow Ident Typ} {c} :
  (e1.product (connect c e2)).well_typed ε →
  findInput c.input e1 = false →
  findOutput c.output e1 = false →
  e1.well_formed ε →
  (connect c (e1.product e2)).well_typed ε := by
  intro ⟨hwt1, ⟨hwt2, mi, T, hbuild, hfi1, hfi2⟩⟩ hf1 hf2 hwf
  constructor; constructor <;> assumption
  obtain ⟨a, hbuild'⟩ := Option.isSome_iff_exists.mp (well_formed_build_module_interface hwf)
  constructor; exists T; and_intros
  · dsimp [build_module_interface]; rw [hbuild,hbuild']; dsimp
  · dsimp; rw [AssocList.append_find_right]; assumption
    apply AssocList.contains_none; rw [findInput_iff_contains_interface (m := a)] at hf1 <;> try assumption
    grind
  · dsimp; rw [AssocList.append_find_right]; assumption
    apply AssocList.contains_none; rw [findOutput_iff_contains_interface (m := a)] at hf2 <;> try assumption
    grind

omit [DecidableEq Typ] in
theorem well_typed_comm_connect2 {e1 e2 : ExprLow Ident Typ} {c} :
  (connect c (e1.product e2)).well_typed ε →
  findInput c.input e1 = false →
  findOutput c.output e1 = false →
  e1.well_formed ε →
  (e1.product (connect c e2)).well_typed ε := by
  intro ⟨⟨hwt1, hwt2⟩, ⟨mi, T, hbuild, hfi1, hfi2⟩⟩ hf1 hf2 hwf
  constructor; assumption
  have ⟨m1, m2, hm1, hm2, heq1, heq2⟩ := build_module_interface_product hbuild
  constructor; assumption
  rw [heq1] at hfi1; rw [heq2] at hfi2
  constructor; exists T; and_intros
  · assumption
  · dsimp; rw [AssocList.append_find_right] at hfi1; assumption
    apply AssocList.contains_none; rw [findInput_iff_contains_interface (m := m1)] at hf1 <;> try assumption
    grind
  · dsimp; rw [AssocList.append_find_right] at hfi2; assumption
    apply AssocList.contains_none; rw [findOutput_iff_contains_interface (m := m1)] at hf2 <;> try assumption
    grind

omit [DecidableEq Typ] in
theorem well_typed_comm_connect_iff {e1 e2 : ExprLow Ident Typ} {c} :
  findInput c.input e1 = false →
  findOutput c.output e1 = false →
  e1.well_formed ε →
  ((e1.product (connect c e2)).well_typed ε ↔ (connect c (e1.product e2)).well_typed ε) := by
  intros; constructor <;> (intros; solve_by_elim [well_typed_comm_connect1, well_typed_comm_connect2])

theorem wt_comm_base_ {e e' : ExprLow Ident Typ} {inst typ}:
  e.well_formed ε →
  e.comm_base_ inst typ = .some e' →
  e.well_typed ε →
  e'.well_typed ε := by
  induction e generalizing e' with
  | base inst' typ' => intro hwf hcomm hwt; cases hcomm
  | connect c e ihe =>
    intro hwf hcomm hwt
    dsimp [comm_base_] at hcomm
    rw [Option.map_eq_some'] at hcomm
    obtain ⟨a, hcomm, hconn⟩ := hcomm; subst_vars
    simp only [well_formed_connect] at *
    apply well_formed_refines_well_typed2
    apply refines_comm_base_
    any_goals assumption
    apply wf_comm_base_; assumption; assumption
    apply ihe; assumption; assumption; apply hwt.1
  | product e1 e2 he1 he2 =>
    intro hwf hcomm hwt
    dsimp [comm_base_] at hcomm
    split at hcomm
    · split at hcomm <;> try contradiction
      · split at hcomm <;> try contradiction
        cases hcomm
        constructor; constructor
        obtain ⟨hwt1, hwt2, hwt3⟩ := hwt
        constructor <;> assumption
      · split at hcomm <;> try contradiction
        cases hcomm; subst_vars
        rw [← well_typed_comm_connect_iff]; assumption
        dsimp [findInput]; rename_i h; obtain ⟨h1, h2⟩ := h
        simp [AssocList.valsList] at h2 ⊢; grind
        dsimp [findOutput]; rename_i h; obtain ⟨h1, h2⟩ := h
        simp [AssocList.valsList] at h1 ⊢; grind
        rw [well_formed_product] at hwf; apply hwf.1
      · split at hcomm <;> try contradiction
        cases hcomm
        cases hwt; constructor; constructor; assumption
    · obtain ⟨e'', h1, h2⟩ := Option.map_eq_some'.mp hcomm
      subst_vars
      constructor; apply hwt.1
      apply he2
      rw [well_formed_product] at hwf; apply hwf.2
      assumption
      apply hwt.2

omit [DecidableEq Typ] in
theorem refines_fix_point_opt1 {iexpr f n} :
    (∀ e e', wfc e → f e = .some e' → ([e| e', ε ] ⊑ ([e| e, ε ])) ∧ wfc e') →
    wfc iexpr →
    [e| fix_point_opt f iexpr n , ε ] ⊑ ([e| iexpr, ε ]) := by
  intros; solve_by_elim [refines_fix_point_opt, Module.refines_reflexive]

omit [DecidableEq Typ] [DecidableEq Ident] in
theorem refines_fix_point_wfc {iexpr f n} :
    (∀ e e', wfc e → f e = .some e' → wfc e') →
    wfc iexpr →
    wfc (fix_point_opt f iexpr n) := by
  intro hfw wf
  induction n generalizing iexpr with
  | zero => assumption
  | succ n ih =>
    dsimp [fix_point_opt]; split <;> grind

omit [DecidableEq Typ] [DecidableEq Ident] in
theorem refines_fix_point_wfc2 {iexpr f n} :
    (∀ e e', wfc e' → f e = .some e' → wfc e) →
    wfc (fix_point_opt f iexpr n) →
    wfc iexpr := by
  intro hfw wf
  induction n generalizing iexpr with
  | zero => assumption
  | succ n ih =>
    dsimp [fix_point_opt] at *; split at wf <;> grind

omit [DecidableEq Typ] in
theorem refines_fix_point_opt2 {iexpr f n} :
    (∀ e e', wfc e → f e = .some e' → ([e| e, ε ] ⊑ ([e| e', ε ])) ∧ wfc e') →
    wfc iexpr →
    [e| iexpr, ε ] ⊑ ([e| fix_point_opt f iexpr n, ε ]) := by
  intros; solve_by_elim [refines_fix_point_opt2', Module.refines_reflexive]

omit [DecidableEq Typ] in
theorem refines_foldr' {α} {iexpr e'} {l : List α} (f : α → ExprLow Ident Typ → ExprLow Ident Typ) :
    (∀ e a, wfc e → ([e| f a e, ε ] ⊑ ([e| e, ε ])) ∧ wfc (f a e)) →
    [e| e', ε ] ⊑ ([e| iexpr, ε ]) → wfc e' →
    ([e| l.foldr f e', ε ] ⊑ ([e| iexpr, ε ])) ∧ wfc (l.foldr f e') := by
  induction l generalizing iexpr e' with
  | nil => intros; solve_by_elim
  | cons x xs ih =>
    intro h href hwf; dsimp
    have ⟨ih', ihwf⟩ := ih h href hwf
    have ⟨hrand₁, hrand₂⟩ := h _ x ihwf
    solve_by_elim [Module.refines_transitive]

omit [DecidableEq Typ] in
theorem refines_foldr2' {α} {iexpr e'} {l : List α} (f : α → ExprLow Ident Typ → ExprLow Ident Typ) :
    (∀ e a, wfc e → ([e| e, ε ] ⊑ ([e| f a e, ε ])) ∧ wfc (f a e)) →
    [e| iexpr, ε ] ⊑ ([e| e', ε ]) → wfc e' →
    ([e| iexpr, ε ] ⊑ ([e| l.foldr f e', ε ])) ∧ wfc (l.foldr f e') := by
  induction l generalizing iexpr e' with
  | nil => intros; solve_by_elim
  | cons x xs ih =>
    intro h href hwf; dsimp
    have ⟨ih', ihwf⟩ := ih h href hwf
    have ⟨hrand₁, hrand₂⟩ := h _ x ihwf
    solve_by_elim [Module.refines_transitive]

omit [DecidableEq Typ] in
theorem refines_foldr {α} {iexpr} {l : List α} (f : α → ExprLow Ident Typ → ExprLow Ident Typ) :
    (∀ e a, wfc e → ([e| f a e, ε ] ⊑ ([e| e, ε ])) ∧ wfc (f a e)) → wfc iexpr →
    ([e| l.foldr f iexpr, ε ] ⊑ ([e| iexpr, ε ])) := by
  intros; exact refines_foldr' (l := l) f ‹_› Module.refines_reflexive ‹_› |>.1

omit [DecidableEq Typ] in
theorem refines_foldr2 {α} {iexpr} {l : List α} (f : α → ExprLow Ident Typ → ExprLow Ident Typ) :
    (∀ e a, wfc e → ([e| e, ε ] ⊑ ([e| f a e, ε ])) ∧ wfc (f a e)) → wfc iexpr →
    ([e| iexpr, ε ] ⊑ ([e| l.foldr f iexpr, ε ])) := by
  intros; exact refines_foldr2' (l := l) f ‹_› Module.refines_reflexive ‹_› |>.1

omit [DecidableEq Typ] in
theorem wf_foldr {α} {iexpr} {l : List α} (f : α → ExprLow Ident Typ → ExprLow Ident Typ) :
    (∀ e a, wfc e → ([e| f a e, ε ] ⊑ ([e| e, ε ])) ∧ wfc (f a e)) → wfc iexpr → wfc (l.foldr f iexpr) := by
  intros; exact refines_foldr' (l := l) f ‹_› Module.refines_reflexive ‹_› |>.2

theorem refines_comm_bases {iexpr l} :
  iexpr.well_formed ε → [e| comm_bases l iexpr, ε ] ⊑ ([e| iexpr, ε ]) := by
  unfold comm_bases; intro hwf
  apply refines_foldr
  · intros; and_intros
    · unfold Function.uncurry; unfold comm_base
      apply refines_fix_point_opt1; intros; and_intros
      all_goals solve_by_elim [refines_comm_base_, wf_comm_base_]
    · unfold Function.uncurry; unfold comm_base
      apply wf_fix_point_opt (wfc := λ x => well_formed ε x = true); intros
      all_goals solve_by_elim [wf_comm_base_]
  · assumption

theorem refines_comm_bases_well_formed {iexpr l} :
  iexpr.well_formed ε → (comm_bases l iexpr).well_formed ε := by
  intro hwf
  apply wf_foldr (wfc := λ x => well_formed ε x = true); intros; and_intros
  · apply refines_fix_point_opt1; intros; and_intros
    all_goals solve_by_elim [refines_comm_base_, wf_comm_base_]
  · unfold Function.uncurry; unfold comm_base
    apply wf_fix_point_opt (wfc := λ x => well_formed ε x = true); intros
    all_goals solve_by_elim [wf_comm_base_]
  · assumption

omit [DecidableEq Typ] in
theorem refines_comm_connections' {iexpr l} :
  iexpr.well_formed ε → [e| comm_connections' l iexpr, ε ] ⊑ ([e| iexpr, ε ]) := by
  unfold comm_connections'; intro hwf
  apply refines_foldr
  · intros; and_intros
    · unfold comm_connection'
      apply refines_fix_point_opt1; intros; and_intros
      all_goals solve_by_elim [refines_comm_connection'_, wf_comm_connection'_]
    · unfold comm_connection'
      apply wf_fix_point_opt (wfc := λ x => well_formed ε x = true); intros
      all_goals solve_by_elim [refines_comm_connection'_, wf_comm_connection'_]
  · assumption

omit [DecidableEq Typ] in
theorem refines_comm_connections'_well_formed {iexpr l} :
  iexpr.well_formed ε → (comm_connections' l iexpr).well_formed ε := by
  intro hwf
  apply wf_foldr (wfc := λ x => well_formed ε x = true); intros; and_intros
  · unfold comm_connection'
    apply refines_fix_point_opt1; intros; and_intros
    all_goals solve_by_elim [refines_comm_connection'_, wf_comm_connection'_]
  · unfold comm_connection'
    apply wf_fix_point_opt (wfc := λ x => well_formed ε x = true); intros
    all_goals solve_by_elim [refines_comm_connection'_, wf_comm_connection'_]
  · assumption

omit [DecidableEq Typ] in
theorem refines_comm_connections'_well_formed2' {iexpr l n} :
  (List.foldr (λ conn e => fix_point_opt (comm_connection'_ conn) e n) iexpr l).well_formed ε → iexpr.well_formed ε := by
  intro hwf
  induction l generalizing iexpr with
  | nil => assumption
  | cons a b ih =>
    apply ih; dsimp [List.foldr] at hwf
    apply refines_fix_point_wfc2 (wfc := λ x => well_formed ε x = true) (by solve_by_elim [wf_comm_connection'_2'])
    apply hwf

omit [DecidableEq Typ] in
theorem refines_comm_connections'_well_formed2 {iexpr l} :
  (comm_connections' l iexpr).well_formed ε → iexpr.well_formed ε := refines_comm_connections'_well_formed2'

omit [DecidableEq Typ] in
theorem refines_comm_connections2' {iexpr l} :
  iexpr.well_formed ε → [e| iexpr, ε ] ⊑ ([e| comm_connections' l iexpr, ε ]) := by
  unfold comm_connections'; intro hwf
  apply refines_foldr2
  · intros; and_intros
    · unfold comm_connection'
      apply refines_fix_point_opt2; intros; and_intros
      all_goals solve_by_elim [refines_comm_connection'_2, wf_comm_connection'_]
    · unfold comm_connection'
      apply wf_fix_point_opt (wfc := λ x => well_formed ε x = true); intros
      all_goals solve_by_elim [refines_comm_connection'_, wf_comm_connection'_]
  · assumption

omit [DecidableEq Typ] in
theorem wt_comm_connections2'' {iexpr l} :
  iexpr.well_formed ε ∧ iexpr.well_typed ε → (comm_connections' l iexpr).well_formed ε ∧ (comm_connections' l iexpr).well_typed ε := by
  intro hwf
  apply wf_foldr (wfc := λ x => well_formed ε x ∧ well_typed ε x); intros; constructor
  · apply refines_fix_point_opt1 (wfc := λ x => well_formed ε x ∧ well_typed ε x); intros; constructor
    apply refines_comm_connection'_
    rename_i y _; apply y.1; assumption
    and_intros
    · apply wf_comm_connection'_; assumption; rename_i y _; apply y.1
    · apply well_typed_comm_connection'_2; rotate_left 2; assumption
      rename_i y _; apply y.1; rename_i y _; apply y.2
    · rename_i y; apply y.1
    · rename_i y; apply y.2
  · unfold comm_connection'
    apply wf_fix_point_opt (wfc := λ x => well_formed ε x ∧ well_typed ε x); intros
    any_goals assumption
    and_intros
    · rename_i y _; apply wf_comm_connection'_; assumption; apply y.1
    · rename_i y _; apply well_typed_comm_connection'_2 <;> try assumption
      apply y.1; apply y.2
  · assumption

omit [DecidableEq Typ] in
theorem wt_comm_connections2' {iexpr l} :
  iexpr.well_formed ε → iexpr.well_typed ε → (comm_connections' l iexpr).well_typed ε := by
  intro h1 h2
  apply (wt_comm_connections2'' _).2
  grind

theorem wt_comm_bases' {iexpr l} :
  iexpr.well_formed ε ∧ iexpr.well_typed ε → (comm_bases l iexpr).well_formed ε ∧ (comm_bases l iexpr).well_typed ε := by
  intro hwf
  apply wf_foldr (wfc := λ x => well_formed ε x ∧ well_typed ε x); intros; constructor
  · apply refines_fix_point_opt1 (wfc := λ x => well_formed ε x ∧ well_typed ε x); intros; constructor
    apply refines_comm_base_
    rename_i y _; apply y.1; assumption
    and_intros
    · apply wf_comm_base_; assumption; rename_i y _; apply y.1
    · apply wt_comm_base_ _ ‹_›; rename_i y _; apply y.2; rename_i y _; apply y.1
    · rename_i y; apply y.1
    · rename_i y; apply y.2
  · unfold Function.uncurry comm_base
    apply wf_fix_point_opt (wfc := λ x => well_formed ε x ∧ well_typed ε x); intros
    any_goals assumption
    and_intros
    · rename_i y _; apply wf_comm_base_; assumption; apply y.1
    · rename_i y _; apply wt_comm_base_ <;> try assumption
      apply y.1; apply y.2
  · assumption

theorem wt_comm_bases {iexpr l} :
  iexpr.well_formed ε → iexpr.well_typed ε → (comm_bases l iexpr).well_typed ε := by
  intro h1 h2
  apply (wt_comm_bases' _).2
  grind

omit [DecidableEq Typ] in
theorem build_module'_build_module_type {e} :
  e.wf ε → build_module' ε e = some ⟨[T| e, ε], [e| e, ε ]⟩ := by
  intro wf
  unfold build_module_type build_module_expr build_module
  replace wf := wf_builds_module wf
  rw [Option.isSome_iff_exists] at wf
  obtain ⟨m, hbuild⟩ := wf
  rw [hbuild]; rfl

theorem keysList_unchanged {α} {p : PortMap Ident (InternalPort Ident)} {ins : PortMap Ident α}:
  (∀ x ∈ AssocList.keysList p, AssocList.contains x ins = false) →
  (∀ x ∈ AssocList.valsList p, AssocList.contains x ins = false) →
  AssocList.mapKey (AssocList.bijectivePortRenaming p) ins = ins := by
  induction ins with
  | nil => intros; rfl
  | cons k v xs ih =>
    intro hkey hval
    rw [AssocList.mapKey_cons, ih] <;> try assumption
    · suffices (AssocList.bijectivePortRenaming p k) = k by rw [this]
      have hin : k ∉ AssocList.keysList p := by
        intro hin
        replace hkey := hkey _ hin
        simp at hkey
      have hin' : k ∉ AssocList.valsList p := by
        intro hin
        replace hkey := hval _ hin
        simp at hkey
      simp only [←AssocList.inverse_keysList] at *
      rw [←AssocList.keysList_find?_isSome_iff,Bool.not_eq_true,Option.isSome_eq_false_iff,Option.isNone_iff_eq_none] at hin hin'
      apply AssocList.bijectivePortRenaming_eq2 <;> assumption
    · intro k' hin; specialize hkey _ hin
      simp only [AssocList.contains, AssocList.any_eq, List.any_eq_false, beq_iff_eq, Prod.forall,
        AssocList.toList, List.any_cons, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at *
      cases hkey; assumption
    · intro k' hin; specialize hval _ hin
      simp only [AssocList.contains, AssocList.any_eq, List.any_eq_false, beq_iff_eq, Prod.forall,
        AssocList.toList, List.any_cons, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at *
      cases hval; assumption

omit [DecidableEq Typ] in
theorem ensureIOUnmodified_correct {e : ExprLow Ident Typ} {p} :
  e.well_formed ε → e.ensureIOUnmodified p → [e| e, ε ].renamePorts p = ([e| e, ε ]) := by
  unfold ensureIOUnmodified; simp only [beq_false, List.all_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq, and_imp]
  intro wf hi1 hi2 ho1 ho2
  generalize h : ([e| e, ε ]) = m; rcases m with ⟨ins, outs, ints, inits⟩
  simp [Module.renamePorts, Module.mapPorts2, Module.mapInputPorts, Module.mapOutputPorts]; and_intros
  · have hi1' : ∀ x, x ∈ p.input.keysList → ins.contains x = false := by
      have : ins = ([e| e, ε ]).inputs := by simp [*]
      subst ins; intro x hcont; rw [←findInput_iff_contains] <;> try assumption
      solve_by_elim
      rw [build_module'_build_module_type]
      exact well_formed_implies_wf wf
    have hi2' : ∀ x, x ∈ p.input.valsList → ins.contains x = false := by
      have : ins = ([e| e, ε ]).inputs := by simp [*]
      subst ins; intro x hcont; rw [←findInput_iff_contains] <;> try assumption
      solve_by_elim
      rw [build_module'_build_module_type]
      exact well_formed_implies_wf wf
    apply keysList_unchanged <;> assumption
  · have hi1' : ∀ x, x ∈ p.output.keysList → outs.contains x = false := by
      have : outs = ([e| e, ε ]).outputs := by simp [*]
      subst outs; intro x hcont; rw [←findOutput_iff_contains] <;> try assumption
      solve_by_elim
      rw [build_module'_build_module_type]
      exact well_formed_implies_wf wf
    have hi2' : ∀ x, x ∈ p.output.valsList → outs.contains x = false := by
      have : outs = ([e| e, ε ]).outputs := by simp [*]
      subst outs; intro x hcont; rw [←findOutput_iff_contains] <;> try assumption
      solve_by_elim
      rw [build_module'_build_module_type]
      exact well_formed_implies_wf wf
    apply keysList_unchanged <;> assumption

theorem force_replace_eq_replace {e e₁ e₂ : ExprLow Ident Typ} :
    (e.force_replace e₁ e₂).1 = e.replace e₁ e₂ := by
  induction e <;> simp [force_replace, replace] <;> split <;> simp [*]

omit [DecidableEq Typ] in
theorem refines_subset_well_formed {e : ExprLow Ident Typ} (ε' : Env Ident Typ) :
  ε.subsetOf ε' → e.well_formed ε → e.well_formed ε' := by
  induction e with
  | base inst typ =>
    intro hsub hwf
    dsimp [well_formed] at *
    split at hwf <;> try contradiction
    simp at hwf
    have ⟨ha, hb, hc, hd⟩ := hwf; clear hwf
    rename_i T m heq
    rw [hsub _ _ heq]; simp; and_intros <;> assumption
  | product e₁ e₂ ih1 ih2 =>
    intro hsub1 hwf1
    rw [well_formed_product] at *
    grind
  | connect c e ihe =>
    intro hsub1 hwf1
    rw [well_formed_connect] at *
    grind

omit [DecidableEq Typ] in
theorem refines_subset_left {e : ExprLow Ident Typ} (ε₁ ε : Env Ident Typ) :
  ε₁.subsetOf ε → e.well_formed ε₁ →
  [e| e, ε₁ ] ⊑ ([e| e, ε ]) := by
  induction e with
  | base inst typ =>
    intro hsub1 hwf1
    dsimp [drunfold] at *
    dsimp [well_formed] at hwf1
    split at hwf1 <;> try contradiction
    rename_i T mod heq
    rw [hsub1 _ _ heq]
    rw [heq]
    apply Module.refines_reflexive
  | product e₁ e₂ ih1 ih2 =>
    intro hsub1 hwf1
    have ⟨ hwfl, hwfr ⟩ := well_formed_product.mp hwf1
    have hwfl' := refines_subset_well_formed _ hsub1 hwfl
    have hwfr' := refines_subset_well_formed _ hsub1 hwfr
    apply refines_product
    apply well_formed_implies_wf; assumption
    apply well_formed_implies_wf; assumption
    apply well_formed_implies_wf; assumption
    apply well_formed_implies_wf; assumption
    all_goals solve_by_elim
  | connect c e ihe =>
    intro hsub1 hwf1
    have hwfl := well_formed_connect.mp hwf1
    have hwfl' := refines_subset_well_formed _ hsub1 hwfl
    apply refines_connect
    apply well_formed_implies_wf; assumption
    apply well_formed_implies_wf; assumption
    solve_by_elim

omit [DecidableEq Typ] in
theorem refines_subset_right {e : ExprLow Ident Typ} (ε₁ ε : Env Ident Typ) :
  ε₁.subsetOf ε → e.well_formed ε₁ →
  [e| e, ε ] ⊑ ([e| e, ε₁ ]) := by
  induction e with
  | base inst typ =>
    intro hsub1 hwf1
    dsimp [drunfold] at *
    dsimp [well_formed] at hwf1
    split at hwf1 <;> try contradiction
    rename_i T mod heq
    rw [hsub1 _ _ heq]
    rw [heq]
    apply Module.refines_reflexive
  | product e₁ e₂ ih1 ih2 =>
    intro hsub1 hwf1
    have ⟨ hwfl, hwfr ⟩ := well_formed_product.mp hwf1
    have hwfl' := refines_subset_well_formed _ hsub1 hwfl
    have hwfr' := refines_subset_well_formed _ hsub1 hwfr
    apply refines_product
    apply well_formed_implies_wf; assumption
    apply well_formed_implies_wf; assumption
    apply well_formed_implies_wf; assumption
    apply well_formed_implies_wf; assumption
    all_goals solve_by_elim
  | connect c e ihe =>
    intro hsub1 hwf1
    have hwfl := well_formed_connect.mp hwf1
    have hwfl' := refines_subset_well_formed _ hsub1 hwfl
    apply refines_connect
    apply well_formed_implies_wf; assumption
    apply well_formed_implies_wf; assumption
    solve_by_elim

omit [DecidableEq Typ] in
theorem refines_subset {e e' : ExprLow Ident Typ} (ε₁ ε₂ ε ε' : Env Ident Typ) :
  ε₁.subsetOf ε → ε₂.subsetOf ε' → e.well_formed ε₁ → e'.well_formed ε₂ →
  [e| e, ε₁ ] ⊑ ([e| e', ε₂ ]) →
  [e| e, ε ] ⊑ ([e| e', ε' ]) := by
  intro hsub1 hsub2 hwf1 hwf2 href
  have hwfl' := refines_subset_well_formed _ hsub1 hwf1
  have hwfr' := refines_subset_well_formed _ hsub2 hwf2
  apply Module.refines_transitive
  apply refines_subset_right
  apply hsub1; assumption
  apply Module.refines_transitive; assumption
  apply refines_subset_left <;> assumption

omit [DecidableEq Typ] in
theorem refines_subset₂ {e e' : ExprLow Ident Typ} (ε₁ ε₂ ε ε' : Env Ident Typ) :
  ε.subsetOf ε₁ → ε'.subsetOf ε₂ → e.well_formed ε → e'.well_formed ε' →
  [e| e, ε₁ ] ⊑ ([e| e', ε₂ ]) →
  [e| e, ε ] ⊑ ([e| e', ε' ]) := by
  intro hsub1 hsub2 hwf1 hwf2 href
  have hwfl' := refines_subset_well_formed _ hsub1 hwf1
  have hwfr' := refines_subset_well_formed _ hsub2 hwf2
  apply Module.refines_transitive
  apply refines_subset_left
  apply hsub1; assumption
  apply Module.refines_transitive; assumption
  apply refines_subset_right <;> assumption

end Refinement

section ExprLowFoldL

variable {Ident Typ}
variable [DecidableEq Ident]

theorem build_module_product_foldl {α} {ε} {acc accb} {l : List α} {f : α → ExprLow Ident Typ}:
  (∀ i, i ∈ l → ∃ b, (ExprLow.build_module' ε (f i)) = .some b) →
  (ExprLow.build_module' ε acc) = .some accb →
  ExprLow.build_module ε (List.foldl (λ acc i => (f i).product acc) acc l)
  = List.foldl (λ acc i => ⟨_, Module.product (ExprLow.build_module ε (f i)).2 acc.2⟩) (ExprLow.build_module ε acc) l := by
  induction l generalizing acc accb with
  | nil => intros; rfl
  | cons x xs ih =>
    intro hfb haccb
    have Hxin: x ∈ x :: xs := by simpa
    obtain ⟨eb, heb⟩ := hfb x Hxin
    dsimp; rw [ih]
    rotate_left 2
    dsimp [ExprLow.build_module']; rw [heb, haccb]; dsimp
    rotate_left 1; intros i Hi
    apply hfb
    right; assumption
    congr
    conv => lhs; dsimp [ExprLow.build_module, ExprLow.build_module']; rw [heb, haccb]; dsimp
    unfold ExprLow.build_module
    congr
    all_goals solve | rw [haccb]; rfl | rw [heb]; rfl

theorem build_module_product_foldr {α} {ε} {acc accb} {l : List α} {f : α → ExprLow Ident Typ}:
  (∀ i, i ∈ l → ∃ b, (ExprLow.build_module' ε (f i)) = .some b) →
  (ExprLow.build_module' ε acc) = .some accb →
  ExprLow.build_module' ε (List.foldr (λ i acc => (f i).product acc) acc l)
  = List.foldr (λ i acc => ⟨_, Module.product (ExprLow.build_module ε (f i)).2 acc.2⟩) (ExprLow.build_module ε acc) l := by
  induction l generalizing acc accb with
  | nil => intros h1 h2; dsimp [build_module]; rw [h2]; rfl
  | cons x xs ih =>
    intro hfb haccb
    have Hxin: x ∈ x :: xs := by simpa
    obtain ⟨eb, heb⟩ := hfb x Hxin
    dsimp [build_module, build_module'];
    rw [heb]
    dsimp
    rw [ih]
    · dsimp; rfl
    · intro i Hi; apply hfb; right; assumption
    · exact haccb

theorem build_module_connect_foldl {α} {ε : Env Ident Typ} {acc accb} {l : List α} {f : α → Connection Ident}:
  (ExprLow.build_module' ε acc) = .some accb →
  ExprLow.build_module ε (List.foldl (λ acc i => acc.connect (f i)) acc l)
  = List.foldl (λ acc i => ⟨acc.1, acc.2.connect' (f i).output (f i).input⟩) (ExprLow.build_module ε acc) l := by
    induction l generalizing acc accb with
    | nil => intros; rfl
    | cons x xs ih =>
      intros haccb
      dsimp; rw [ih]
      congr
      dsimp [ExprLow.build_module, ExprLow.build_module']
      rw [haccb]
      dsimp
      simp [ExprLow.build_module, ExprLow.build_module']
      rw [haccb]
      dsimp

theorem check_eq_build_module_interface [DecidableEq Typ] {ε : Env Ident Typ} {iexpr iexpr' : ExprLow Ident Typ} {a} :
  iexpr.check_eq iexpr' →
  build_module_interface ε iexpr = some a →
  ∃ b, build_module_interface ε iexpr' = some b ∧ a.inputs.EqExt b.inputs ∧ a.outputs.EqExt b.outputs := by
  induction iexpr generalizing iexpr' a with
  | base inst typ =>
    intro hchk hbmi
    cases iexpr' <;> try contradiction
    simp only [check_eq, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq] at hchk
    repeat with_reducible cases ‹_ ∧ _›; subst_vars
    simp only [build_module_interface, Option.map_eq_some_iff, Sigma.exists] at hbmi
    obtain ⟨a1, b1, hε, modint⟩ := hbmi; subst_vars
    dsimp [build_module_interface]; rw [hε]; dsimp
    constructor; and_intros
    · rfl
    · rw [Module.renamePorts_EqExt]; apply Batteries.AssocList.EqExt.refl
      all_goals (constructor <;> solve_by_elim [Batteries.AssocList.EqExt.symm])
    · rw [Module.renamePorts_EqExt]; apply Batteries.AssocList.EqExt.refl
      all_goals (constructor <;> solve_by_elim [Batteries.AssocList.EqExt.symm])
  | connect c e ih =>
    intro hchk hbuild
    cases iexpr' <;> try contradiction
    simp only [check_eq, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq] at hchk
    cases hchk; subst_vars
    rename_i c e' hchk
    dsimp [build_module_interface] at hbuild
    rw [Option.bind_eq_some_iff] at hbuild
    obtain ⟨a1, hbuild, heq⟩ := hbuild
    cases heq
    specialize ih hchk hbuild
    obtain ⟨bmod, hbuild', h1, h2⟩ := ih
    constructor; and_intros
    · dsimp [build_module_interface]; rw [hbuild']; rfl
    · solve_by_elim [AssocList.EqExt_eraseAll]
    · solve_by_elim [AssocList.EqExt_eraseAll]
  | product e1 e2 ih1 ih2 =>
    intro hchk hbuild
    cases iexpr' <;> try contradiction
    rename_i e1' e2'
    simp only [check_eq, Bool.decide_and, Bool.decide_eq_true, Bool.and_eq_true] at hchk
    obtain ⟨h1, h2⟩ := hchk
    dsimp [build_module_interface] at hbuild
    rw [Option.bind_eq_some_iff] at hbuild
    obtain ⟨a1, heq, hbuild⟩ := hbuild
    rw [Option.bind_eq_some_iff] at hbuild
    obtain ⟨a2, heq', hbuild⟩ := hbuild
    cases hbuild
    obtain ⟨a1', hbuild1, hext1, hext2⟩ := ih1 h1 heq
    obtain ⟨a2', hbuild2, hext1', hext2'⟩ := ih2 h2 heq'
    dsimp [build_module_interface]
    rw [hbuild1,hbuild2]; dsimp
    constructor; and_intros
    · rfl
    · solve_by_elim [AssocList.EqExt_append]
    · solve_by_elim [AssocList.EqExt_append]

theorem eq_check_well_typed [DecidableEq Typ] {ε : Env Ident Typ} {iexpr iexpr' : ExprLow Ident Typ} :
  iexpr.well_typed ε →
  iexpr.check_eq iexpr' →
  iexpr'.well_typed ε := by
  induction iexpr generalizing iexpr' with
  | base inst typ =>
    intro hwt hchk
    cases iexpr' <;> try contradiction
    constructor
  | connect c e eih =>
    intro hwt hchk
    cases iexpr' <;> try contradiction
    simp [check_eq] at hchk
    repeat with_reducible cases ‹_ ∧ _›; subst_vars
    cases hwt
    constructor; solve_by_elim
    rename_i c e' h1 h2 h3
    obtain ⟨mi, T, hbuild, hf1, hf2⟩ := h3
    obtain ⟨mi', hbuild', heq1, heq2⟩ := check_eq_build_module_interface h1 hbuild
    exists mi', T; and_intros
    · assumption
    · grind [AssocList.EqExt]
    · grind [AssocList.EqExt]
  | product e1 e2 he1 he2 =>
    intro hw hchk
    obtain ⟨hw1, hw2⟩ := hw
    cases iexpr' <;> try contradiction
    simp only [check_eq, Bool.decide_and, Bool.decide_eq_true, Bool.and_eq_true] at hchk
    obtain ⟨hchk1, hchk2⟩ := hchk
    constructor <;> grind

theorem replacement_well_typed [DecidableEq Typ] {ε : Env Ident Typ} {iexpr e_new e_pat : ExprLow Ident Typ} :
  iexpr.well_typed ε →
  (iexpr.force_replace e_pat e_new).2 →
  e_pat.well_typed ε := by
  induction iexpr generalizing e_pat with
  | base inst typ =>
    intro hwt hrep
    dsimp [force_replace] at hrep; split at hrep <;> try contradiction
    cases e_pat <;> try contradiction
    solve_by_elim [eq_check_well_typed]
  | connect c e ih =>
    intro hwt hrep
    dsimp [force_replace] at hrep; split at hrep
    · cases e_pat <;> try contradiction
      rename_i c' e' h'
      solve_by_elim [eq_check_well_typed]
    · apply ih; cases hwt; assumption; assumption
  | product e1 e2 he1 he2 =>
    intro hwt hrep
    dsimp [force_replace] at hrep; split at hrep
    · cases e_pat <;> try contradiction
      rename_i c' e' h'
      solve_by_elim [eq_check_well_typed]
    · simp only [Bool.or_eq_true] at hrep
      cases hrep <;> grind [well_typed]

theorem replacement_well_formed2 [DecidableEq Typ] {ε : Env Ident Typ} {iexpr e_new e_pat : ExprLow Ident Typ} :
  iexpr.well_formed ε →
  (iexpr.force_replace e_pat e_new).2 →
  e_pat.well_formed ε := by
  induction iexpr generalizing e_pat with
  | base inst typ =>
    intro hwt hrep
    dsimp [force_replace] at hrep; split at hrep <;> try contradiction
    cases e_pat <;> try contradiction
    solve_by_elim [check_eq_well_formed]
  | connect c e ih =>
    intro hwt hrep
    dsimp [force_replace] at hrep; split at hrep
    · cases e_pat <;> try contradiction
      rename_i c' e' h'
      solve_by_elim [check_eq_well_formed]
    · apply ih; simp only [well_formed_connect] at *; assumption; assumption
  | product e1 e2 he1 he2 =>
    intro hwt hrep
    dsimp [force_replace] at hrep; split at hrep
    · cases e_pat <;> try contradiction
      rename_i c' e' h'
      solve_by_elim [check_eq_well_formed]
    · simp only [Bool.or_eq_true] at hrep
      cases hrep <;> grind [well_formed]

theorem well_formed_fix_point_opt {wfc : ExprLow Ident Typ → Prop} {wfc' : ExprLow Ident Typ → Bool} {ε} {e' f n} :
    (∀ e e', wfc' e → f e = .some e' → ([e| e', ε ] ⊑ ([e| e, ε ])) ∧ wfc' e') →
    (∀ e e', wfc' e → wfc e' → f e = .some e' → wfc e) →
    wfc' e' →
    wfc (fix_point_opt f e' n) →
    wfc e' := by
-- Proof
  induction n generalizing e' with
  | zero => intros; simp [fix_point_opt] at *; assumption
  | succ n ih =>
    intro he h hwf hwt
    dsimp [fix_point_opt] at *
    split at hwt <;> simp at * <;> grind

theorem wf_foldr' {wfc : ExprLow Ident Typ → Prop} {wfc' : ExprLow Ident Typ → Bool} {ε} {α} {e'} {l : List α} (f : α → ExprLow Ident Typ → ExprLow Ident Typ) :
    (∀ e a, wfc' e → ([e| f a e, ε ] ⊑ ([e| e, ε ])) ∧ wfc' (f a e)) →
    (∀ e a, wfc' e → wfc (f a e) → wfc e) →
    wfc' e' →
    wfc (l.foldr f e') →
    wfc e'
  := by
  induction l with
  | nil => grind
  | cons x xs ih =>
    dsimp at *; intro he' he hwfc' hwfc
    apply ih <;> try assumption
    apply he <;> try assumption
    apply wf_foldr (wfc := λ x => wfc' x = true) <;> assumption

theorem comm_connections_well_typed [DecidableEq Typ] {ε : Env Ident Typ} {iexpr : ExprLow Ident Typ} {l} :
  iexpr.well_formed ε →
  (comm_connections' l iexpr).well_typed ε →
  iexpr.well_typed ε := by
  unfold comm_connections' comm_connection'
  intro hwf hwt; apply wf_foldr' <;> try assumption
  intros; and_intros
  apply refines_fix_point_opt1 (wfc := λ x => well_formed ε x)
  intros; and_intros
  apply refines_comm_connection'_ <;> assumption
  apply wf_comm_connection'_ <;> assumption
  assumption
  apply wf_fix_point_opt (wfc := λ x => well_formed ε x)
  intros; apply wf_comm_connection'_ <;> assumption
  assumption
  intros; apply well_formed_fix_point_opt <;> try assumption
  intros; and_intros
  apply refines_comm_connection'_ <;> assumption
  apply wf_comm_connection'_ <;> assumption
  intros; apply well_typed_comm_connection'_ <;> try assumption

theorem renamePorts_well_typed [DecidableEq Typ] {ε : Env Ident Typ} {iexpr e : ExprLow Ident Typ} {l} :
  iexpr.well_formed ε →
  iexpr.renamePorts l = some e →
  e.well_typed ε →
  iexpr.well_typed ε := by
  induction iexpr generalizing e with
  | base inst typ => intros; constructor
  | connect c iexpr ihe =>
    intro hwf hrename hwt
    obtain ⟨iexpr', hmap, hconn⟩ := mapPorts2_unfold_connect hrename; subst_vars
    obtain ⟨hwt1, mi, T, hbuild, hf1, hf2⟩ := hwt
    dsimp [well_typed]; and_intros; solve_by_elim
    dsimp at *
    obtain ⟨mod, hb1, hb2⟩ := build_module_build_module_interface' hbuild; subst_vars
    replace hwf := well_formed_connect.mp hwf
    obtain ⟨mod', hbuild'⟩ := Option.isSome_iff_exists.mp (well_formed_builds_module hwf)
    exists mod'.2.toModuleInterface, T; and_intros
    · solve_by_elim [build_module_build_module_interface]
    · rw [rename_build_module_eq] at hb1; rotate_left
      apply AssocList.bijectivePortRenaming_bijective; rotate_left
      apply AssocList.bijectivePortRenaming_bijective; rotate_left
      any_goals apply hmap
      apply well_formed_implies_wf_mapping; assumption
      apply well_formed_implies_wf_locally; assumption
      rw [hbuild'] at hb1
      dsimp [Sigma.map] at hb1; cases hb1
      dsimp [Module.toModuleInterface] at hf1 hf2
      rw [mapPorts2_mapKey_inputs] at hf1
      rw [AssocList.find?_mapVal] at hf1
      rw [AssocList.mapKey_find?] at hf1
      dsimp [Module.toModuleInterface]
      rw [AssocList.find?_mapVal]; assumption
      apply AssocList.bijectivePortRenaming_bijective.injective
    · rw [rename_build_module_eq] at hb1; rotate_left
      apply AssocList.bijectivePortRenaming_bijective; rotate_left
      apply AssocList.bijectivePortRenaming_bijective; rotate_left
      any_goals apply hmap
      apply well_formed_implies_wf_mapping; assumption
      apply well_formed_implies_wf_locally; assumption
      rw [hbuild'] at hb1
      dsimp [Sigma.map] at hb1; cases hb1
      dsimp [Module.toModuleInterface] at hf1 hf2
      rw [mapPorts2_mapKey_outputs] at hf2
      rw [AssocList.find?_mapVal] at hf2
      rw [AssocList.mapKey_find?] at hf2
      dsimp [Module.toModuleInterface]
      rw [AssocList.find?_mapVal]; assumption
      apply AssocList.bijectivePortRenaming_bijective.injective
  | product e1 e2 he1 he2 =>
    intro hwf hrename hwt
    obtain ⟨iexpr1', iexpr2', hmap, h1, h2⟩ := mapPorts2_unfold_product hrename; subst_vars
    obtain ⟨hwt1, hwt2⟩ := hwt
    obtain ⟨hwf1, hwf2⟩ := well_formed_product.mp hwf
    dsimp [well_typed] at *; and_intros <;> solve_by_elim

theorem renamePorts_well_typed2' [DecidableEq Typ] {ε : Env Ident Typ} {iexpr e : ExprLow Ident Typ} {l} :
  iexpr.well_formed ε →
  e.well_formed ε →
  iexpr.renamePorts l = some e →
  iexpr.well_typed ε →
  e.well_typed ε := by
  induction iexpr generalizing e with
  | base inst typ => intro hwf1 hwf hre hwt; dsimp [renamePorts] at hre; have := mapPorts2_unfold_base hre; subst_vars; constructor
  | connect c iexpr ihe =>
    intro hwf' hwf hrename hwt
    obtain ⟨iexpr', hmap, hconn⟩ := mapPorts2_unfold_connect hrename; subst_vars
    obtain ⟨hwt1, mi, T, hbuild, hf1, hf2⟩ := hwt
    dsimp [well_typed]; and_intros; solve_by_elim
    dsimp at *
    obtain ⟨mod, hbuild', hb2⟩ := build_module_build_module_interface' hbuild; subst_vars
    replace hwf := well_formed_connect.mp hwf
    obtain ⟨mod', hb1⟩ := Option.isSome_iff_exists.mp (well_formed_builds_module hwf)
    exists mod'.2.toModuleInterface, T; and_intros
    · solve_by_elim [build_module_build_module_interface]
    · rw [rename_build_module_eq] at hb1; rotate_left
      apply AssocList.bijectivePortRenaming_bijective; rotate_left
      apply AssocList.bijectivePortRenaming_bijective; rotate_left
      any_goals apply hmap
      apply well_formed_implies_wf_mapping; assumption
      apply well_formed_implies_wf_locally; assumption
      rw [hbuild'] at hb1
      dsimp [Sigma.map] at hb1; cases hb1
      dsimp [Module.toModuleInterface]
      rw [mapPorts2_mapKey_inputs]
      rw [AssocList.find?_mapVal]
      rw [AssocList.mapKey_find?]
      dsimp [Module.toModuleInterface] at hf1 hf2
      grind [AssocList.find?_mapVal]
      apply AssocList.bijectivePortRenaming_bijective.injective
    · rw [rename_build_module_eq] at hb1; rotate_left
      apply AssocList.bijectivePortRenaming_bijective; rotate_left
      apply AssocList.bijectivePortRenaming_bijective; rotate_left
      any_goals apply hmap
      apply well_formed_implies_wf_mapping; assumption
      apply well_formed_implies_wf_locally; assumption
      rw [hbuild'] at hb1
      dsimp [Sigma.map] at hb1; cases hb1
      dsimp [Module.toModuleInterface]
      rw [mapPorts2_mapKey_outputs]
      rw [AssocList.find?_mapVal]
      rw [AssocList.mapKey_find?]
      dsimp [Module.toModuleInterface] at hf1 hf2
      grind [AssocList.find?_mapVal]
      apply AssocList.bijectivePortRenaming_bijective.injective
  | product e1 e2 he1 he2 =>
    intro hwf' hwf hrename hwt
    obtain ⟨iexpr1', iexpr2', hmap, h1, h2⟩ := mapPorts2_unfold_product hrename; subst_vars
    obtain ⟨hwt1, hwt2⟩ := hwt
    obtain ⟨hwf1, hwf2⟩ := well_formed_product.mp hwf
    obtain ⟨hwf1', hwf2'⟩ := well_formed_product.mp hwf'
    dsimp [well_typed] at *; and_intros <;> solve_by_elim

theorem renamePorts_well_typed2 [DecidableEq Typ] {ε : Env Ident Typ} {iexpr e : ExprLow Ident Typ} {l} :
  iexpr.well_formed ε →
  iexpr.renamePorts l = some e →
  iexpr.well_typed ε →
  e.well_typed ε := by
  intros
  apply renamePorts_well_typed2' <;> try assumption
  apply refines_renamePorts_well_formed <;> assumption

theorem wt_replacement [DecidableEq Typ] {iexpr e_new e_pat : ExprLow Ident Typ} {ε : Env Ident Typ} :
  [e| e_new, ε ] ⊑ [e| e_pat, ε ] →
  iexpr.well_formed ε →
  e_new.well_formed ε →
  iexpr.well_typed ε →
  e_new.well_typed ε →
  (iexpr.replace e_pat e_new).well_typed ε := by
  induction iexpr with
  | base inst typ =>
    intros; dsimp [replace]; split
    assumption; constructor
  | connect c e ih =>
    intro href hwf hwfn hwt hwtn
    dsimp [replace]; split; assumption
    apply well_formed_refines_well_typed2; apply replacement; apply well_formed_implies_wf; assumption
    apply well_formed_implies_wf; assumption
    assumption
    assumption
    apply replacement_well_formed; assumption
    assumption; assumption
    cases hwt; apply ih <;> assumption
  | product e1 e2 he1 he2 =>
    intros
    dsimp [replace]; split; assumption
    cases ‹well_typed _ (ExprLow.product _ _)›
    rw [well_formed_product] at ‹well_formed _ (ExprLow.product _ _)›
    cases ‹_ ∧ _›
    constructor
    apply he1 <;> assumption
    apply he2 <;> assumption

theorem subset_build_module {ε : Env Ident Typ} {ε' : Env Ident Typ} {e : ExprLow Ident Typ} {m} :
  ε.subsetOf ε' → e.build_module' ε = some m → e.build_module' ε' = some m := by
  induction e generalizing m with
  | base inst typ =>
    intro hsub hbuild; dsimp [build_module'] at *
    rw [Option.bind_eq_some'] at hbuild
    obtain ⟨a, h1, h2⟩ := hbuild
    have := hsub _ _ h1
    rw [← h2,this]; rfl
  | connect c e ih =>
    intro hsub hbuild
    dsimp [build_module'] at *
    rw [Option.bind_eq_some'] at hbuild
    obtain ⟨a, h1, h2⟩ := hbuild
    cases h2
    rw [ih] <;> try assumption
    rfl
  | product e1 e2 ih1 ih2 =>
    intro hsub hbuild
    dsimp [build_module'] at *
    rw [Option.bind_eq_some'] at hbuild
    obtain ⟨a, h1, h2⟩ := hbuild
    rw [Option.bind_eq_some'] at h2
    obtain ⟨a', h1', h2'⟩ := h2
    cases h2'
    rw [ih1,ih2] <;> try assumption
    rfl

theorem subset_build_module_interface {ε : Env Ident Typ} {ε' : Env Ident Typ} {e : ExprLow Ident Typ} {m} :
  ε.subsetOf ε' → e.build_module_interface ε = some m → e.build_module_interface ε' = some m := by
  intro hsub hbuild
  obtain ⟨mod, hbuild', heq⟩ := build_module_build_module_interface' hbuild
  subst m
  solve_by_elim [build_module_build_module_interface, subset_build_module]

theorem subset_well_typed {ε : Env Ident Typ} {e : ExprLow Ident Typ} (ε' : Env Ident Typ) :
  ε.subsetOf ε' → e.well_typed ε → e.well_typed ε' := by
  induction e with
  | base => intros; constructor
  | connect c e ih =>
    intro hsub hwt
    dsimp [well_typed] at *
    obtain ⟨wt1, ho⟩ := hwt
    constructor; solve_by_elim
    obtain ⟨mi, T, h1, h2, h3⟩ := ho
    exists mi, T
    and_intros <;> try assumption
    solve_by_elim [subset_build_module_interface]
  | product e1 e2 ih1 ih2 =>
    intro hs ht
    cases ht; constructor <;> solve_by_elim

theorem build_module_connect_foldr {α} {ε : Env Ident Typ} {acc accb} {l : List α} {f : α → Connection Ident}:
  (ExprLow.build_module' ε acc) = .some accb →
  ExprLow.build_module' ε (List.foldr (λ i acc => acc.connect (f i)) acc l)
  = List.foldr (λ i acc => ⟨acc.1, acc.2.connect' (f i).output (f i).input⟩) (ExprLow.build_module ε acc) l := by
    sorry

end ExprLowFoldL

end ExprLow
end Graphiti
