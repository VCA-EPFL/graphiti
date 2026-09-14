/-
Copyright (c) 2024-2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

module

public import Graphiti.Core.Rewriter

public import Graphiti.Core.Graph.ExprHighLemmas
public import Graphiti.Core.Graph.Environment
public import Graphiti.Core.Graph.WellTyped

@[expose] public section

open Batteries (AssocList)

namespace Graphiti

variable (env_well_formed : Env String (String × Nat) → Prop)

structure WellFormedEnv (ε : FinEnv String (String × Nat)) (max_type : Nat) : Prop where
  h_wf : env_well_formed ε.toEnv
  max_is_max : ε.max_typeD <= max_type

class Environment {n} (lhs : Vector Nat n → ExprLow String (String × Nat)) where
  ε : FinEnv String (String × Nat)
  max_type : Nat
  types : Vector Nat n
  h_wf : WellFormedEnv env_well_formed ε max_type
  h_lhs_wt : (lhs types).well_typed ε.toEnv
  h_lhs_wf : (lhs types).well_formed ε.toEnv

theorem EStateM.bind_eq_ok {ε σ α β} {x : EStateM ε σ α} {f : α → EStateM ε σ β} {s v s'} :
  x.bind f s = .ok v s' →
  ∃ (x_int : α) (s_int : σ),
    x s = .ok x_int s_int ∧ f x_int s_int = .ok v s' := by
  unfold EStateM.bind; split <;> grind

theorem ofOption_eq_ok {ε σ α} {e : ε} {o : Option α} {o' : α} {s s' : σ} :
  ofOption e o s = EStateM.Result.ok o' s' →
  o = o' ∧ s = s' := by
  unfold ofOption
  split <;> (intros h; cases h)
  constructor <;> rfl

theorem liftError_eq_ok {σ α} {o : Except String α} {o' : α} {s s' : σ} :
  liftError o s = EStateM.Result.ok o' s' →
  o = .ok o' ∧ s = s' := by
  unfold liftError; split <;> (intros h; cases h)
  constructor <;> rfl

theorem guard_eq_ok {ε σ} {e : ε} {b : Bool} {o' : Unit} {s s' : σ} :
  EStateM.guard e b s = EStateM.Result.ok o' s' →
  b = true ∧ s = s' := by
  unfold EStateM.guard; split <;> (intros h; cases h)
  subst b; constructor <;> rfl

theorem EStateM.map_eq_ok {ε σ α β} {f : α → β} {o : EStateM ε σ α} {o' : β} {s s' : σ} :
  EStateM.map f o s = .ok o' s' →
  ∃ o'' s'', o s = .ok o'' s'' ∧ s' = s'' ∧ o' = f o'' := by
  unfold EStateM.map; split <;> (intros h; cases h)
  constructor; constructor; and_intros <;> solve | assumption | rfl

theorem higher_correct_products_correct {Ident Typ} {f} {e₂ : ExprLow Ident Typ} {v'} :
  e₂.higher_correct_products f = some v' →
  List.foldr ExprHigh.generate_product none v'.toList = some e₂ := by
  induction e₂ generalizing v' with
  | base => rintro ⟨⟩; rfl
  | connect => rintro ⟨⟩
  | product e₁ e₂ _ ih =>
    cases e₁ <;> cases h : e₂.higher_correct_products f <;>
      simp_all [ExprLow.higher_correct_products, ExprHigh.generate_product, ExprHigh.uncurry, eq_comm (b := v')]

theorem refines_higher_correct_connections {Ident Typ} {f} {e : ExprLow Ident Typ} {e' : ExprHigh Ident Typ} :
  e.higher_correct_connections f = .some e' →
  e'.lower = .some e := by
  induction e generalizing e' with
  | base => rintro ⟨⟩; rfl
  | connect c e ih =>
    cases h : e.higher_correct_connections f <;>
      grind [ExprLow.higher_correct_connections, ExprHigh.lower, ExprHigh.lower']
  | product e₁ e₂ =>
    intro h
    obtain ⟨v, ha, ⟨⟩⟩ := Option.bind_eq_some_iff.mp h
    cases e₁ with
    | base =>
      obtain ⟨v', hv', ⟨⟩⟩ := Option.bind_eq_some_iff.mp ha
      simp [ExprHigh.lower, ExprHigh.lower', higher_correct_products_correct hv', ExprHigh.uncurry]
    | _ => cases ha

theorem higher_correct_eq {Ident Typ} [DecidableEq Ident] [DecidableEq Typ] {f} {e : ExprLow Ident Typ} {e' : ExprHigh Ident Typ} :
  e.higher_correct f = .some e' →
  e'.lower = .some (ExprLow.comm_bases (ExprLow.get_all_products e) e) :=
  refines_higher_correct_connections

theorem refines_higher_correct {Ident Typ} [DecidableEq Ident] [DecidableEq Typ] {f} {ε g} {e : ExprLow Ident Typ} :
  e.higher_correct f = .some g →
  ExprLow.well_formed ε e = true →
  [Ge| g, ε ] ⊑ ([e| e, ε ]) := by
  intro higher hwf
  rw [ExprHigh.build_module_expr, ExprHigh.build_module, ExprHigh.build_module', higher_correct_eq higher]
  grind [ExprLow.refines_comm_bases]

structure VerifiedRewrite {n}
          (pattern : Pattern String (String × Nat) n)
          (rewrite : DefiniteRewrite String (String × Nat))
          (ε : FinEnv String (String × Nat))
where
  ε_ext : FinEnv String (String × Nat)
  ε_ext_wf : env_well_formed ε_ext.toEnv
  ε_independent : Env.independent ε_ext.toEnv ε.toEnv
  rhs_wf : rewrite.output_expr.well_formed ε_ext.toEnv
  rhs_wt : rewrite.output_expr.well_typed ε_ext.toEnv
  lhs_locally_wf : rewrite.input_expr.locally_wf
  /--
  The refinement only has to hold if `rewrite.input_expr` comes from a matched subgraph: `pattern` matched the nodes
  `sub` in `g`, extracting `sub` from `g` produces `g₁`, and `rewrite.input_expr` is weakly α-equivalent to the lowered
  `g₁`.
  -/
  refinement {g sub types g₁ g₂ e_sub mapping} :
    pattern g = .ok (sub, types) →
    g.extract sub = .some (g₁, g₂) →
    g₁.lower = .some e_sub →
    rewrite.input_expr.weak_beq e_sub = .ok mapping →
    [e| rewrite.output_expr, (ε ++ ε_ext).toEnv ] ⊑ [e| rewrite.input_expr, ε.toEnv ]

structure VerifiedConditionalRewrite (rewrite : DefiniteRewrite String (String × Nat)) (ε : FinEnv String (String × Nat)) where
  ε_ext : FinEnv String (String × Nat)
  ε_ext_wf : env_well_formed ε_ext.toEnv
  ε_independent : Env.independent ε_ext.toEnv ε.toEnv
  rhs_wf : rewrite.output_expr.well_formed ε_ext.toEnv
  rhs_wt : rewrite.output_expr.well_typed ε_ext.toEnv
  lhs_locally_wf : rewrite.input_expr.locally_wf
  refinement : [e| rewrite.output_expr, (ε ++ ε_ext).toEnv ] ⊑ [e| rewrite.input_expr, ε.toEnv ]

private theorem run'_bind_ok_iff {ε σ α β} {x : EStateM ε σ α} {f : α → EStateM ε σ β} {s v s'} :
    x.bind f s = .ok v s' ↔ ∃ a s₁, x s = .ok a s₁ ∧ f a s₁ = .ok v s' := by
  unfold EStateM.bind; split <;> grind

private theorem run'_ofOption_ok_iff {ε σ α} {e : ε} {o : Option α} {a : α} {s s' : σ} :
    ofOption e o s = .ok a s' ↔ o = some a ∧ s = s' := by
  cases o <;> simp [ofOption, pure, EStateM.pure, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

private theorem run'_liftError_ok_iff {σ α} {o : Except String α} {a : α} {s s' : σ} :
    liftError o s = .ok a s' ↔ o = .ok a ∧ s = s' := by
  cases o <;> simp [liftError, pure, EStateM.pure, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

private theorem run'_guard_ok_iff {ε σ} {e : ε} {b : Bool} {u : Unit} {s s' : σ} :
    EStateM.guard e b s = .ok u s' ↔ b = true ∧ s = s' := by
  cases b <;> simp [EStateM.guard, pure, EStateM.pure, EStateM.throw]

private theorem run'_runWithState_ok_iff {Ident Typ α} {r : RewriteResultSL α} {a : α}
    {s s' : RewriteState Ident Typ} :
    r.runWithState s = .ok a s' ↔ r = .ok a ∧ s = s' := by
  cases r <;> simp [RewriteResultSL.runWithState]

/--
Inversion of a successful `Rewrite.run'` whose pattern matched `(sub, types)` in a graph `g` that lowers to `g_lower`.
It names the intermediate results of the do-block and keeps the facts that the correctness proofs below rely on;
logging, fresh-name generation and state updates are dropped.
-/
private theorem run'_ok_inversion {Typ} [Repr Typ] [DecidableEq Typ] {g g' : ExprHigh String Typ}
    {rw : Rewrite String Typ} {b st st' sub types g_lower} :
    rw.pattern g = .ok (sub, types) →
    g.lower = some g_lower →
    Rewrite.run' g rw b st = .ok g' st' →
    ∃ g₁ g₂ e_sub bases mapping comb norm e_in e_out' e_out,
      g.extract sub = some (g₁, g₂) ∧
      g₁.lower = some e_sub ∧
      (rw.rewrite types st.fresh_type).input_expr.weak_beq e_sub = .ok mapping ∧
      (rw.rewrite types st.fresh_type).input_expr.renamePorts comb = some e_in ∧
      (rw.rewrite types st.fresh_type).output_expr.renamePorts comb = some e_out' ∧
      e_out'.ensureIOUnmodified norm ∧
      e_out'.renamePorts norm = some e_out ∧
      ((ExprLow.comm_connections' g₁.connections (ExprLow.comm_bases bases g_lower)).force_replace
        (ExprLow.comm_connections' g₁.connections e_in) e_out).2 ∧
      ((ExprLow.comm_connections' g₁.connections (ExprLow.comm_bases bases g_lower)).replace
        (ExprLow.comm_connections' g₁.connections e_in) e_out).higher_correct PortMapping.hashPortMapping
        = some g' := by
  intro hpat hlower h
  simp only [Rewrite.run', bind, run'_bind_ok_iff, run'_ofOption_ok_iff, run'_liftError_ok_iff, run'_guard_ok_iff,
    run'_runWithState_ok_iff, EStateM.get, pure, EStateM.pure, ExprLow.force_replace_eq_replace] at h
  grind

theorem run'_implies_pattern {Typ} [Repr Typ] [DecidableEq Typ] {g b st g' _st' rw}:
  Rewrite.run' (Typ := Typ) g rw b st = .ok g' _st' →
  ∃ out, rw.pattern g = .ok out := by
  intro h
  cases hpat : rw.pattern g <;>
    simp_all [Rewrite.run', bind, EStateM.bind, EStateM.get, RewriteResultSL.runWithState]

/-- The subexpression that `force_replace` found in a normalised well-formed expression is well-formed. -/
private theorem run'_replaced_wf {ε : Env String (String × Nat)} {conns bases}
    {iexpr e_pat e_new : ExprLow String (String × Nat)} :
    iexpr.well_formed ε →
    ((ExprLow.comm_connections' conns (ExprLow.comm_bases bases iexpr)).force_replace
      (ExprLow.comm_connections' conns e_pat) e_new).2 →
    e_pat.well_formed ε := by
  intro hwf hrep
  apply ExprLow.refines_comm_connections'_well_formed2
  apply ExprLow.replacement_well_formed2 _ hrep
  simp [ExprLow.refines_comm_connections'_well_formed, ExprLow.refines_comm_bases_well_formed, hwf]

/-- The subexpression that `force_replace` found in a normalised well-typed expression is well-typed. -/
private theorem run'_replaced_wt {ε : Env String (String × Nat)} {conns bases}
    {iexpr e_pat e_new : ExprLow String (String × Nat)} :
    iexpr.well_formed ε → iexpr.well_typed ε →
    ((ExprLow.comm_connections' conns (ExprLow.comm_bases bases iexpr)).force_replace
      (ExprLow.comm_connections' conns e_pat) e_new).2 →
    e_pat.well_typed ε := by
  intro hwf hwt hrep
  apply ExprLow.comm_connections_well_typed (run'_replaced_wf hwf hrep)
  apply ExprLow.replacement_well_typed _ hrep
  simp [ExprLow.wt_comm_connections2', ExprLow.wt_comm_bases, ExprLow.refines_comm_bases_well_formed, hwf, hwt]

/-- Renaming the ports of a locally well-formed expression reflects well-formedness. -/
private theorem run'_renamePorts_wf_rev {ε : Env String (String × Nat)} {e e' : ExprLow String (String × Nat)} {p} :
    e.locally_wf → e.renamePorts p = some e' → e'.well_formed ε → e.well_formed ε := by
  grind [ExprLow.renamePorts, ExprLow.mapPorts2_well_formed2, AssocList.bijectivePortRenaming_bijective]

theorem run'_implies_wt_lhs {b} {ε_global : FinEnv String (String × Nat)}
  {g g' : ExprHigh String (String × Nat)}
  {e_g : ExprLow String (String × Nat)}
  {st _st'}
  {rw : Rewrite String (String × Nat)}
  {elems types}
  {grph} :
  rw.pattern g = .ok (elems, types) →
  g.lower = some e_g →
  e_g.well_formed ε_global.toEnv →
  e_g.well_typed ε_global.toEnv →
  Rewrite.run' g rw b st = .ok g' _st' →
  grph = (rw.rewrite types st.fresh_type).input_expr →
  grph.locally_wf →
  grph.well_typed ε_global.toEnv := by
  intro hpat hlower _ _ hrun rfl _
  have := run'_ok_inversion hpat hlower hrun
  grind [run'_renamePorts_wf_rev, run'_replaced_wf, run'_replaced_wt, ExprLow.renamePorts_well_typed]

theorem run'_implies_wf_lhs {b} {ε_global : FinEnv String (String × Nat)}
  {g g' : ExprHigh String (String × Nat)}
  {e_g : ExprLow String (String × Nat)}
  {st _st'}
  {rw : Rewrite String (String × Nat)}
  {elems types}
  {grph} :
  rw.pattern g = .ok (elems, types) →
  g.lower = some e_g →
  e_g.well_formed ε_global.toEnv →
  e_g.well_typed ε_global.toEnv →
  Rewrite.run' g rw b st = .ok g' _st' →
  grph = (rw.rewrite types st.fresh_type).input_expr →
  grph.locally_wf →
  grph.well_formed ε_global.toEnv := by
  intro hpat hlower _ _ hrun rfl _
  have := run'_ok_inversion hpat hlower hrun
  grind [run'_renamePorts_wf_rev, run'_replaced_wf]

section RefinementCalc

/-- Refinement between modules with different state types is transitive, which lets `calc` chain refinements. -/
local instance {I J S : Type _} :
    @Trans (Module String I) (Module String J) (Module String S) Module.refines Module.refines Module.refines :=
  ⟨Module.refines_transitive _⟩

/--
The right-hand side of a verified rewrite, renamed and normalised as in `Rewrite.run'`, refines the renamed left-hand
side with canonicalised connections.
-/
private theorem run'_renamed_rhs_refines {ε ε' : Env String (String × Nat)}
    {rw : DefiniteRewrite String (String × Nat)} {comb norm conns} {e_in e_out' e_out : ExprLow String (String × Nat)} :
    ε.subsetOf ε' →
    rw.input_expr.well_formed ε →
    rw.output_expr.well_formed ε' →
    [e| rw.output_expr, ε' ] ⊑ [e| rw.input_expr, ε ] →
    rw.input_expr.renamePorts comb = some e_in →
    rw.output_expr.renamePorts comb = some e_out' →
    e_out'.ensureIOUnmodified norm →
    e_out'.renamePorts norm = some e_out →
    [e| e_out, ε' ] ⊑ [e| ExprLow.comm_connections' conns e_in, ε' ] := by
  intro hsub hin_wf hout_wf href hin hout hio hnorm
  have hout'_wf := ExprLow.refines_renamePorts_well_formed hout hout_wf
  have hin_wf' := ExprLow.refines_subset_well_formed _ hsub hin_wf
  calc [e| e_out, ε' ]
      _ ⊑ [e| e_out', ε' ].renamePorts norm := by grind [ExprLow.refines_renamePorts_2']
      _ = [e| e_out', ε' ] := by grind [ExprLow.ensureIOUnmodified_correct]
      _ ⊑ [e| rw.output_expr, ε' ].renamePorts comb := by grind [ExprLow.refines_renamePorts_2']
      _ ⊑ [e| rw.input_expr, ε ].renamePorts comb := by grind [Module.refines_renamePorts]
      _ ⊑ [e| rw.input_expr, ε' ].renamePorts comb := by
        grind [Module.refines_renamePorts, ExprLow.refines_subset_left]
      _ ⊑ [e| e_in, ε' ] := by grind [ExprLow.refines_renamePorts_1']
      _ ⊑ [e| ExprLow.comm_connections' conns e_in, ε' ] := by
        grind [ExprLow.refines_comm_connections2', ExprLow.refines_renamePorts_well_formed]

/--
A successful verified `Rewrite.run'` replaces `e_pat` by `e_new` in the normalised lowering `iexpr` of `g`, and lifts
the result to `g'`.
-/
private theorem run'_ok_replacement {b} {ε_global : FinEnv String (String × Nat)}
    {g g' : ExprHigh String (String × Nat)} {e_g : ExprLow String (String × Nat)} {st st'}
    {rw : Rewrite String (String × Nat)} {elems types}
    (vrw : VerifiedRewrite env_well_formed rw.pattern (rw.rewrite types st.fresh_type) ε_global) :
    rw.pattern g = .ok (elems, types) →
    g.lower = some e_g →
    e_g.well_formed ε_global.toEnv →
    e_g.well_typed ε_global.toEnv →
    Rewrite.run' g rw b st = .ok g' st' →
    ∃ iexpr e_pat e_new,
      (iexpr.replace e_pat e_new).higher_correct PortMapping.hashPortMapping = some g' ∧
      iexpr.well_formed (ε_global ++ vrw.ε_ext).toEnv ∧ iexpr.well_typed (ε_global ++ vrw.ε_ext).toEnv ∧
      e_new.well_formed (ε_global ++ vrw.ε_ext).toEnv ∧ e_new.well_typed (ε_global ++ vrw.ε_ext).toEnv ∧
      [e| e_new, (ε_global ++ vrw.ε_ext).toEnv ] ⊑ [e| e_pat, (ε_global ++ vrw.ε_ext).toEnv ] ∧
      [e| iexpr, (ε_global ++ vrw.ε_ext).toEnv ] ⊑ [Ge| g, ε_global.toEnv ] := by
  intro hpat hlower hwf hwt hrun
  obtain ⟨g₁, g₂, e_sub, bases, mapping, comb, norm, e_in, e_out', e_out,
    hextract, hlower₁, hbeq, hin, hout, hio, hnorm, hrep, hhigher⟩ := run'_ok_inversion hpat hlower hrun
  have hsub : ε_global.toEnv.subsetOf (ε_global ++ vrw.ε_ext).toEnv := FinEnv.subset_of_union
  have hsub_ext : vrw.ε_ext.toEnv.subsetOf (ε_global ++ vrw.ε_ext).toEnv :=
    FinEnv.independent_subset_of_union (Env.independent_symm vrw.ε_independent)
  have hin_wf := run'_renamePorts_wf_rev vrw.lhs_locally_wf hin (run'_replaced_wf hwf hrep)
  have hout_wf := ExprLow.refines_subset_well_formed _ hsub_ext vrw.rhs_wf
  have hnew := run'_renamed_rhs_refines (conns := g₁.connections) hsub hin_wf hout_wf
    (vrw.refinement hpat hextract hlower₁ hbeq) hin hout hio hnorm
  have hwf' := ExprLow.refines_subset_well_formed _ hsub hwf
  have hiexpr : [e| ExprLow.comm_connections' g₁.connections (ExprLow.comm_bases bases e_g),
      (ε_global ++ vrw.ε_ext).toEnv ] ⊑ [Ge| g, ε_global.toEnv ] :=
    calc _ ⊑ [e| ExprLow.comm_bases bases e_g, (ε_global ++ vrw.ε_ext).toEnv ] := by
          grind [ExprLow.refines_comm_connections', ExprLow.refines_comm_bases_well_formed]
      _ ⊑ [e| e_g, (ε_global ++ vrw.ε_ext).toEnv ] := by grind [ExprLow.refines_comm_bases]
      _ ⊑ [Ge| g, ε_global.toEnv ] := by
        rw [ExprHigh.build_module_expr, ExprHigh.build_module, ExprHigh.build_module', hlower]
        grind [ExprLow.refines_subset_right]
  have := vrw.rhs_wt
  grind [ExprLow.refines_comm_connections'_well_formed, ExprLow.refines_comm_bases_well_formed,
    ExprLow.wt_comm_connections2', ExprLow.wt_comm_bases, ExprLow.subset_well_typed,
    ExprLow.renamePorts_well_typed2, ExprLow.refines_renamePorts_well_formed]

theorem run'_refines {b} {ε_global : FinEnv String (String × Nat)}
  {g g' : ExprHigh String (String × Nat)}
  {e_g : ExprLow String (String × Nat)}
  {st _st'}
  {rw : Rewrite String (String × Nat)}
  {elems types}
  {vrw : VerifiedRewrite env_well_formed rw.pattern (rw.rewrite types st.fresh_type) ε_global}:
  rw.pattern g = .ok (elems, types) →
  g.lower = some e_g →
  e_g.well_formed ε_global.toEnv →
  e_g.well_typed ε_global.toEnv →
  Rewrite.run' g rw b st = .ok g' _st' →
  [Ge| g', (ε_global ++ vrw.ε_ext).toEnv ] ⊑ [Ge| g, ε_global.toEnv ] := by
  intro hpat hlower hwf hwt hrun
  obtain ⟨iexpr, e_pat, e_new, hhigher, hi_wf, -, hn_wf, -, hnew, hiexpr⟩ :=
    run'_ok_replacement _ vrw hpat hlower hwf hwt hrun
  calc [Ge| g', (ε_global ++ vrw.ε_ext).toEnv ]
      _ ⊑ [e| iexpr.replace e_pat e_new, (ε_global ++ vrw.ε_ext).toEnv ] := by
        grind [refines_higher_correct, ExprLow.replacement_well_formed]
      _ ⊑ [e| iexpr, (ε_global ++ vrw.ε_ext).toEnv ] := by
        grind [ExprLow.replacement, ExprLow.well_formed_implies_wf]
      _ ⊑ [Ge| g, ε_global.toEnv ] := hiexpr

/-- info: 'Graphiti.run'_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run'_refines

theorem run'_preserves_well_formed {b} {ε_global : FinEnv String (String × Nat)}
  {g g' : ExprHigh String (String × Nat)}
  {e_g : ExprLow String (String × Nat)}
  {st _st'}
  {rw : Rewrite String (String × Nat)}
  {elems types}
  {vrw : VerifiedRewrite env_well_formed rw.pattern (rw.rewrite types st.fresh_type) ε_global}:
  rw.pattern g = .ok (elems, types) →
  g.lower = some e_g →
  e_g.well_formed ε_global.toEnv →
  e_g.well_typed ε_global.toEnv →
  Rewrite.run' g rw b st = .ok g' _st' →
  ∃ e_g', g'.lower = some e_g' ∧ e_g'.well_formed (ε_global ++ vrw.ε_ext).toEnv := by
  intro hpat hlower hwf hwt hrun
  obtain ⟨_, _, _, hhigher, _⟩ := run'_ok_replacement _ vrw hpat hlower hwf hwt hrun
  have := higher_correct_eq hhigher
  grind [ExprLow.refines_comm_bases_well_formed, ExprLow.replacement_well_formed]

theorem run'_preserves_well_typed {b} {ε_global : FinEnv String (String × Nat)}
  {g g' : ExprHigh String (String × Nat)}
  {e_g : ExprLow String (String × Nat)}
  {st _st'}
  {rw : Rewrite String (String × Nat)}
  {elems types}
  {vrw : VerifiedRewrite env_well_formed rw.pattern (rw.rewrite types st.fresh_type) ε_global}:
  rw.pattern g = .ok (elems, types) →
  g.lower = some e_g →
  e_g.well_formed ε_global.toEnv →
  e_g.well_typed ε_global.toEnv →
  Rewrite.run' g rw b st = .ok g' _st' →
  ∃ e_g', g'.lower = some e_g' ∧ e_g'.well_typed (ε_global ++ vrw.ε_ext).toEnv := by
  intro hpat hlower hwf hwt hrun
  obtain ⟨_, _, _, hhigher, _⟩ := run'_ok_replacement _ vrw hpat hlower hwf hwt hrun
  have := higher_correct_eq hhigher
  grind [ExprLow.wt_comm_bases, ExprLow.refines_comm_bases_well_formed, ExprLow.replacement_well_formed,
    ExprLow.wt_replacement]

end RefinementCalc

end Graphiti
