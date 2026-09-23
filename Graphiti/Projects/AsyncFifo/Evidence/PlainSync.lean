/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.ProofWriteOnly.BusRegTiming

/-!
# Evidence: the plain two-flip-flop synchroniser

The Gray pointer arriving from the other clock domain is sampled by two registers in series:
the first may be sampling a bus that is changing, the second re-samples what the first settled
on.  Both are the three-bit register of `BusReg.lean`, so as a netlist this is only wiring.

What this file does *not* do is relate the netlist to `SyncStage.syncSpec`, and that is not an
omission.  `SyncStage.syncSpec` reads an oracle -- which bits of a metastable sample resolve to the
new value, and what is observed while the first stage settles -- and one might hope the netlist
could discharge the oracle by reading it off its own behaviour.  It cannot, and not for want of
trying: `Metastability.lean` exhibits a run with a clean clock, a released clear and data
glitching inside the aperture for which the netlist oscillates for ever, so there is no instant
after which its output is the value at the edge, the value before the aperture, or any other
constant -- nothing an oracle can name.  `syncNetlist ⊑ SyncStage.syncSpec` is therefore false, and
what is at fault is the model: a deterministic Boolean model has no noise to knock a bistable
off its balance point and no continuum for it to slide down, while a real stage resolves after
a random time with an exponentially decaying tail.  That is an MTBF argument, so the settling
of the first stage stays an assumption --- `SyncStage.settlingDffO` (one clause about one bit)
and `stl < P` are where it is written down.  This file is still the honest account of the *wiring*: two `BusReg` stages in
series, `syncGateOut`, and the second stage, whose data is stable from `stl` instants after an
edge, is an ordinary register of the bank.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Graphiti.AsyncFifo.Sync

open Graphiti.AsyncFifo Graphiti.AsyncFifo.Gates Graphiti.AsyncFifo.Contracts Graphiti.AsyncFifo.Timed Graphiti.AsyncFifo.BusReg

/-- What the two stages report: the second register over the first's output. -/
def syncGateOut (clk : List Bool) (d : List (BitVec 3)) (crn : List Bool) : List (BitVec 3) :=
  busOut clk (busOut clk d crn) crn

/-! ### The netlist -/

def syncGraph := [graphEnv|
    clk [type="io"];
    d [type="io"];
    clrn [type="io"];
    q [type="io"];

    clkF [type="fork2", typeImp=$(⟨_, fork2 Bool⟩)];
    crF [type="fork2", typeImp=$(⟨_, fork2 Bool⟩)];
    s1 [type="busreg", typeImp=$(⟨_, busSpec⟩)];
    s2 [type="busreg", typeImp=$(⟨_, busSpec⟩)];

    clk -> clkF [to="in"];
    d -> s1 [to="d"];
    clrn -> crF [to="in"];

    clkF -> s1 [from="out1", to="clk"];
    clkF -> s2 [from="out2", to="clk"];
    crF -> s1 [from="out1", to="clrn"];
    crF -> s2 [from="out2", to="clrn"];
    s1 -> s2 [from="q", to="d"];

    s2 -> q [from="q"];
  ]

@[drunfold_defs]
def syncLowered := syncGraph.1.lower_TR |>.get rfl

def yenv := syncGraph.2

@[drenv] theorem yenv_fork2 : yenv.find? "fork2" = .some ⟨_, fork2 Bool⟩ := rfl
@[drenv] theorem yenv_busreg : yenv.find? "busreg" = .some ⟨_, busSpec⟩ := rfl

seal yenv in
def_module syncT : Type :=
  [T| syncLowered, yenv.find? ]
reduction_by
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type,
         ExprLow.build_module, ExprLow.build_module', toString]
  simp only [drenv]
  dsimp

seal yenv in
def_module syncNetlist : StringModule syncT :=
  [e| syncLowered, yenv.find? ]

/-! ### The specification -/

/-- The synchroniser as a single block. -/
@[drcomponents]
def syncSpec : StringModule (List Bool × List (BitVec 3) × List Bool × List (BitVec 3)) :=
  { inputs := [ (↑"clk", ⟨List Bool, fun s v s' => s.1 ⊏ v ∧ s' = (v, s.2)⟩)
              , (↑"d", ⟨List (BitVec 3), fun s v s' => s.2.1 ⊏ v ∧ s' = (s.1, v, s.2.2)⟩)
              , (↑"clrn", ⟨List Bool, fun s v s' => s.2.2.1 ⊏ v ∧ s' = (s.1, s.2.1, v, s.2.2.2)⟩)
              ].toAssocList
    outputs := [ (↑"q", ⟨List (BitVec 3), fun s v s' => s.2.2.2 <+: v ∧
                    v <+: syncGateOut s.1 s.2.1 s.2.2.1 ∧ s' = (s.1, s.2.1, s.2.2.1, v)⟩) ].toAssocList
    internals := []
    init_state := fun s => s = ([], [], [], []) }

instance : MatchInterface syncNetlist syncSpec := by
  dsimp [syncNetlist, syncSpec]
  solve_match_interface

/-! ### The netlist, as an index type

Each wire holds a prefix of what drives it.  Here the wires do not all carry the same thing --
the clock and the clear are bits, the data between the stages is a three-bit bus -- so the
invariant is `Netlist.Het`'s, indexed by what each wire carries. -/

open Graphiti.AsyncFifo.Netlist

/-- The five driven wires.  The block's own clock, data and clear are not among them: they are
inputs, closed over by `drv`. -/
inductive W | s1_clk | s1_crn | s2_clk | s2_crn | s2_d
  deriving DecidableEq

/-- What each wire carries. -/
def Ty : W → Type
  | .s2_d => BitVec 3
  | _ => Bool

/-- What drives each wire, and the only place the shape of this netlist is written down: the two
forks hand both stages the block's clock and clear, and the second stage's data is the first
stage's output. -/
def drv (clk crn : List Bool) (d : List (BitVec 3)) : Het.Drv Ty
  | _, .s1_clk | _, .s2_clk => clk
  | _, .s1_crn | _, .s2_crn => crn
  | w, .s2_d => busOut (w .s1_clk) d (w .s1_crn)

theorem drv_mono {clk crn d} : Het.Mono (drv clk crn d) := by
  intro a b h k
  cases k <;> simp only [drv] <;>
    apply_rules [List.prefix_rfl, h, busOut_mono]
theorem drv_env {clk clk' crn crn' : List Bool} {d d' : List (BitVec 3)}
    (hc : clk <+: clk') (hr : crn <+: crn') (hd : d <+: d') (w : Het.Wires Ty) (k : W) :
    drv clk crn d w k <+: drv clk' crn' d' w k := by
  cases k <;> simp only [drv] <;>
    apply_rules [List.prefix_rfl, hc, hd, hr, busOut_mono]
def wires (i : syncT) : Het.Wires Ty
  | .s1_clk => i.2.2.2.1 | .s1_crn => i.2.2.2.2.2.1
  | .s2_clk => i.2.1.1 | .s2_crn => i.2.1.2.2.1 | .s2_d => i.2.1.2.1

/-- The invariant: the wires are well formed, the three inputs the netlist holds are the
specification's, and the second stage's recorded output is what the specification has reported. -/
def ψ (i : syncT) (s : List Bool × List (BitVec 3) × List Bool × List (BitVec 3)) : Prop :=
  Het.Wf (drv s.1 s.2.2.1 s.2.1) (wires i) ∧ i.2.2.1 = s.1 ∧ i.2.2.2.2.1 = s.2.1
    ∧ i.1 = s.2.2.1 ∧ i.2.1.2.2.2 = s.2.2.2

/-- What the second stage reports is a prefix of what the specification says: one `busOut` over
another, which is `syncGateOut`. -/
theorem out_q {clk crn d} {w : Het.Wires Ty} (hw : Het.Wf (drv clk crn d) w) :
    busOut (w .s2_clk) (w .s2_d) (w .s2_crn) <+: syncGateOut clk d crn :=
  busOut_mono (hw .s2_clk)
    ((hw .s2_d).trans (busOut_mono (hw .s1_clk) List.prefix_rfl (hw .s1_crn))) (hw .s2_crn)

/-! ### One tactic for every connection -/

syntax "sync_case" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| sync_case) => `(tactic| (
      obtain ⟨cr, ⟨b_clk, b_d, b_crn, b_qh⟩, ck, ⟨a_clk, a_d, a_crn, a_qh⟩⟩ := i
      obtain ⟨_, ⟨_, _, _, _⟩, _, ⟨_, _, _, _⟩⟩ := mid
      have Hr := Hrule.1 rfl; clear Hrule
      obtain ⟨⟨_, ⟨_, _, _, _⟩, _, ⟨_, _, _, _⟩⟩, out, Hr⟩ := Hr
      simp only [Prod.mk.injEq, and_assoc] at Hr
      repeat' (obtain ⟨hh, Hr⟩ := Hr; try subst hh)
      obtain ⟨hw, e1, e2, e3, e4⟩ := H
      refine ⟨s, existSR_reflexive, Het.step hw drv_mono ?_ ?_, e1, e2, e3, e4⟩
      · intro j
        cases j <;> dsimp only [wires] <;>
          first | exact List.prefix_rfl | exact (‹_ ⊏ _›).isPrefix
      · intro j
        have hj := hw j
        cases j <;> (try dsimp only [wires, drv] at hj) <;> dsimp only [wires, drv] <;>
          first
            | exact hj
            | exact e1 ▸ List.prefix_rfl
            | exact e3 ▸ List.prefix_rfl
            | (rw [← e2]; assumption)))

theorem syncNetlist_internals_eq : syncNetlist.internals =
    [syncNetlist.internals.getD 0 (fun _ _ => False), syncNetlist.internals.getD 1 (fun _ _ => False), syncNetlist.internals.getD 2 (fun _ _ => False),
     syncNetlist.internals.getD 3 (fun _ _ => False), syncNetlist.internals.getD 4 (fun _ _ => False)] := rfl


/-! ### The specification's own rules -/

section SpecRules
variable (sp : List Bool × List (BitVec 3) × List Bool × List (BitVec 3))

theorem spec_in_clk (v : List Bool) (h : sp.1 ⊏ v) :
    (syncSpec.inputs.getIO ↑"clk").2 sp v (v, sp.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem spec_in_d (v : List (BitVec 3)) (h : sp.2.1 ⊏ v) :
    (syncSpec.inputs.getIO ↑"d").2 sp v (sp.1, v, sp.2.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem spec_in_clrn (v : List Bool) (h : sp.2.2.1 ⊏ v) :
    (syncSpec.inputs.getIO ↑"clrn").2 sp v (sp.1, sp.2.1, v, sp.2.2.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem spec_out_q (v : List (BitVec 3)) (h1 : sp.2.2.2 <+: v)
    (h2 : v <+: syncGateOut sp.1 sp.2.1 sp.2.2.1) :
    (syncSpec.outputs.getIO ↑"q").2 sp v (sp.1, sp.2.1, sp.2.2.1, v) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h1, h2, rfl⟩
end SpecRules

/-! ### The refinement -/

theorem refines_ψ : syncNetlist ⊑_{ψ} syncSpec := by
  intro i s H
  constructor
  · intro ident mid_i v Hrule
    obtain ⟨cr, ⟨b_clk, b_d, b_crn, b_qh⟩, ck, ⟨a_clk, a_d, a_crn, a_qh⟩⟩ := i
    obtain ⟨_, ⟨_, _, _, _⟩, _, ⟨_, _, _, _⟩⟩ := mid_i
    obtain ⟨hw, e1, e2, e3, e4⟩ := H
    case_transition Hcontains : Module.inputs syncNetlist, ident,
      (PortMap.getIO_not_contained_false' Hrule)
    dsimp only [syncNetlist] at Hcontains
    simp at Hcontains
    rcases Hcontains with h | h | h <;> subst h <;>
      rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule <;>
      dsimp only at Hrule <;>
      simp only [Prod.mk.injEq, and_assoc] at Hrule <;>
      obtain ⟨hpre, Hrule⟩ := Hrule <;>
      repeat' (obtain ⟨hh, Hrule⟩ := Hrule; try subst hh)
    all_goals simp only [eq_mp_eq_cast] at hpre
    -- The port's identity is decided by `hpre`'s type; the three proofs are one shape.
    all_goals first
      | exact ⟨_, _, spec_in_clk s _ (by rw [← e1]; exact hpre), existSR_reflexive,
          Het.drv_le hw (drv_env (e1 ▸ hpre.isPrefix) List.prefix_rfl List.prefix_rfl _),
          rfl, e2, e3, e4⟩
      | exact ⟨_, _, spec_in_d s _ (by rw [← e2]; exact hpre), existSR_reflexive,
          Het.drv_le hw (drv_env List.prefix_rfl List.prefix_rfl (e2 ▸ hpre.isPrefix) _),
          e1, rfl, e3, e4⟩
      | exact ⟨_, _, spec_in_clrn s _ (by rw [← e3]; exact hpre), existSR_reflexive,
          Het.drv_le hw (drv_env List.prefix_rfl (e3 ▸ hpre.isPrefix) List.prefix_rfl _),
          e1, e2, rfl, e4⟩
  · intro ident mid_i v Hrule
    obtain ⟨cr, ⟨b_clk, b_d, b_crn, b_qh⟩, ck, ⟨a_clk, a_d, a_crn, a_qh⟩⟩ := i
    obtain ⟨_, ⟨_, _, _, _⟩, _, ⟨_, _, _, _⟩⟩ := mid_i
    obtain ⟨hw, e1, e2, e3, e4⟩ := H
    case_transition Hcontains : Module.outputs syncNetlist, ident,
      (PortMap.getIO_not_contained_false' Hrule)
    dsimp only [syncNetlist] at Hcontains
    simp at Hcontains
    subst Hcontains
    rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule
    dsimp only at Hrule
    simp only [Prod.mk.injEq, and_assoc] at Hrule
    repeat' (obtain ⟨hh, Hrule⟩ := Hrule; try subst hh)
    simp only [eq_mp_eq_cast, cast_self]
    have ho := out_q hw
    dsimp only [wires] at ho
    exact ⟨s, _, existSR_reflexive, spec_out_q s _ (e4 ▸ ‹_›) (‹_ <+: busOut _ _ _›.trans ho),
      hw, e1, e2, e3, rfl⟩
  · intro rule mid Hin Hrule
    rw [syncNetlist_internals_eq] at Hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at Hin
    rcases Hin with h | h | h | h | h
    all_goals (subst h; sync_case)

theorem refines_initial : Module.refines_initial syncNetlist syncSpec ψ := by
  intro i hi
  obtain ⟨cr, ⟨b_clk, b_d, b_crn, b_qh⟩, ck, ⟨a_clk, a_d, a_crn, a_qh⟩⟩ := i
  dsimp only [syncNetlist] at hi
  simp only [Prod.mk.injEq, and_assoc] at hi
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hi
  refine ⟨([], [], [], []), rfl, ?_, rfl, rfl, rfl, rfl⟩
  intro k; cases k <;> exact List.nil_prefix

/-- **The two registers refine the synchroniser's netlist block.** -/
theorem sync_refines : syncNetlist ⊑ syncSpec :=
  ⟨inferInstance, ψ, refines_ψ, refines_initial⟩

end Graphiti.AsyncFifo.Sync
