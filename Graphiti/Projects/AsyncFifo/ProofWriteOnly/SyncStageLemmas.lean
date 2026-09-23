/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.ProofWriteOnly.SyncSettle
import Graphiti.Projects.AsyncFifo.components.level5.SyncStage

/-! # `SyncStage`: the lemmas

Facts about the definitions in `components/level5/SyncStage.lean`.  The statement of the
main theorem names none of them. -/

namespace Graphiti.AsyncFifo.SyncStage
open Graphiti.AsyncFifo Graphiti.AsyncFifo.Gates Graphiti.AsyncFifo.Contracts Graphiti.AsyncFifo.Timed
  Graphiti.AsyncFifo.BusReg Graphiti.AsyncFifo.SyncSettle

section NetlistAsModule

/-! ### The circuit reduced to a single module, for the proofs -/

@[drenv] theorem senvS_unpB (lat su stl : Nat) :
    (senvS lat su stl).find? "unpB" = .some ⟨_, unpB lat⟩ := rfl
@[drenv] theorem senvS_unpO (lat su stl : Nat) :
    (senvS lat su stl).find? "unpO" = .some ⟨_, unpO⟩ := rfl
@[drenv] theorem senvS_fork3 (lat su stl : Nat) :
    (senvS lat su stl).find? "fork3" = .some ⟨_, fork3⟩ := rfl
@[drenv] theorem senvS_sdff (lat su stl : Nat) :
    (senvS lat su stl).find? "sdff" = .some ⟨_, settlingDffO su stl⟩ := rfl
@[drenv] theorem senvS_pack3 (lat su stl : Nat) :
    (senvS lat su stl).find? "pack3" = .some ⟨_, pack3⟩ := rfl

variable (lat su stl : Nat)

seal senvS in
def_module stageT : Type :=
  [T| stageLowered, (senvS lat su stl).find? ]
reduction_by
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type,
         ExprLow.build_module, ExprLow.build_module', toString]
  simp only [drenv]
  dsimp

seal senvS in
def_module stageNetlist : StringModule stageT :=
  [e| stageLowered, (senvS lat su stl).find? ]

seal senvS in
/-- The `def_module` above is the `[e| … ]` circuit `components/` names, reduced. -/
theorem stageNetlist_sigma (lat su stl : Nat) :
    (⟨_, stageNetlist lat su stl⟩ : Σ T, StringModule T) = ExprLow.build_module (senvS lat su stl).find? stageLowered := by
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module,
    ExprLow.build_module', toString]
  simp only [drenv]
  dsimp
  dsimp [Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts, Module.mapInputPorts, reduceAssocListfind?]
  simp (disch := decide) only [Batteries.AssocList.bijectivePortRenaming_invert]
  dsimp [Module.product]
  dsimp only [reduceModuleconnect'2]
  dsimp only [reduceEraseAll]
  dsimp; dsimp -failIfUnchanged [reduceAssocListfind?]
  unfold Module.connect''
  dsimp [Module.liftL, Module.liftR, drcomponents]
  rfl

end NetlistAsModule


@[simp] theorem settleOut1_length (su stl : Nat) (clk d osel ojunk : List Bool) :
    (settleOut1 su stl clk d osel ojunk).length = sbitLen clk d osel ojunk := timeline_length _ _

theorem settleOut1_getD {su stl : Nat} {clk d osel ojunk : List Bool} {t : Nat}
    (ht : t < sbitLen clk d osel ojunk) :
    (settleOut1 su stl clk d osel ojunk).getD t false =
      (if (sbitRun su stl clk d osel t).since < stl then ojunk.getD t false
       else (sbitRun su stl clk d osel t).val) := timeline_getD _ ht _

theorem sbitInp_congr {su : Nat} {clk clk' d d' osel osel' : List Bool} (h₁ : clk <+: clk')
    (h₂ : d <+: d') (h₃ : osel <+: osel') {t : Nat} (ht : t < min (min clk.length d.length) osel.length) :
    sbitInp su clk d osel t = sbitInp su clk' d' osel' t := by
  simp only [Nat.lt_min] at ht
  unfold sbitInp
  rw [riseAt_prefix h₁ (by omega), h₂.getD_eq_left (by omega),
    h₂.getD_eq_left (t := t - su - 1) (by omega), h₃.getD_eq_left (by omega)]

theorem sbitRun_congr {su stl : Nat} {clk clk' d d' osel osel' : List Bool} (h₁ : clk <+: clk')
    (h₂ : d <+: d') (h₃ : osel <+: osel') {t : Nat}
    (ht : t ≤ min (min clk.length d.length) osel.length) :
    sbitRun su stl clk d osel t = sbitRun su stl clk' d' osel' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    show sbitStep (sbitRun su stl clk d osel t) (sbitInp su clk d osel t) = _
    rw [ih (by omega), sbitInp_congr h₁ h₂ h₃ (by omega)]
    rfl

theorem settleOut1_mono {su stl : Nat} {clk clk' d d' osel osel' ojunk ojunk' : List Bool}
    (h₁ : clk <+: clk') (h₂ : d <+: d') (h₃ : osel <+: osel') (h₄ : ojunk <+: ojunk') :
    settleOut1 su stl clk d osel ojunk <+: settleOut1 su stl clk' d' osel' ojunk' := by
  have l1 := h₁.length_le; have l2 := h₂.length_le
  have l3 := h₃.length_le; have l4 := h₄.length_le
  apply timeline_mono (by unfold sbitLen; omega)
  intro t ht
  unfold sbitLen at ht
  simp only [Nat.lt_min] at ht
  rw [sbitRun_congr h₁ h₂ h₃ (by simp only [Nat.le_min]; omega), h₄.getD_eq_left (by omega)]

@[simp] theorem selBit_length (i : Nat) (orc : List (Orc 2)) :
    (selBit i orc).length = orc.length := by simp [selBit]
@[simp] theorem junkBit_length (i : Nat) (orc : List (Orc 2)) :
    (junkBit i orc).length = orc.length := by simp [junkBit]

theorem selBit_mono {i : Nat} {orc orc' : List (Orc 2)} (h : orc <+: orc') :
    selBit i orc <+: selBit i orc' := h.map _
theorem junkBit_mono {i : Nat} {orc orc' : List (Orc 2)} (h : orc <+: orc') :
    junkBit i orc <+: junkBit i orc' := h.map _

/-- Beyond the oracle both sides read `0`, so this needs no bound. -/
theorem selBit_getD (i : Nat) (orc : List (Orc 2)) (u : Nat) :
    (selBit i orc).getD u false = (orc.getD u default).sel.getLsbD i := by
  by_cases h : u < orc.length
  · simp [selBit, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [selBit]; omega),
      List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    show false = (0#3).getLsbD i
    simp

theorem junkBit_getD (i : Nat) (orc : List (Orc 2)) (u : Nat) :
    (junkBit i orc).getD u false = (orc.getD u default).junk.getLsbD i := by
  by_cases h : u < orc.length
  · simp [junkBit, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [junkBit]; omega),
      List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    show false = (0#3).getLsbD i
    simp

/-! ### The bus is its bits -/

section Decompose

variable {lat su stl : Nat} {clk : List Bool} {d : List (BitVec 3)} {orc : List (Orc 2)}

/-- The bus-level register of `SyncStage.syncSpec`, bit by bit. -/
theorem syncRun_bit (i : Nat) (t : Nat) :
    (SyncStage.syncRun lat su stl clk d orc t).since
        = (sbitRun su stl clk (bitsOf i (wireOf lat d)) (selBit i orc) t).since ∧
      (SyncStage.syncRun lat su stl clk d orc t).val.getLsbD i
        = (sbitRun su stl clk (bitsOf i (wireOf lat d)) (selBit i orc) t).val := by
  induction t with
  | zero => exact ⟨rfl, by show (0#3).getLsbD i = false; simp⟩
  | succ t ih =>
    show (SyncStage.syncStep (SyncStage.syncRun lat su stl clk d orc t) (SyncStage.syncInp lat su clk d orc t)).since = _ ∧
      (SyncStage.syncStep (SyncStage.syncRun lat su stl clk d orc t) (SyncStage.syncInp lat su clk d orc t)).val.getLsbD i = _
    show _ ∧ _
    have hb : sbitRun su stl clk (bitsOf i (wireOf lat d)) (selBit i orc) (t + 1)
        = sbitStep (sbitRun su stl clk (bitsOf i (wireOf lat d)) (selBit i orc) t)
            (sbitInp su clk (bitsOf i (wireOf lat d)) (selBit i orc) t) := rfl
    rw [hb]
    by_cases hr : riseAt clk t = true
    · rw [syncStep_rise (i := SyncStage.syncInp lat su clk d orc t) hr]
      have hr' : (sbitInp su clk (bitsOf i (wireOf lat d)) (selBit i orc) t).rise = true := hr
      rw [show sbitStep (sbitRun su stl clk (bitsOf i (wireOf lat d)) (selBit i orc) t)
              (sbitInp su clk (bitsOf i (wireOf lat d)) (selBit i orc) t)
            = ⟨if (sbitInp su clk (bitsOf i (wireOf lat d)) (selBit i orc) t).sel
                 then (sbitInp su clk (bitsOf i (wireOf lat d)) (selBit i orc) t).dNew
                 else (sbitInp su clk (bitsOf i (wireOf lat d)) (selBit i orc) t).dOld, 0⟩ by
        unfold sbitStep; rw [if_pos hr']]
      refine ⟨rfl, ?_⟩
      show (mix (orc.getD t default).sel (delayed lat d t) (delayed lat d (t - su - 1))).getLsbD i = _
      rw [mix_getLsbD]
      show (if ((orc.getD t default).sel).getLsbD i then _ else _) = _
      rw [← selBit_getD i orc t, ← wireOf_bit lat d i t, ← wireOf_bit lat d i (t - su - 1)]
      rfl
    · have hr0 : riseAt clk t = false := by simpa using hr
      rw [syncStep_norise (i := SyncStage.syncInp lat su clk d orc t) hr0]
      have hr' : (sbitInp su clk (bitsOf i (wireOf lat d)) (selBit i orc) t).rise = false := hr0
      rw [show sbitStep (sbitRun su stl clk (bitsOf i (wireOf lat d)) (selBit i orc) t)
              (sbitInp su clk (bitsOf i (wireOf lat d)) (selBit i orc) t)
            = ⟨(sbitRun su stl clk (bitsOf i (wireOf lat d)) (selBit i orc) t).val,
               (sbitRun su stl clk (bitsOf i (wireOf lat d)) (selBit i orc) t).since + 1⟩ by
        unfold sbitStep; rw [if_neg (by simp [hr'])]]
      exact ⟨by rw [ih.1], by rw [ih.2]⟩

theorem sbitLen_eq (i : Nat) :
    sbitLen clk (bitsOf i (wireOf lat d)) (selBit i orc) (junkBit i orc)
      = SyncStage.syncLen lat clk d orc := by
  simp only [sbitLen, SyncStage.syncLen, bitsOf_length, wireOf_length, selBit_length, junkBit_length,
    Nat.min_self]

/-- **The bus-level stage is three one-bit stages.**  Nothing of the oracle is left over: `sel`
and `junk` split per bit, and `SyncStage.syncOut` is the three bits packed. -/
theorem syncOut_pack :
    SyncStage.syncOut lat su stl clk d orc =
      pack3Out (settleOut1 su stl clk (bitsOf 0 (wireOf lat d)) (selBit 0 orc) (junkBit 0 orc))
               (settleOut1 su stl clk (bitsOf 1 (wireOf lat d)) (selBit 1 orc) (junkBit 1 orc))
               (settleOut1 su stl clk (bitsOf 2 (wireOf lat d)) (selBit 2 orc) (junkBit 2 orc)) := by
  have hl : ∀ i, (settleOut1 su stl clk (bitsOf i (wireOf lat d)) (selBit i orc)
      (junkBit i orc)).length = SyncStage.syncLen lat clk d orc := by
    intro i; rw [settleOut1_length, sbitLen_eq]
  have hpl : (pack3Out (settleOut1 su stl clk (bitsOf 0 (wireOf lat d)) (selBit 0 orc) (junkBit 0 orc))
      (settleOut1 su stl clk (bitsOf 1 (wireOf lat d)) (selBit 1 orc) (junkBit 1 orc))
      (settleOut1 su stl clk (bitsOf 2 (wireOf lat d)) (selBit 2 orc) (junkBit 2 orc))).length
      = SyncStage.syncLen lat clk d orc := by
    rw [pack3Out_length, hl 0, hl 1, hl 2, Nat.min_self, Nat.min_self]
  have hsl : (SyncStage.syncOut lat su stl clk d orc).length = SyncStage.syncLen lat clk d orc := by
    unfold SyncStage.syncOut; rw [timeline_length]
  refine (((prefix_iff_length_getD (0#3)).mpr ⟨by rw [hsl, hpl], fun t ht => ?_⟩) :
    SyncStage.syncOut lat su stl clk d orc <+: _).eq_of_length (by rw [hsl, hpl])
  rw [hsl] at ht
  unfold SyncStage.syncOut
  rw [timeline_getD _ ht, pack3Out_getD (by rw [hl 0, hl 1, hl 2, Nat.min_self, Nat.min_self]; exact ht)]
  have hb : ∀ i, (settleOut1 su stl clk (bitsOf i (wireOf lat d)) (selBit i orc)
        (junkBit i orc)).getD t false =
      (if (SyncStage.syncRun lat su stl clk d orc t).since < stl
       then ((orc.getD t default).junk).getLsbD i
       else ((SyncStage.syncRun lat su stl clk d orc t).val).getLsbD i) := by
    intro i
    rw [settleOut1_getD (by rw [sbitLen_eq]; exact ht), (syncRun_bit (lat := lat) i t).1,
      ← (syncRun_bit (lat := lat) i t).2, junkBit_getD]
  rw [hb 0, hb 1, hb 2]
  by_cases hs : (SyncStage.syncRun lat su stl clk d orc t).since < stl
  · rw [if_pos hs, if_pos hs, if_pos hs, if_pos hs]; exact (bv3_bits _).symm
  · rw [if_neg hs, if_neg hs, if_neg hs, if_neg hs]; exact (bv3_bits _).symm

end Decompose

/-! ### Each bit is a settling flip-flop

`Timed.SettleOut` is the contract `Dff.dffOut_settleOut` proves of the real netlist wherever its
data meets the aperture.  Each of the stage's one-bit primitives satisfies it, whatever the
oracle says --- so the primitive assumes no more than that contract does. -/

theorem settleOut1_lastEdge {su stl : Nat} {clk d osel : List Bool} {e t : Nat}
    (h : LastEdge clk e t) :
    sbitRun su stl clk d osel t =
      ⟨(sbitRun su stl clk d osel (e + 1)).val, t - e - 1⟩ := by
  obtain ⟨het, hre, hno⟩ := h
  induction t with
  | zero => exact absurd het (Nat.not_lt_zero e)
  | succ t ih =>
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ het) with hlt | heq
    · have hr : (sbitInp su clk d osel t).rise = false := hno t hlt (Nat.lt_succ_self t)
      show sbitStep (sbitRun su stl clk d osel t) (sbitInp su clk d osel t) = _
      rw [show sbitStep (sbitRun su stl clk d osel t) (sbitInp su clk d osel t)
            = ⟨(sbitRun su stl clk d osel t).val, (sbitRun su stl clk d osel t).since + 1⟩ by
        unfold sbitStep; rw [if_neg (by simp [hr])]]
      rw [ih hlt (fun e' h1 h2 => hno e' h1 (by lia))]
      show SBit.mk _ _ = SBit.mk _ _
      congr 1
      lia
    · subst heq
      have h0 : (sbitRun su stl clk d osel (e + 1)).since = 0 := by
        show (sbitStep (sbitRun su stl clk d osel e) (sbitInp su clk d osel e)).since = 0
        unfold sbitStep; rw [if_pos (show (sbitInp su clk d osel e).rise = true from hre)]
      have he0 : e + 1 - e - 1 = 0 := by lia
      rw [he0]
      generalize sbitRun su stl clk d osel (e + 1) = r at *
      obtain ⟨val, since⟩ := r
      simp only at h0
      subst h0
      rfl

theorem settleOut1_at_edge {su stl : Nat} {clk d osel : List Bool} {e : Nat}
    (hre : riseAt clk e = true) :
    (sbitRun su stl clk d osel (e + 1)).val =
      (if osel.getD e false then d.getD e false else d.getD (e - su - 1) false) := by
  show (sbitStep (sbitRun su stl clk d osel e) (sbitInp su clk d osel e)).val = _
  unfold sbitStep
  rw [if_pos (show (sbitInp su clk d osel e).rise = true from hre)]
  rfl

theorem sbitRun_noedge {su stl : Nat} {clk d osel : List Bool} {t : Nat} (h : NoEdge clk t) :
    sbitRun su stl clk d osel t = ⟨false, stl + t⟩ := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have h' : NoEdge clk t := fun e he => h e (by lia)
    have hr : (sbitInp su clk d osel t).rise = false := h t (Nat.lt_succ_self t)
    show sbitStep (sbitRun su stl clk d osel t) (sbitInp su clk d osel t) = _
    rw [show sbitStep (sbitRun su stl clk d osel t) (sbitInp su clk d osel t)
          = ⟨(sbitRun su stl clk d osel t).val, (sbitRun su stl clk d osel t).since + 1⟩ by
      unfold sbitStep; rw [if_neg (by simp [hr])]]
    rw [ih h']
    rfl

/-- **One settling bit meets `Timed.SettleOut`**, with clk-to-q and settling time `stl + 1`:
nothing is promised while `since < stl`, and from the next instant the bit holds one of the two
values the data showed at the ends of the aperture.  The `+ 1` is the instant of the edge
itself, which `SyncStage.syncOut` counts as settling.

This is the contract `Dff.dffOut_settleOut` proves of the real seven-gate flip-flop wherever its
data is stable over the aperture --- so the primitive assumes no more than that theorem states,
and `Metastability.lean` is the argument that the hypothesis cannot be discharged here. -/
theorem settleOut1_settleOut {su stl : Nat} {clk d osel ojunk : List Bool} :
    SettleOut (stl + 1) su (stl + 1) clk (fun u => d.getD u false) d.length
      (settleOut1 su stl clk d osel ojunk) := by
  have hlen : (settleOut1 su stl clk d osel ojunk).length ≤ min clk.length d.length + 1 := by
    rw [settleOut1_length]; unfold sbitLen; omega
  have hv : ∀ t, t < (settleOut1 su stl clk d osel ojunk).length →
      (settleOut1 su stl clk d osel ojunk).getD t false =
        (if (sbitRun su stl clk d osel t).since < stl then ojunk.getD t false
         else (sbitRun su stl clk d osel t).val) := by
    intro t ht; rw [settleOut1_length] at ht; exact settleOut1_getD ht
  -- past the settling window the bit is the value the edge latched
  have hset : ∀ t e, LastEdge clk e t → e + stl + 1 ≤ t →
      t < (settleOut1 su stl clk d osel ojunk).length →
      (settleOut1 su stl clk d osel ojunk).getD t false =
        (if osel.getD e false then d.getD e false else d.getD (e - su - 1) false) := by
    intro t e he hk ht
    rw [hv t ht, settleOut1_lastEdge he, if_neg (show ¬ (t - e - 1 < stl) by have := he.1; omega),
      settleOut1_at_edge he.2.1]
  refine ⟨⟨hlen, fun t ht => ⟨fun hno => ?_, fun e he hst hk => ?_⟩⟩, fun t ht e he hk => ?_⟩
  · show (settleOut1 su stl clk d osel ojunk).getD t false = false
    rw [hv t ht, sbitRun_noedge hno, if_neg (show ¬ (stl + t < stl) by omega)]
  · show (settleOut1 su stl clk d osel ojunk).getD t false = d.getD e false
    rw [hset t e he (by omega) ht]
    have hd : d.getD (e - su - 1) false = d.getD e false := hst.2 (e - su - 1) (by omega) (by omega)
    by_cases ho : osel.getD e false = true
    · rw [if_pos ho]
    · rw [if_neg ho, hd]
  · have hk1 := he.1
    have hl : e + (stl + 1) < (settleOut1 su stl clk d osel ojunk).length := by omega
    have he' : LastEdge clk e (e + (stl + 1)) :=
      ⟨by omega, he.2.1, fun e' h1 h2 => he.2.2 e' h1 (by omega)⟩
    refine ⟨by rw [hset t e he (by omega) ht, hset (e + (stl + 1)) e he' (by omega) hl], ?_⟩
    rw [hset (e + (stl + 1)) e he' (by omega) hl]
    by_cases ho : osel.getD e false = true
    · exact Or.inl (by rw [if_pos ho])
    · exact Or.inr (by rw [if_neg ho])
variable (lat su stl : Nat)
end Graphiti.AsyncFifo.SyncStage