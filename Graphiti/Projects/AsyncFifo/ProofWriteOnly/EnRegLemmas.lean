/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Core.Graph.ModuleLemmas
import Graphiti.Core.Graph.ModuleReduction
import Graphiti.Core.Graph.ExprHighElaborator
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.Dff
import Graphiti.Projects.AsyncFifo.components.level4.EnReg

/-! # `EnReg`: the lemmas

Facts about the definitions in `components/level4/EnReg.lean`.  The statement of the
main theorem names none of them. -/

namespace Graphiti.AsyncFifo.EnReg
open Graphiti.AsyncFifo Graphiti.AsyncFifo.Gates Graphiti.AsyncFifo.Dff

@[drenv] theorem eenv_fork2 : eenv.find? "fork2" = .some ⟨_, fork2 Bool⟩ := rfl
@[drenv] theorem eenv_fork3 : eenv.find? "fork3" = .some ⟨_, fork3⟩ := rfl
@[drenv] theorem eenv_not1 : eenv.find? "not1" = .some ⟨_, gate1 not⟩ := rfl
@[drenv] theorem eenv_and2 : eenv.find? "and2" = .some ⟨_, gate2 and2⟩ := rfl
@[drenv] theorem eenv_or2 : eenv.find? "or2" = .some ⟨_, gate2 or2⟩ := rfl
@[drenv] theorem eenv_dff : eenv.find? "dff" = .some ⟨_, dffSpec⟩ := rfl
@[drenv] theorem eenv_cut4 : eenv.find? "cut4" = .some ⟨_, cut4⟩ := rfl

seal eenv in
def_module enT : Type :=
  [T| enLowered, eenv.find? ]
reduction_by
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type,
         ExprLow.build_module, ExprLow.build_module', toString]
  simp only [drenv]
  dsimp

seal eenv in
def_module enNetlist : StringModule enT :=
  [e| enLowered, eenv.find? ]


instance : Inhabited EnSt := ⟨⟨false, false, false, false, false, false, false, false, false,
  false, false⟩⟩

theorem enRun_congr {clk clk' en en' dat dat' crn crn' : List Bool} (hc : clk <+: clk')
    (he : en <+: en') (hd : dat <+: dat') (hr : crn <+: crn') {t : Nat}
    (ht : t ≤ enLen clk en dat crn) : enRun clk en dat crn t = enRun clk' en' dat' crn' t := by
  refine run_congr _ _ (fun u hu => ?_) t ht
  unfold enLen at hu
  unfold enInp
  rw [hc.getD_eq_left (by omega), he.getD_eq_left (by omega), hd.getD_eq_left (by omega),
    hr.getD_eq_left (by omega)]

@[simp] theorem enOut_length (clk en dat crn : List Bool) :
    (enOut clk en dat crn).length = enLen clk en dat crn + 1 := timeline_length _ _

theorem enOut_getD (clk en dat crn : List Bool) {t : Nat} (ht : t < enLen clk en dat crn + 1) :
    (enOut clk en dat crn).getD t false = (enRun clk en dat crn t).q := timeline_getD _ ht _

theorem enOut_mono {clk clk' en en' dat dat' crn crn' : List Bool} (hc : clk <+: clk')
    (he : en <+: en') (hd : dat <+: dat') (hr : crn <+: crn') :
    enOut clk en dat crn <+: enOut clk' en' dat' crn' := by
  have := hc.length_le; have := he.length_le; have := hd.length_le; have := hr.length_le
  apply timeline_mono (by unfold enLen; omega)
  intro t ht
  rw [enRun_congr hc he hd hr (by unfold enLen at *; omega)]

/-! ### The cell's stream, and the flip-flop inside it

The cell is sequential and its state includes the flip-flop's, so what it computes is a
fixpoint: the multiplexer's stream `mStream` is read off the combined automaton.  But the
flip-flop inside is the flip-flop (`enRun_ff`), and the cell's output is exactly the
flip-flop's over that stream (`enOut_eq`).  That is what lets the netlist below name
`Dff.dffSpec` as a node instead of repeating its gates, and what lets `EnRegTiming.lean`
inherit the whole timing analysis of `DffTiming.lean`. -/

/-- The multiplexer's stream, as far as the cell's inputs are known. -/
def mStream (clk en dat crn : List Bool) : List Bool :=
  timeline (fun t => (enRun clk en dat crn t).m) (enLen clk en dat crn)

@[simp] theorem mStream_length (clk en dat crn : List Bool) :
    (mStream clk en dat crn).length = enLen clk en dat crn := timeline_length _ _

theorem mStream_getD {clk en dat crn : List Bool} {t : Nat} (ht : t < enLen clk en dat crn) :
    (mStream clk en dat crn).getD t false = (enRun clk en dat crn t).m := timeline_getD _ ht _

theorem dffLen_mStream (clk en dat crn : List Bool) :
    dffLen clk (mStream clk en dat crn) crn = enLen clk en dat crn := by
  simp only [dffLen, mStream_length]
  unfold enLen
  omega

/-- The six flip-flop wires of the cell, as a state of `Dff`'s automaton. -/
def ffOf (s : EnSt) : DffSt := ⟨s.n1, s.n2, s.n3, s.n4, s.n5, s.n6⟩

/-- **The cell's flip-flop is the flip-flop**, driven by the multiplexer's stream.  This is what
lets the cell inherit the whole timing analysis of `DffTiming.lean`. -/
theorem enRun_ff {clk en dat crn : List Bool} {t : Nat} (ht : t ≤ enLen clk en dat crn) :
    ffOf (enRun clk en dat crn t) = dffRun clk (mStream clk en dat crn) crn t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have ht' : t ≤ enLen clk en dat crn := by omega
    have e1 : dffRun clk (mStream clk en dat crn) crn (t + 1) =
        dffStep (dffRun clk (mStream clk en dat crn) crn t)
          (dffInp clk (mStream clk en dat crn) crn t) := rfl
    have e2 : enRun clk en dat crn (t + 1) =
        enStep (enRun clk en dat crn t) (enInp clk en dat crn t) := rfl
    rw [e1, ← ih ht', e2]
    unfold dffInp enInp ffOf dffStep enStep
    rw [mStream_getD (by omega)]

/-- The cell's output is the flip-flop's output over the multiplexer's stream. -/
theorem enOut_eq (clk en dat crn : List Bool) :
    enOut clk en dat crn = dffOut clk (mStream clk en dat crn) crn := by
  refine list_eq_of_getD false ?_ (fun t ht => ?_)
  · simp only [enOut_length, dffOut_length, dffLen_mStream]
  · simp only [enOut_length] at ht
    rw [enOut_getD _ _ _ _ ht, dffOut_getD _ _ _ (by rw [dffLen_mStream]; omega)]
    match t with
    | 0 => rfl
    | u + 1 =>
      show (enStep (enRun clk en dat crn u) (enInp clk en dat crn u)).q = _
      show and2 (enRun clk en dat crn u).n5 (crn.getD u false) = _
      show _ = and2 (dffRun clk (mStream clk en dat crn) crn u).n5 (crn.getD u false)
      rw [← enRun_ff (t := u) (by omega)]
      rfl

instance : MatchInterface enNetlist enSpec := by
  dsimp [enNetlist, enSpec]
  solve_match_interface
end Graphiti.AsyncFifo.EnReg