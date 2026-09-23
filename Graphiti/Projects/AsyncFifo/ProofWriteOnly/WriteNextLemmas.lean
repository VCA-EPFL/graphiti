/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.ProofWriteOnly.Gates
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.NetlistWf
import Graphiti.Projects.AsyncFifo.components.level4.WriteNext

/-! # `WriteNext`: the lemmas

Facts about the definitions in `components/level4/WriteNext.lean`.  The statement of the
main theorem names none of them. -/

namespace Graphiti.AsyncFifo.WriteNext
open Graphiti.AsyncFifo Graphiti.AsyncFifo.Contracts Graphiti.AsyncFifo.Timed Graphiti.AsyncFifo.Gates Gray
open Batteries (AssocList)

section NetlistAsModule

/-! ### The circuit reduced to a single module, for the proofs -/

@[drenv] theorem genv_unpack2 : genv.find? "unpack2" = .some ⟨_, unpack2⟩ := rfl
@[drenv] theorem genv_g1_not : genv.find? "g1_not" = .some ⟨_, gate1 not⟩ := rfl
@[drenv] theorem genv_g2_Bool_and : genv.find? "g2_Bool_and" = .some ⟨_, gate2 Bool.and⟩ := rfl
@[drenv] theorem genv_fork3 : genv.find? "fork3" = .some ⟨_, fork3⟩ := rfl
@[drenv] theorem genv_g2_Bool_xor : genv.find? "g2_Bool_xor" = .some ⟨_, gate2 Bool.xor⟩ := rfl
@[drenv] theorem genv_fork2 : genv.find? "fork2" = .some ⟨_, fork2 Bool⟩ := rfl
@[drenv] theorem genv_fork4 : genv.find? "fork4" = .some ⟨_, fork4⟩ := rfl
@[drenv] theorem genv_g2_xnor : genv.find? "g2_xnor" = .some ⟨_, gate2 (fun a b => a == b)⟩ := rfl
@[drenv] theorem genv_pack2 : genv.find? "pack2" = .some ⟨_, pack2⟩ := rfl

/-- The state of the netlist: the stored inputs of every node, in netlist order. -/
abbrev gateNextT : Type :=
  (List (WSt 2) × List (BitVec 3)) × List Bool × (List Bool × List Bool) × List Bool × List Bool × List Bool × (List Bool × List Bool) × (List Bool × List Bool) × List Bool × (List Bool × List Bool) × (List Bool × List Bool) × (List Bool × List Bool) × List Bool × List Bool × List Bool × (List Bool × List Bool) × (List Bool × List Bool) × List Bool × (List Bool × List Bool) × List Bool × (List Bool × List Bool) × (List Bool × List Bool) × (List Bool × List Bool) × (List Bool × List Bool) × (List Bool × List Bool) × (List Bool × List Bool) × PackSt

set_option maxHeartbeats 4000000 in
seal genv in
def_module gateNext : StringModule gateNextT :=
  [e| gateNextExpr, genv.find? ]

set_option maxHeartbeats 4000000 in
seal genv in
/-- The `def_module` above is the `[e| … ]` circuit `components/` names, reduced. -/
theorem gateNext_sigma :
    (⟨_, gateNext⟩ : Σ T, StringModule T) = ExprLow.build_module genv.find? gateNextExpr := by
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


@[simp] theorem pack2Out_length (s : PackSt) : (pack2Out s).length = packLen s - 1 := timeline_length _ _

theorem pack2Out_getD (s : PackSt) {t : Nat} (ht : t < packLen s - 1) :
    (pack2Out s).getD t default = ⟨⟨bv3 (s.p0.getD t false) (s.p1.getD t false) (s.p2.getD t false), s.fl.getD t false,
      bv3 (s.q0.getD t false) (s.q1.getD t false) (s.q2.getD t false)⟩,
    bv3 (s.g0.getD t false) (s.g1.getD t false) (s.g2.getD t false), s.we.getD t false,
    bv2 (s.a0.getD t false) (s.a1.getD t false), s.dt.getD t false⟩ := timeline_getD _ ht _

theorem pack2Out_mono {s s' : PackSt} (hp0 : s.p0 <+: s'.p0) (hp1 : s.p1 <+: s'.p1) (hp2 : s.p2 <+: s'.p2) (hfl : s.fl <+: s'.fl) (hq0 : s.q0 <+: s'.q0) (hq1 : s.q1 <+: s'.q1) (hq2 : s.q2 <+: s'.q2) (hg0 : s.g0 <+: s'.g0) (hg1 : s.g1 <+: s'.g1) (hg2 : s.g2 <+: s'.g2) (hwe : s.we <+: s'.we) (ha0 : s.a0 <+: s'.a0) (ha1 : s.a1 <+: s'.a1) (hdt : s.dt <+: s'.dt) :
    pack2Out s <+: pack2Out s' := by
  apply timeline_mono (Nat.sub_le_sub_right (min_mono hp0.length_le (min_mono hp1.length_le (min_mono hp2.length_le (min_mono hfl.length_le (min_mono hq0.length_le (min_mono hq1.length_le (min_mono hq2.length_le (min_mono hg0.length_le (min_mono hg1.length_le (min_mono hg2.length_le (min_mono hwe.length_le (min_mono ha0.length_le (min_mono ha1.length_le (hdt.length_le)))))))))))))) 1)
  intro t ht
  have ht2 : t < packLen s := Nat.lt_of_lt_of_le ht (Nat.sub_le _ _)
  simp only [packLen, Nat.lt_min] at ht2
  obtain ⟨t_p0, t_p1, t_p2, t_fl, t_q0, t_q1, t_q2, t_g0, t_g1, t_g2, t_we, t_a0, t_a1, t_dt⟩ := ht2
  rw [hp0.getD_eq_left t_p0, hp1.getD_eq_left t_p1, hp2.getD_eq_left t_p2, hfl.getD_eq_left t_fl, hq0.getD_eq_left t_q0, hq1.getD_eq_left t_q1, hq2.getD_eq_left t_q2, hg0.getD_eq_left t_g0, hg1.getD_eq_left t_g1, hg2.getD_eq_left t_g2, hwe.getD_eq_left t_we, ha0.getD_eq_left t_a0, ha1.getD_eq_left t_a1, hdt.getD_eq_left t_dt]

/-- `pack2Out_mono` stated field by field: callers then unify their wires with the fields
syntactically, instead of unfolding a wire to compare it with a projection. -/
theorem pack2Out_mono' {p0 p0' p1 p1' p2 p2' fl fl' q0 q0' q1 q1' q2 q2' g0 g0' g1 g1' g2 g2' we we' a0 a0' a1 a1' dt dt' : List Bool}
    (hp0 : p0 <+: p0') (hp1 : p1 <+: p1') (hp2 : p2 <+: p2') (hfl : fl <+: fl') (hq0 : q0 <+: q0') (hq1 : q1 <+: q1') (hq2 : q2 <+: q2') (hg0 : g0 <+: g0') (hg1 : g1 <+: g1') (hg2 : g2 <+: g2') (hwe : we <+: we') (ha0 : a0 <+: a0') (ha1 : a1 <+: a1') (hdt : dt <+: dt') :
    pack2Out ⟨p0, p1, p2, fl, q0, q1, q2, g0, g1, g2, we, a0, a1, dt⟩ <+: pack2Out ⟨p0', p1', p2', fl', q0', q1', q2', g0', g1', g2', we', a0', a1', dt'⟩ :=
  pack2Out_mono hp0 hp1 hp2 hfl hq0 hq1 hq2 hg0 hg1 hg2 hwe ha0 ha1 hdt

seal genv in
def_module gateNextT' : Type :=
  [T| gateNextExpr, genv.find? ]
reduction_by
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type,
         ExprLow.build_module, ExprLow.build_module', toString]
  simp only [drenv]
  dsimp

/-- A compiled check, not a step of any proof: the type `def_module` reduces the graph to
is the one written by hand above, so the hand-written `abbrev` — which every statement below
names — cannot drift from the graph. -/
theorem gateNextT_eq : gateNextT' = gateNextT := rfl

/-! ### The wires as functions of the block's inputs -/

/-- Primary inputs at one instant, as `WriteNext.nextDep` produces them. -/
abbrev Inp := WSt 2 × Bool × Bool × BitVec 3

def F_inc : Inp → Bool := fun i => i.2.1
def F_data : Inp → Bool := fun i => i.2.2.1
def F_unp_p0 : Inp → Bool := fun i => i.1.ptr.getLsbD 0
def F_unp_p1 : Inp → Bool := fun i => i.1.ptr.getLsbD 1
def F_unp_p2 : Inp → Bool := fun i => i.1.ptr.getLsbD 2
def F_unp_fl : Inp → Bool := fun i => i.1.full
def F_unp_q20 : Inp → Bool := fun i => i.1.q2.getLsbD 0
def F_unp_q21 : Inp → Bool := fun i => i.1.q2.getLsbD 1
def F_unp_q22 : Inp → Bool := fun i => i.1.q2.getLsbD 2
def F_unp_q10 : Inp → Bool := fun i => i.2.2.2.getLsbD 0
def F_unp_q11 : Inp → Bool := fun i => i.2.2.2.getLsbD 1
def F_unp_q12 : Inp → Bool := fun i => i.2.2.2.getLsbD 2
def F_nfl : Inp → Bool := fun i => not (F_unp_fl i)
def F_ok : Inp → Bool := fun i => Bool.and (F_inc i) (F_nfl i)
def F_xp0 : Inp → Bool := fun i => Bool.xor (F_unp_p0 i) (F_ok i)
def F_cp0 : Inp → Bool := fun i => Bool.and (F_unp_p0 i) (F_ok i)
def F_xp1 : Inp → Bool := fun i => Bool.xor (F_unp_p1 i) (F_cp0 i)
def F_cp1 : Inp → Bool := fun i => Bool.and (F_unp_p1 i) (F_cp0 i)
def F_xp2 : Inp → Bool := fun i => Bool.xor (F_unp_p2 i) (F_cp1 i)
def F_xg0 : Inp → Bool := fun i => Bool.xor (F_xp1 i) (F_xp0 i)
def F_xg1 : Inp → Bool := fun i => Bool.xor (F_xp2 i) (F_xp1 i)
def F_xu1 : Inp → Bool := fun i => Bool.xor (F_unp_q22 i) (F_unp_q21 i)
def F_xu0 : Inp → Bool := fun i => Bool.xor (F_xu1 i) (F_unp_q20 i)
def F_xe2 : Inp → Bool := fun i => Bool.xor (F_xp2 i) (F_unp_q22 i)
def F_xe1 : Inp → Bool := fun i => (fun a b => a == b) (F_xp1 i) (F_xu1 i)
def F_xe0 : Inp → Bool := fun i => (fun a b => a == b) (F_xp0 i) (F_xu0 i)
def F_ae : Inp → Bool := fun i => Bool.and (F_xe2 i) (F_xe1 i)
def F_af : Inp → Bool := fun i => Bool.and (F_ae i) (F_xe0 i)

def W_unp_p0 (s : WriteNext.NextSt Bool 2) : List Bool := List.map (fun x => x.ptr.getLsbD 0) s.st
def W_unp_p1 (s : WriteNext.NextSt Bool 2) : List Bool := List.map (fun x => x.ptr.getLsbD 1) s.st
def W_unp_p2 (s : WriteNext.NextSt Bool 2) : List Bool := List.map (fun x => x.ptr.getLsbD 2) s.st
def W_unp_fl (s : WriteNext.NextSt Bool 2) : List Bool := List.map (fun x => x.full) s.st
def W_unp_q20 (s : WriteNext.NextSt Bool 2) : List Bool := List.map (fun x => x.q2.getLsbD 0) s.st
def W_unp_q21 (s : WriteNext.NextSt Bool 2) : List Bool := List.map (fun x => x.q2.getLsbD 1) s.st
def W_unp_q22 (s : WriteNext.NextSt Bool 2) : List Bool := List.map (fun x => x.q2.getLsbD 2) s.st
def W_unp_q10 (s : WriteNext.NextSt Bool 2) : List Bool := List.map (fun x => x.getLsbD 0) s.q1
def W_unp_q11 (s : WriteNext.NextSt Bool 2) : List Bool := List.map (fun x => x.getLsbD 1) s.q1
def W_unp_q12 (s : WriteNext.NextSt Bool 2) : List Bool := List.map (fun x => x.getLsbD 2) s.q1
def W_nfl (s : WriteNext.NextSt Bool 2) : List Bool := gate1Out not (W_unp_fl s)
def W_ok (s : WriteNext.NextSt Bool 2) : List Bool := gateOut Bool.and (s.inc) (W_nfl s)
def W_xp0 (s : WriteNext.NextSt Bool 2) : List Bool := gateOut Bool.xor (W_unp_p0 s) (W_ok s)
def W_cp0 (s : WriteNext.NextSt Bool 2) : List Bool := gateOut Bool.and (W_unp_p0 s) (W_ok s)
def W_xp1 (s : WriteNext.NextSt Bool 2) : List Bool := gateOut Bool.xor (W_unp_p1 s) (W_cp0 s)
def W_cp1 (s : WriteNext.NextSt Bool 2) : List Bool := gateOut Bool.and (W_unp_p1 s) (W_cp0 s)
def W_xp2 (s : WriteNext.NextSt Bool 2) : List Bool := gateOut Bool.xor (W_unp_p2 s) (W_cp1 s)
def W_xg0 (s : WriteNext.NextSt Bool 2) : List Bool := gateOut Bool.xor (W_xp1 s) (W_xp0 s)
def W_xg1 (s : WriteNext.NextSt Bool 2) : List Bool := gateOut Bool.xor (W_xp2 s) (W_xp1 s)
def W_xu1 (s : WriteNext.NextSt Bool 2) : List Bool := gateOut Bool.xor (W_unp_q22 s) (W_unp_q21 s)
def W_xu0 (s : WriteNext.NextSt Bool 2) : List Bool := gateOut Bool.xor (W_xu1 s) (W_unp_q20 s)
def W_xe2 (s : WriteNext.NextSt Bool 2) : List Bool := gateOut Bool.xor (W_xp2 s) (W_unp_q22 s)
def W_xe1 (s : WriteNext.NextSt Bool 2) : List Bool := gateOut (fun a b => a == b) (W_xp1 s) (W_xu1 s)
def W_xe0 (s : WriteNext.NextSt Bool 2) : List Bool := gateOut (fun a b => a == b) (W_xp0 s) (W_xu0 s)
def W_ae (s : WriteNext.NextSt Bool 2) : List Bool := gateOut Bool.and (W_xe2 s) (W_xe1 s)
def W_af (s : WriteNext.NextSt Bool 2) : List Bool := gateOut Bool.and (W_ae s) (W_xe0 s)

/-- The packer's stored inputs when every wire carries its full stream. -/
def Wpk (s : WriteNext.NextSt Bool 2) : PackSt := ⟨W_xp0 s, W_xp1 s, W_xp2 s, W_af s, W_unp_q10 s, W_unp_q11 s, W_unp_q12 s, W_xg0 s, W_xg1 s, W_xp2 s, W_ok s, W_unp_p0 s, W_unp_p1 s, s.data⟩
def W_pack (s : WriteNext.NextSt Bool 2) : List (WNext Bool 2) := pack2Out (Wpk s)

/-! ### Monotonicity of the wires in the inputs -/

variable {s s' : WriteNext.NextSt Bool 2}

theorem W_unp_p0_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.data <+: s'.data) (h4 : s.q1 <+: s'.q1) :
    W_unp_p0 s <+: W_unp_p0 s' := h1.map _
theorem W_unp_p1_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.data <+: s'.data) (h4 : s.q1 <+: s'.q1) :
    W_unp_p1 s <+: W_unp_p1 s' := h1.map _
theorem W_unp_p2_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.data <+: s'.data) (h4 : s.q1 <+: s'.q1) :
    W_unp_p2 s <+: W_unp_p2 s' := h1.map _
theorem W_unp_fl_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.data <+: s'.data) (h4 : s.q1 <+: s'.q1) :
    W_unp_fl s <+: W_unp_fl s' := h1.map _
theorem W_unp_q20_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.data <+: s'.data) (h4 : s.q1 <+: s'.q1) :
    W_unp_q20 s <+: W_unp_q20 s' := h1.map _
theorem W_unp_q21_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.data <+: s'.data) (h4 : s.q1 <+: s'.q1) :
    W_unp_q21 s <+: W_unp_q21 s' := h1.map _
theorem W_unp_q22_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.data <+: s'.data) (h4 : s.q1 <+: s'.q1) :
    W_unp_q22 s <+: W_unp_q22 s' := h1.map _
theorem W_unp_q10_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.data <+: s'.data) (h4 : s.q1 <+: s'.q1) :
    W_unp_q10 s <+: W_unp_q10 s' := h4.map _
theorem W_unp_q11_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.data <+: s'.data) (h4 : s.q1 <+: s'.q1) :
    W_unp_q11 s <+: W_unp_q11 s' := h4.map _
theorem W_unp_q12_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.data <+: s'.data) (h4 : s.q1 <+: s'.q1) :
    W_unp_q12 s <+: W_unp_q12 s' := h4.map _
theorem W_nfl_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.data <+: s'.data) (h4 : s.q1 <+: s'.q1) :
    W_nfl s <+: W_nfl s' := gate1Out_mono _ (W_unp_fl_mono h1 h2 h3 h4)
theorem W_ok_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.data <+: s'.data) (h4 : s.q1 <+: s'.q1) :
    W_ok s <+: W_ok s' := gateOut_mono _ h2 (W_nfl_mono h1 h2 h3 h4)
theorem W_xp0_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.data <+: s'.data) (h4 : s.q1 <+: s'.q1) :
    W_xp0 s <+: W_xp0 s' := gateOut_mono _ (W_unp_p0_mono h1 h2 h3 h4) (W_ok_mono h1 h2 h3 h4)
theorem W_cp0_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.data <+: s'.data) (h4 : s.q1 <+: s'.q1) :
    W_cp0 s <+: W_cp0 s' := gateOut_mono _ (W_unp_p0_mono h1 h2 h3 h4) (W_ok_mono h1 h2 h3 h4)
theorem W_xp1_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.data <+: s'.data) (h4 : s.q1 <+: s'.q1) :
    W_xp1 s <+: W_xp1 s' := gateOut_mono _ (W_unp_p1_mono h1 h2 h3 h4) (W_cp0_mono h1 h2 h3 h4)
theorem W_cp1_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.data <+: s'.data) (h4 : s.q1 <+: s'.q1) :
    W_cp1 s <+: W_cp1 s' := gateOut_mono _ (W_unp_p1_mono h1 h2 h3 h4) (W_cp0_mono h1 h2 h3 h4)
theorem W_xp2_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.data <+: s'.data) (h4 : s.q1 <+: s'.q1) :
    W_xp2 s <+: W_xp2 s' := gateOut_mono _ (W_unp_p2_mono h1 h2 h3 h4) (W_cp1_mono h1 h2 h3 h4)
theorem W_xg0_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.data <+: s'.data) (h4 : s.q1 <+: s'.q1) :
    W_xg0 s <+: W_xg0 s' := gateOut_mono _ (W_xp1_mono h1 h2 h3 h4) (W_xp0_mono h1 h2 h3 h4)
theorem W_xg1_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.data <+: s'.data) (h4 : s.q1 <+: s'.q1) :
    W_xg1 s <+: W_xg1 s' := gateOut_mono _ (W_xp2_mono h1 h2 h3 h4) (W_xp1_mono h1 h2 h3 h4)
theorem W_xu1_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.data <+: s'.data) (h4 : s.q1 <+: s'.q1) :
    W_xu1 s <+: W_xu1 s' := gateOut_mono _ (W_unp_q22_mono h1 h2 h3 h4) (W_unp_q21_mono h1 h2 h3 h4)
theorem W_xu0_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.data <+: s'.data) (h4 : s.q1 <+: s'.q1) :
    W_xu0 s <+: W_xu0 s' := gateOut_mono _ (W_xu1_mono h1 h2 h3 h4) (W_unp_q20_mono h1 h2 h3 h4)
theorem W_xe2_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.data <+: s'.data) (h4 : s.q1 <+: s'.q1) :
    W_xe2 s <+: W_xe2 s' := gateOut_mono _ (W_xp2_mono h1 h2 h3 h4) (W_unp_q22_mono h1 h2 h3 h4)
theorem W_xe1_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.data <+: s'.data) (h4 : s.q1 <+: s'.q1) :
    W_xe1 s <+: W_xe1 s' := gateOut_mono _ (W_xp1_mono h1 h2 h3 h4) (W_xu1_mono h1 h2 h3 h4)
theorem W_xe0_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.data <+: s'.data) (h4 : s.q1 <+: s'.q1) :
    W_xe0 s <+: W_xe0 s' := gateOut_mono _ (W_xp0_mono h1 h2 h3 h4) (W_xu0_mono h1 h2 h3 h4)
theorem W_ae_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.data <+: s'.data) (h4 : s.q1 <+: s'.q1) :
    W_ae s <+: W_ae s' := gateOut_mono _ (W_xe2_mono h1 h2 h3 h4) (W_xe1_mono h1 h2 h3 h4)
theorem W_af_mono (h1 : s.st <+: s'.st) (h2 : s.inc <+: s'.inc) (h3 : s.data <+: s'.data) (h4 : s.q1 <+: s'.q1) :
    W_af s <+: W_af s' := gateOut_mono _ (W_ae_mono h1 h2 h3 h4) (W_xe0_mono h1 h2 h3 h4)

/-! ### Combinational contracts of the wires -/

variable (s : WriteNext.NextSt Bool 2)

theorem C_inc : Comb 0 0 F_inc (WriteNext.nextDep Bool s) s.inc := Comb.input (fun t _ => rfl)
theorem C_data : Comb 0 0 F_data (WriteNext.nextDep Bool s) s.data := Comb.input (fun t _ => rfl)
theorem C_unp_p0 : Comb 0 0 F_unp_p0 (WriteNext.nextDep Bool s) (W_unp_p0 s) :=
  Comb.input (fun t ht => by unfold W_unp_p0 at ht ⊢; rw [getD_map_lt _ _ (by simpa using ht)]; rfl)
theorem C_unp_p1 : Comb 0 0 F_unp_p1 (WriteNext.nextDep Bool s) (W_unp_p1 s) :=
  Comb.input (fun t ht => by unfold W_unp_p1 at ht ⊢; rw [getD_map_lt _ _ (by simpa using ht)]; rfl)
theorem C_unp_p2 : Comb 0 0 F_unp_p2 (WriteNext.nextDep Bool s) (W_unp_p2 s) :=
  Comb.input (fun t ht => by unfold W_unp_p2 at ht ⊢; rw [getD_map_lt _ _ (by simpa using ht)]; rfl)
theorem C_unp_fl : Comb 0 0 F_unp_fl (WriteNext.nextDep Bool s) (W_unp_fl s) :=
  Comb.input (fun t ht => by unfold W_unp_fl at ht ⊢; rw [getD_map_lt _ _ (by simpa using ht)]; rfl)
theorem C_unp_q20 : Comb 0 0 F_unp_q20 (WriteNext.nextDep Bool s) (W_unp_q20 s) :=
  Comb.input (fun t ht => by unfold W_unp_q20 at ht ⊢; rw [getD_map_lt _ _ (by simpa using ht)]; rfl)
theorem C_unp_q21 : Comb 0 0 F_unp_q21 (WriteNext.nextDep Bool s) (W_unp_q21 s) :=
  Comb.input (fun t ht => by unfold W_unp_q21 at ht ⊢; rw [getD_map_lt _ _ (by simpa using ht)]; rfl)
theorem C_unp_q22 : Comb 0 0 F_unp_q22 (WriteNext.nextDep Bool s) (W_unp_q22 s) :=
  Comb.input (fun t ht => by unfold W_unp_q22 at ht ⊢; rw [getD_map_lt _ _ (by simpa using ht)]; rfl)
theorem C_unp_q10 : Comb 0 0 F_unp_q10 (WriteNext.nextDep Bool s) (W_unp_q10 s) :=
  Comb.input (fun t ht => by unfold W_unp_q10 at ht ⊢; rw [getD_map_lt _ _ (by simpa using ht)]; rfl)
theorem C_unp_q11 : Comb 0 0 F_unp_q11 (WriteNext.nextDep Bool s) (W_unp_q11 s) :=
  Comb.input (fun t ht => by unfold W_unp_q11 at ht ⊢; rw [getD_map_lt _ _ (by simpa using ht)]; rfl)
theorem C_unp_q12 : Comb 0 0 F_unp_q12 (WriteNext.nextDep Bool s) (W_unp_q12 s) :=
  Comb.input (fun t ht => by unfold W_unp_q12 at ht ⊢; rw [getD_map_lt _ _ (by simpa using ht)]; rfl)
theorem C_nfl : Comb 1 1 F_nfl (WriteNext.nextDep Bool s) (W_nfl s) :=
  Comb.gate1 not (C_unp_fl s)
theorem C_ok : Comb 1 2 F_ok (WriteNext.nextDep Bool s) (W_ok s) :=
  Comb.gate2 Bool.and (C_inc s) (C_nfl s)
theorem C_xp0 : Comb 1 3 F_xp0 (WriteNext.nextDep Bool s) (W_xp0 s) :=
  Comb.gate2 Bool.xor (C_unp_p0 s) (C_ok s)
theorem C_cp0 : Comb 1 3 F_cp0 (WriteNext.nextDep Bool s) (W_cp0 s) :=
  Comb.gate2 Bool.and (C_unp_p0 s) (C_ok s)
theorem C_xp1 : Comb 1 4 F_xp1 (WriteNext.nextDep Bool s) (W_xp1 s) :=
  Comb.gate2 Bool.xor (C_unp_p1 s) (C_cp0 s)
theorem C_cp1 : Comb 1 4 F_cp1 (WriteNext.nextDep Bool s) (W_cp1 s) :=
  Comb.gate2 Bool.and (C_unp_p1 s) (C_cp0 s)
theorem C_xp2 : Comb 1 5 F_xp2 (WriteNext.nextDep Bool s) (W_xp2 s) :=
  Comb.gate2 Bool.xor (C_unp_p2 s) (C_cp1 s)
theorem C_xg0 : Comb 2 5 F_xg0 (WriteNext.nextDep Bool s) (W_xg0 s) :=
  Comb.gate2 Bool.xor (C_xp1 s) (C_xp0 s)
theorem C_xg1 : Comb 2 6 F_xg1 (WriteNext.nextDep Bool s) (W_xg1 s) :=
  Comb.gate2 Bool.xor (C_xp2 s) (C_xp1 s)
theorem C_xu1 : Comb 1 1 F_xu1 (WriteNext.nextDep Bool s) (W_xu1 s) :=
  Comb.gate2 Bool.xor (C_unp_q22 s) (C_unp_q21 s)
theorem C_xu0 : Comb 1 2 F_xu0 (WriteNext.nextDep Bool s) (W_xu0 s) :=
  Comb.gate2 Bool.xor (C_xu1 s) (C_unp_q20 s)
theorem C_xe2 : Comb 1 6 F_xe2 (WriteNext.nextDep Bool s) (W_xe2 s) :=
  Comb.gate2 Bool.xor (C_xp2 s) (C_unp_q22 s)
theorem C_xe1 : Comb 2 5 F_xe1 (WriteNext.nextDep Bool s) (W_xe1 s) :=
  Comb.gate2 (fun a b => a == b) (C_xp1 s) (C_xu1 s)
theorem C_xe0 : Comb 2 4 F_xe0 (WriteNext.nextDep Bool s) (W_xe0 s) :=
  Comb.gate2 (fun a b => a == b) (C_xp0 s) (C_xu0 s)
theorem C_ae : Comb 2 7 F_ae (WriteNext.nextDep Bool s) (W_ae s) :=
  Comb.gate2 Bool.and (C_xe2 s) (C_xe1 s)
theorem C_af : Comb 3 8 F_af (WriteNext.nextDep Bool s) (W_af s) :=
  Comb.gate2 Bool.and (C_ae s) (C_xe0 s)

/-! ### The netlist computes the next-state function

One field of the record at a time, for all 4096 values of the input bits, checked by the kernel. -/

theorem identity_st_ptr : ∀ a, a < 2 ^ 3 → ∀ b, b < 2 ^ 3 → ∀ c, c < 2 ^ 3 → ∀ full inc data : Bool,
    bv3 (F_xp0 ((⟨BitVec.ofNat 3 a, full, BitVec.ofNat 3 b⟩ : WSt 2), inc, data, BitVec.ofNat 3 c)) (F_xp1 ((⟨BitVec.ofNat 3 a, full, BitVec.ofNat 3 b⟩ : WSt 2), inc, data, BitVec.ofNat 3 c)) (F_xp2 ((⟨BitVec.ofNat 3 a, full, BitVec.ofNat 3 b⟩ : WSt 2), inc, data, BitVec.ofNat 3 c)) = (WriteNext.nextFun Bool ((⟨BitVec.ofNat 3 a, full, BitVec.ofNat 3 b⟩ : WSt 2), inc, data, BitVec.ofNat 3 c)).st.ptr := by decide +kernel

theorem identity_st_full : ∀ a, a < 2 ^ 3 → ∀ b, b < 2 ^ 3 → ∀ c, c < 2 ^ 3 → ∀ full inc data : Bool,
    F_af ((⟨BitVec.ofNat 3 a, full, BitVec.ofNat 3 b⟩ : WSt 2), inc, data, BitVec.ofNat 3 c) = (WriteNext.nextFun Bool ((⟨BitVec.ofNat 3 a, full, BitVec.ofNat 3 b⟩ : WSt 2), inc, data, BitVec.ofNat 3 c)).st.full := by decide +kernel

theorem identity_st_q2 : ∀ a, a < 2 ^ 3 → ∀ b, b < 2 ^ 3 → ∀ c, c < 2 ^ 3 → ∀ full inc data : Bool,
    bv3 (F_unp_q10 ((⟨BitVec.ofNat 3 a, full, BitVec.ofNat 3 b⟩ : WSt 2), inc, data, BitVec.ofNat 3 c)) (F_unp_q11 ((⟨BitVec.ofNat 3 a, full, BitVec.ofNat 3 b⟩ : WSt 2), inc, data, BitVec.ofNat 3 c)) (F_unp_q12 ((⟨BitVec.ofNat 3 a, full, BitVec.ofNat 3 b⟩ : WSt 2), inc, data, BitVec.ofNat 3 c)) = (WriteNext.nextFun Bool ((⟨BitVec.ofNat 3 a, full, BitVec.ofNat 3 b⟩ : WSt 2), inc, data, BitVec.ofNat 3 c)).st.q2 := by decide +kernel

theorem identity_gnext : ∀ a, a < 2 ^ 3 → ∀ b, b < 2 ^ 3 → ∀ c, c < 2 ^ 3 → ∀ full inc data : Bool,
    bv3 (F_xg0 ((⟨BitVec.ofNat 3 a, full, BitVec.ofNat 3 b⟩ : WSt 2), inc, data, BitVec.ofNat 3 c)) (F_xg1 ((⟨BitVec.ofNat 3 a, full, BitVec.ofNat 3 b⟩ : WSt 2), inc, data, BitVec.ofNat 3 c)) (F_xp2 ((⟨BitVec.ofNat 3 a, full, BitVec.ofNat 3 b⟩ : WSt 2), inc, data, BitVec.ofNat 3 c)) = (WriteNext.nextFun Bool ((⟨BitVec.ofNat 3 a, full, BitVec.ofNat 3 b⟩ : WSt 2), inc, data, BitVec.ofNat 3 c)).gnext := by decide +kernel

theorem identity_we : ∀ a, a < 2 ^ 3 → ∀ b, b < 2 ^ 3 → ∀ c, c < 2 ^ 3 → ∀ full inc data : Bool,
    F_ok ((⟨BitVec.ofNat 3 a, full, BitVec.ofNat 3 b⟩ : WSt 2), inc, data, BitVec.ofNat 3 c) = (WriteNext.nextFun Bool ((⟨BitVec.ofNat 3 a, full, BitVec.ofNat 3 b⟩ : WSt 2), inc, data, BitVec.ofNat 3 c)).we := by decide +kernel

theorem identity_addr : ∀ a, a < 2 ^ 3 → ∀ b, b < 2 ^ 3 → ∀ c, c < 2 ^ 3 → ∀ full inc data : Bool,
    bv2 (F_unp_p0 ((⟨BitVec.ofNat 3 a, full, BitVec.ofNat 3 b⟩ : WSt 2), inc, data, BitVec.ofNat 3 c)) (F_unp_p1 ((⟨BitVec.ofNat 3 a, full, BitVec.ofNat 3 b⟩ : WSt 2), inc, data, BitVec.ofNat 3 c)) = (WriteNext.nextFun Bool ((⟨BitVec.ofNat 3 a, full, BitVec.ofNat 3 b⟩ : WSt 2), inc, data, BitVec.ofNat 3 c)).addr := by decide +kernel

theorem identity_data : ∀ a, a < 2 ^ 3 → ∀ b, b < 2 ^ 3 → ∀ c, c < 2 ^ 3 → ∀ full inc data : Bool,
    F_data ((⟨BitVec.ofNat 3 a, full, BitVec.ofNat 3 b⟩ : WSt 2), inc, data, BitVec.ofNat 3 c) = (WriteNext.nextFun Bool ((⟨BitVec.ofNat 3 a, full, BitVec.ofNat 3 b⟩ : WSt 2), inc, data, BitVec.ofNat 3 c)).data := by decide +kernel

theorem pack_identity' (ptr q2 q1 : BitVec 3) (full inc data : Bool) :
    (⟨⟨bv3 (F_xp0 ((⟨ptr, full, q2⟩ : WSt 2), inc, data, q1)) (F_xp1 ((⟨ptr, full, q2⟩ : WSt 2), inc, data, q1)) (F_xp2 ((⟨ptr, full, q2⟩ : WSt 2), inc, data, q1)), F_af ((⟨ptr, full, q2⟩ : WSt 2), inc, data, q1), bv3 (F_unp_q10 ((⟨ptr, full, q2⟩ : WSt 2), inc, data, q1)) (F_unp_q11 ((⟨ptr, full, q2⟩ : WSt 2), inc, data, q1)) (F_unp_q12 ((⟨ptr, full, q2⟩ : WSt 2), inc, data, q1))⟩, bv3 (F_xg0 ((⟨ptr, full, q2⟩ : WSt 2), inc, data, q1)) (F_xg1 ((⟨ptr, full, q2⟩ : WSt 2), inc, data, q1)) (F_xp2 ((⟨ptr, full, q2⟩ : WSt 2), inc, data, q1)), F_ok ((⟨ptr, full, q2⟩ : WSt 2), inc, data, q1), bv2 (F_unp_p0 ((⟨ptr, full, q2⟩ : WSt 2), inc, data, q1)) (F_unp_p1 ((⟨ptr, full, q2⟩ : WSt 2), inc, data, q1)), F_data ((⟨ptr, full, q2⟩ : WSt 2), inc, data, q1)⟩ : WNext Bool 2) = WriteNext.nextFun Bool ((⟨ptr, full, q2⟩ : WSt 2), inc, data, q1) := by
  have e : ∀ x : BitVec 3, BitVec.ofNat 3 x.toNat = x := fun x => by simp
  have h_st_ptr := identity_st_ptr ptr.toNat ptr.isLt q2.toNat q2.isLt q1.toNat q1.isLt full inc data
  rw [e ptr, e q2, e q1] at h_st_ptr
  have h_st_full := identity_st_full ptr.toNat ptr.isLt q2.toNat q2.isLt q1.toNat q1.isLt full inc data
  rw [e ptr, e q2, e q1] at h_st_full
  have h_st_q2 := identity_st_q2 ptr.toNat ptr.isLt q2.toNat q2.isLt q1.toNat q1.isLt full inc data
  rw [e ptr, e q2, e q1] at h_st_q2
  have h_gnext := identity_gnext ptr.toNat ptr.isLt q2.toNat q2.isLt q1.toNat q1.isLt full inc data
  rw [e ptr, e q2, e q1] at h_gnext
  have h_we := identity_we ptr.toNat ptr.isLt q2.toNat q2.isLt q1.toNat q1.isLt full inc data
  rw [e ptr, e q2, e q1] at h_we
  have h_addr := identity_addr ptr.toNat ptr.isLt q2.toNat q2.isLt q1.toNat q1.isLt full inc data
  rw [e ptr, e q2, e q1] at h_addr
  have h_data := identity_data ptr.toNat ptr.isLt q2.toNat q2.isLt q1.toNat q1.isLt full inc data
  rw [e ptr, e q2, e q1] at h_data
  rw [show WriteNext.nextFun Bool ((⟨ptr, full, q2⟩ : WSt 2), inc, data, q1) = ⟨⟨(WriteNext.nextFun Bool ((⟨ptr, full, q2⟩ : WSt 2), inc, data, q1)).st.ptr, (WriteNext.nextFun Bool ((⟨ptr, full, q2⟩ : WSt 2), inc, data, q1)).st.full, (WriteNext.nextFun Bool ((⟨ptr, full, q2⟩ : WSt 2), inc, data, q1)).st.q2⟩, (WriteNext.nextFun Bool ((⟨ptr, full, q2⟩ : WSt 2), inc, data, q1)).gnext, (WriteNext.nextFun Bool ((⟨ptr, full, q2⟩ : WSt 2), inc, data, q1)).we, (WriteNext.nextFun Bool ((⟨ptr, full, q2⟩ : WSt 2), inc, data, q1)).addr, (WriteNext.nextFun Bool ((⟨ptr, full, q2⟩ : WSt 2), inc, data, q1)).data⟩ from rfl]
  rw [h_st_ptr, h_st_full, h_st_q2, h_gnext, h_we, h_addr, h_data]

theorem pack_identity (i : Inp) : (⟨⟨bv3 (F_xp0 i) (F_xp1 i) (F_xp2 i), F_af i, bv3 (F_unp_q10 i) (F_unp_q11 i) (F_unp_q12 i)⟩, bv3 (F_xg0 i) (F_xg1 i) (F_xp2 i), F_ok i, bv2 (F_unp_p0 i) (F_unp_p1 i), F_data i⟩ : WNext Bool 2) = WriteNext.nextFun Bool i := by
  obtain ⟨⟨ptr, full, q2⟩, inc, data, q1⟩ := i
  exact pack_identity' ptr q2 q1 full inc data

/-- The packer's output is no longer than the block's inputs.  Each bound is a disjunction over
the leaves of the length tree, closed by the leaf that is the input itself. -/
theorem W_pack_length : (W_pack s).length ≤ WriteNext.nextLen Bool s := by
  simp only [W_pack, pack2Out_length, WriteNext.nextLen, Nat.le_min]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  all_goals rw [Nat.sub_le_iff_le_add]
  all_goals simp only [packLen, Wpk, W_unp_p0, W_unp_p1, W_unp_p2, W_unp_fl, W_unp_q20, W_unp_q21, W_unp_q22, W_unp_q10, W_unp_q11, W_unp_q12, W_nfl, W_ok, W_xp0, W_cp0, W_xp1, W_cp1, W_xp2, W_xg0, W_xg1, W_xu1, W_xu0, W_xe2, W_xe1, W_xe0, W_ae, W_af, gateOut_length, gate1Out_length, gate3Out_length, List.length_map, Nat.add_le_add_iff_right, min_le_iff_nat, Nat.le_refl, true_or, or_true, Nat.le_add_right]

/-- **The netlist satisfies the contract of the next-state block** with delay window `[0, 8]`. -/
theorem W_pack_comb : CombOut (WriteNext.nextDep Bool s) (WriteNext.nextFun Bool) (WriteNext.nextLen Bool s) 0 8 (W_pack s) := by
  refine ⟨W_pack_length s, fun t hdt ht hs => ?_⟩
  have hst := Comb.stable_of_StableOn hs
  simp only [W_pack, pack2Out_length] at ht
  have htp : t < packLen (Wpk s) - 1 := ht
  have ht : t < packLen (Wpk s) := Nat.lt_of_lt_of_le htp (Nat.sub_le _ _)
  simp only [packLen, Wpk, Nat.lt_min] at ht
  obtain ⟨t_p0, t_p1, t_p2, t_fl, t_q0, t_q1, t_q2, t_g0, t_g1, t_g2, t_we, t_a0, t_a1, t_dt⟩ := ht
  rw [W_pack, pack2Out_getD _ htp]
  simp only [Wpk]
  rw [(C_xp0 s).weaken (Nat.zero_le _) (by decide) |>.2 t hdt t_p0 hst]
  rw [(C_xp1 s).weaken (Nat.zero_le _) (by decide) |>.2 t hdt t_p1 hst]
  rw [(C_xp2 s).weaken (Nat.zero_le _) (by decide) |>.2 t hdt t_p2 hst]
  rw [(C_af s).weaken (Nat.zero_le _) (by decide) |>.2 t hdt t_fl hst]
  rw [(C_unp_q10 s).weaken (Nat.zero_le _) (by decide) |>.2 t hdt t_q0 hst]
  rw [(C_unp_q11 s).weaken (Nat.zero_le _) (by decide) |>.2 t hdt t_q1 hst]
  rw [(C_unp_q12 s).weaken (Nat.zero_le _) (by decide) |>.2 t hdt t_q2 hst]
  rw [(C_xg0 s).weaken (Nat.zero_le _) (by decide) |>.2 t hdt t_g0 hst]
  rw [(C_xg1 s).weaken (Nat.zero_le _) (by decide) |>.2 t hdt t_g1 hst]
  rw [(C_ok s).weaken (Nat.zero_le _) (by decide) |>.2 t hdt t_we hst]
  rw [(C_unp_p0 s).weaken (Nat.zero_le _) (by decide) |>.2 t hdt t_a0 hst]
  rw [(C_unp_p1 s).weaken (Nat.zero_le _) (by decide) |>.2 t hdt t_a1 hst]
  rw [(C_data s).weaken (Nat.zero_le _) (by decide) |>.2 t hdt t_dt hst]
  exact pack_identity _

/-! ### Refinement of the next-state block -/

instance : MatchInterface gateNext (WriteNext.nextSpec Bool (n := 2) 0 8) := by
  dsimp [gateNext, WriteNext.nextSpec]
  solve_match_interface
end Graphiti.AsyncFifo.WriteNext