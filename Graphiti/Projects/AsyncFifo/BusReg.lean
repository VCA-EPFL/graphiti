/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.Dff

/-!
# A three-bit register from three flip-flops

The Gray pointer of the write domain is a three-bit register, and this is that register: three
copies of `Dff.dffNetlist` sharing a clock and a clear, with the bus split into bits on the way
in and reassembled on the way out.

The two adapters are not gates.  They are the same reinterpretation of a bus as its bits that
`GateNext.lean` uses, with no delay of their own: a netlist has no notion of a bus, only of
wires, and the boundary is where the two views meet.

The flip-flops appear here as `Dff.dffSpec`, the block they were proved to refine, not as their
netlists.  Substituting the netlists back is `ExprLow.refines_env`'s job and happens once, at
the top, as in `GateLifting.lean`: refining component by component is what keeps each proof the
size of one block.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Graphiti.AsyncFifo.BusReg

open Graphiti.AsyncFifo Graphiti.AsyncFifo.Gates Graphiti.AsyncFifo.Dff

/-! ### The bus adapters -/

/-- The bits of a bus, as far as the bus is known. -/
def bitsOf (i : Nat) (d : List (BitVec 3)) : List Bool := d.map (·.getLsbD i)

@[simp] theorem bitsOf_length (i : Nat) (d : List (BitVec 3)) : (bitsOf i d).length = d.length := by
  simp [bitsOf]

theorem bitsOf_mono {i : Nat} {d d' : List (BitVec 3)} (h : d <+: d') : bitsOf i d <+: bitsOf i d' :=
  h.map _

theorem bitsOf_getD {i : Nat} {d : List (BitVec 3)} {t : Nat} (ht : t < d.length) :
    (bitsOf i d).getD t false = (d.getD t 0#3).getLsbD i := by
  simp [bitsOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem ht]

/-- Split a bus into its three bits. -/
@[drcomponents]
def unpack3 : StringModule (List (BitVec 3)) :=
  { inputs := [ (↑"d", ⟨List (BitVec 3), fun s v s' => s ⊏ v ∧ s' = v⟩) ].toAssocList
    outputs := [ (↑"b0", ⟨List Bool, fun s v s' => s' = s ∧ v = bitsOf 0 s⟩)
               , (↑"b1", ⟨List Bool, fun s v s' => s' = s ∧ v = bitsOf 1 s⟩)
               , (↑"b2", ⟨List Bool, fun s v s' => s' = s ∧ v = bitsOf 2 s⟩) ].toAssocList
    internals := []
    init_state := fun s => s = [] }

/-- The bus assembled from its bits, known as far as every bit is. -/
def pack3Out (b0 b1 b2 : List Bool) : List (BitVec 3) :=
  timeline (fun t => bv3 (b0.getD t false) (b1.getD t false) (b2.getD t false))
    (min (min b0.length b1.length) b2.length)

@[simp] theorem pack3Out_length (b0 b1 b2 : List Bool) :
    (pack3Out b0 b1 b2).length = min (min b0.length b1.length) b2.length := timeline_length _ _

theorem pack3Out_getD {b0 b1 b2 : List Bool} {t : Nat}
    (ht : t < min (min b0.length b1.length) b2.length) :
    (pack3Out b0 b1 b2).getD t 0#3 =
      bv3 (b0.getD t false) (b1.getD t false) (b2.getD t false) := timeline_getD _ ht _

theorem pack3Out_mono {b0 b0' b1 b1' b2 b2' : List Bool} (h0 : b0 <+: b0') (h1 : b1 <+: b1')
    (h2 : b2 <+: b2') : pack3Out b0 b1 b2 <+: pack3Out b0' b1' b2' := by
  have := h0.length_le; have := h1.length_le; have := h2.length_le
  apply timeline_mono (by omega)
  intro t ht
  simp only [Nat.lt_min] at ht
  rw [h0.getD_eq_left (by omega), h1.getD_eq_left (by omega), h2.getD_eq_left (by omega)]

/-- Assemble a bus from its three bits. -/
@[drcomponents]
def pack3 : StringModule (List Bool × List Bool × List Bool) :=
  { inputs := [ (↑"b0", ⟨List Bool, fun s v s' => s.1 ⊏ v ∧ s' = (v, s.2)⟩)
              , (↑"b1", ⟨List Bool, fun s v s' => s.2.1 ⊏ v ∧ s' = (s.1, v, s.2.2)⟩)
              , (↑"b2", ⟨List Bool, fun s v s' => s.2.2 ⊏ v ∧ s' = (s.1, s.2.1, v)⟩) ].toAssocList
    outputs := [ (↑"q", ⟨List (BitVec 3), fun s v s' => s' = s ∧ v = pack3Out s.1 s.2.1 s.2.2⟩) ].toAssocList
    internals := []
    init_state := fun s => s = ([], [], []) }

/-! ### The netlist -/

def busGraph := [graphEnv|
    clk [type="io"];
    d [type="io"];
    clrn [type="io"];
    q [type="io"];

    unp [type="unpack3", typeImp=$(⟨_, unpack3⟩)];
    clkF [type="fork3", typeImp=$(⟨_, fork3⟩)];
    crF [type="fork3", typeImp=$(⟨_, fork3⟩)];
    ff0 [type="dff", typeImp=$(⟨_, dffSpec⟩)];
    ff1 [type="dff", typeImp=$(⟨_, dffSpec⟩)];
    ff2 [type="dff", typeImp=$(⟨_, dffSpec⟩)];
    pk [type="pack3", typeImp=$(⟨_, pack3⟩)];

    clk -> clkF [to="in"];
    d -> unp [to="d"];
    clrn -> crF [to="in"];

    clkF -> ff0 [from="out1", to="clk"];
    clkF -> ff1 [from="out2", to="clk"];
    clkF -> ff2 [from="out3", to="clk"];
    crF -> ff0 [from="out1", to="clrn"];
    crF -> ff1 [from="out2", to="clrn"];
    crF -> ff2 [from="out3", to="clrn"];
    unp -> ff0 [from="b0", to="d"];
    unp -> ff1 [from="b1", to="d"];
    unp -> ff2 [from="b2", to="d"];
    ff0 -> pk [from="q", to="b0"];
    ff1 -> pk [from="q", to="b1"];
    ff2 -> pk [from="q", to="b2"];

    pk -> q [from="q"];
  ]

@[drunfold_defs]
def busLowered := busGraph.1.lower_TR |>.get rfl

def benv := busGraph.2

@[drenv] theorem benv_unpack3 : benv.find? "unpack3" = .some ⟨_, unpack3⟩ := rfl
@[drenv] theorem benv_fork3 : benv.find? "fork3" = .some ⟨_, fork3⟩ := rfl
@[drenv] theorem benv_dff : benv.find? "dff" = .some ⟨_, dffSpec⟩ := rfl
@[drenv] theorem benv_pack3 : benv.find? "pack3" = .some ⟨_, pack3⟩ := rfl

seal benv in
def_module busT : Type :=
  [T| busLowered, benv.find? ]
reduction_by
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type,
         ExprLow.build_module, ExprLow.build_module', toString]
  simp only [drenv]
  dsimp

seal benv in
def_module busNetlist : StringModule busT :=
  [e| busLowered, benv.find? ]

-- HEADER_END (everything below is generated by gen/gen_busreg.py)

/-! ### The specification -/

/-- What the register reports: each bit of the bus through its own flip-flop. -/
def busOut (clk : List Bool) (d : List (BitVec 3)) (crn : List Bool) : List (BitVec 3) :=
  pack3Out (dffOut clk (bitsOf 0 d) crn) (dffOut clk (bitsOf 1 d) crn) (dffOut clk (bitsOf 2 d) crn)

theorem busOut_mono {clk clk' : List Bool} {d d' : List (BitVec 3)}
    {crn crn' : List Bool} (hc : clk <+: clk') (hd : d <+: d') (hr : crn <+: crn') :
    busOut clk d crn <+: busOut clk' d' crn' :=
  pack3Out_mono (dffOut_mono hc (bitsOf_mono hd) hr) (dffOut_mono hc (bitsOf_mono hd) hr) (dffOut_mono hc (bitsOf_mono hd) hr)

/-- The three-bit register as a single block. -/
@[drcomponents]
def busSpec : StringModule (List Bool × List (BitVec 3) × List Bool × List (BitVec 3)) :=
  { inputs := [ (↑"clk", ⟨List Bool, fun s v s' => s.1 ⊏ v ∧ s' = (v, s.2)⟩)
              , (↑"d", ⟨List (BitVec 3), fun s v s' => s.2.1 ⊏ v ∧ s' = (s.1, v, s.2.2)⟩)
              , (↑"clrn", ⟨List Bool, fun s v s' => s.2.2.1 ⊏ v ∧ s' = (s.1, s.2.1, v, s.2.2.2)⟩) ].toAssocList
    outputs := [ (↑"q", ⟨List (BitVec 3), fun s v s' => s.2.2.2 <+: v ∧
                    v <+: busOut s.1 s.2.1 s.2.2.1 ∧ s' = (s.1, s.2.1, s.2.2.1, v)⟩) ].toAssocList
    internals := []
    init_state := fun s => s = ([], [], [], []) }

instance : MatchInterface busNetlist busSpec := by
  dsimp [busNetlist, busSpec]
  solve_match_interface

/-! ### The invariant -/

structure Wf (pk_b0 pk_b1 pk_b2 crF_in clkF_in ff0_clk ff0_d ff0_clrn ff1_clk ff1_d ff1_clrn ff2_clk ff2_d ff2_clrn : List Bool)
    (unp_d : List (BitVec 3)) (s : List Bool × List (BitVec 3) × List Bool × List (BitVec 3)) : Prop where
  e_clk : clkF_in = s.1
  e_d : unp_d = s.2.1
  e_crn : crF_in = s.2.2.1
  w_pk_b0 : pk_b0 <+: dffOut ff0_clk ff0_d ff0_clrn
  w_pk_b1 : pk_b1 <+: dffOut ff1_clk ff1_d ff1_clrn
  w_pk_b2 : pk_b2 <+: dffOut ff2_clk ff2_d ff2_clrn
  w_ff0_clk : ff0_clk <+: clkF_in
  w_ff0_d : ff0_d <+: bitsOf 0 unp_d
  w_ff0_clrn : ff0_clrn <+: crF_in
  w_ff1_clk : ff1_clk <+: clkF_in
  w_ff1_d : ff1_d <+: bitsOf 1 unp_d
  w_ff1_clrn : ff1_clrn <+: crF_in
  w_ff2_clk : ff2_clk <+: clkF_in
  w_ff2_d : ff2_d <+: bitsOf 2 unp_d
  w_ff2_clrn : ff2_clrn <+: crF_in
  h_q : s.2.2.2 <+: pack3Out pk_b0 pk_b1 pk_b2

def ψ (i : busT) (s : List Bool × List (BitVec 3) × List Bool × List (BitVec 3)) : Prop :=
  Wf i.1.1 i.1.2.1 i.1.2.2 i.2.2.1 i.2.2.2.1 i.2.2.2.2.1.1 i.2.2.2.2.1.2.1 i.2.2.2.2.1.2.2 i.2.2.2.2.2.1.1 i.2.2.2.2.2.1.2.1 i.2.2.2.2.2.1.2.2 i.2.2.2.2.2.2.1 i.2.2.2.2.2.2.2.1 i.2.2.2.2.2.2.2.2 i.2.1 s

theorem Wf.init : Wf [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] ([], [], [], []) :=
  ⟨rfl, rfl, rfl, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix⟩

section SpecRules
variable (sp : List Bool × List (BitVec 3) × List Bool × List (BitVec 3))

theorem spec_in_clk (v : List Bool) (h : sp.1 ⊏ v) :
    (busSpec.inputs.getIO ↑"clk").2 sp v (v, sp.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem spec_in_d (v : List (BitVec 3)) (h : sp.2.1 ⊏ v) :
    (busSpec.inputs.getIO ↑"d").2 sp v (sp.1, v, sp.2.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem spec_in_clrn (v : List Bool) (h : sp.2.2.1 ⊏ v) :
    (busSpec.inputs.getIO ↑"clrn").2 sp v (sp.1, sp.2.1, v, sp.2.2.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem spec_out_q (v : List (BitVec 3)) (h1 : sp.2.2.2 <+: v)
    (h2 : v <+: busOut sp.1 sp.2.1 sp.2.2.1) :
    (busSpec.outputs.getIO ↑"q").2 sp v (sp.1, sp.2.1, sp.2.2.1, v) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h1, h2, rfl⟩
end SpecRules

section Cases
variable {pk_b0 pk_b1 pk_b2 crF_in clkF_in ff0_clk ff0_d ff0_clrn ff1_clk ff1_d ff1_clrn ff2_clk ff2_d ff2_clrn : List Bool}
  {unp_d : List (BitVec 3)} {sp : List Bool × List (BitVec 3) × List Bool × List (BitVec 3)}
  (Hψ : Wf pk_b0 pk_b1 pk_b2 crF_in clkF_in ff0_clk ff0_d ff0_clrn ff1_clk ff1_d ff1_clrn ff2_clk ff2_d ff2_clrn unp_d sp)
include Hψ

theorem in_clk (v : List Bool) (h : clkF_in ⊏ v) :
    Wf pk_b0 pk_b1 pk_b2 crF_in (v) ff0_clk ff0_d ff0_clrn ff1_clk ff1_d ff1_clrn ff2_clk ff2_d ff2_clrn unp_d (v, sp.2) := by
  have hm : clkF_in <+: v := h.isPrefix
  exact { e_clk := rfl
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_pk_b0 := Hψ.w_pk_b0
          w_pk_b1 := Hψ.w_pk_b1
          w_pk_b2 := Hψ.w_pk_b2
          w_ff0_clk := Hψ.w_ff0_clk.trans hm
          w_ff0_d := Hψ.w_ff0_d
          w_ff0_clrn := Hψ.w_ff0_clrn
          w_ff1_clk := Hψ.w_ff1_clk.trans hm
          w_ff1_d := Hψ.w_ff1_d
          w_ff1_clrn := Hψ.w_ff1_clrn
          w_ff2_clk := Hψ.w_ff2_clk.trans hm
          w_ff2_d := Hψ.w_ff2_d
          w_ff2_clrn := Hψ.w_ff2_clrn
          h_q := Hψ.h_q }

theorem in_d (v : List (BitVec 3)) (h : unp_d ⊏ v) :
    Wf pk_b0 pk_b1 pk_b2 crF_in clkF_in ff0_clk ff0_d ff0_clrn ff1_clk ff1_d ff1_clrn ff2_clk ff2_d ff2_clrn (v) (sp.1, v, sp.2.2) := by
  have hm : unp_d <+: v := h.isPrefix
  exact { e_clk := Hψ.e_clk
          e_d := rfl
          e_crn := Hψ.e_crn
          w_pk_b0 := Hψ.w_pk_b0
          w_pk_b1 := Hψ.w_pk_b1
          w_pk_b2 := Hψ.w_pk_b2
          w_ff0_clk := Hψ.w_ff0_clk
          w_ff0_d := Hψ.w_ff0_d.trans (bitsOf_mono hm)
          w_ff0_clrn := Hψ.w_ff0_clrn
          w_ff1_clk := Hψ.w_ff1_clk
          w_ff1_d := Hψ.w_ff1_d.trans (bitsOf_mono hm)
          w_ff1_clrn := Hψ.w_ff1_clrn
          w_ff2_clk := Hψ.w_ff2_clk
          w_ff2_d := Hψ.w_ff2_d.trans (bitsOf_mono hm)
          w_ff2_clrn := Hψ.w_ff2_clrn
          h_q := Hψ.h_q }

theorem in_clrn (v : List Bool) (h : crF_in ⊏ v) :
    Wf pk_b0 pk_b1 pk_b2 (v) clkF_in ff0_clk ff0_d ff0_clrn ff1_clk ff1_d ff1_clrn ff2_clk ff2_d ff2_clrn unp_d (sp.1, sp.2.1, v, sp.2.2.2) := by
  have hm : crF_in <+: v := h.isPrefix
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := rfl
          w_pk_b0 := Hψ.w_pk_b0
          w_pk_b1 := Hψ.w_pk_b1
          w_pk_b2 := Hψ.w_pk_b2
          w_ff0_clk := Hψ.w_ff0_clk
          w_ff0_d := Hψ.w_ff0_d
          w_ff0_clrn := Hψ.w_ff0_clrn.trans hm
          w_ff1_clk := Hψ.w_ff1_clk
          w_ff1_d := Hψ.w_ff1_d
          w_ff1_clrn := Hψ.w_ff1_clrn.trans hm
          w_ff2_clk := Hψ.w_ff2_clk
          w_ff2_d := Hψ.w_ff2_d
          w_ff2_clrn := Hψ.w_ff2_clrn.trans hm
          h_q := Hψ.h_q }

theorem int_0 (_h : ff0_clk ⊏ clkF_in) :
    Wf pk_b0 pk_b1 pk_b2 crF_in clkF_in (clkF_in) ff0_d ff0_clrn ff1_clk ff1_d ff1_clrn ff2_clk ff2_d ff2_clrn unp_d sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_pk_b0 := Hψ.w_pk_b0.trans (dffOut_mono Hψ.w_ff0_clk List.prefix_rfl List.prefix_rfl)
          w_pk_b1 := Hψ.w_pk_b1
          w_pk_b2 := Hψ.w_pk_b2
          w_ff0_clk := List.prefix_rfl
          w_ff0_d := Hψ.w_ff0_d
          w_ff0_clrn := Hψ.w_ff0_clrn
          w_ff1_clk := Hψ.w_ff1_clk
          w_ff1_d := Hψ.w_ff1_d
          w_ff1_clrn := Hψ.w_ff1_clrn
          w_ff2_clk := Hψ.w_ff2_clk
          w_ff2_d := Hψ.w_ff2_d
          w_ff2_clrn := Hψ.w_ff2_clrn
          h_q := Hψ.h_q }

theorem int_1 (_h : ff1_clk ⊏ clkF_in) :
    Wf pk_b0 pk_b1 pk_b2 crF_in clkF_in ff0_clk ff0_d ff0_clrn (clkF_in) ff1_d ff1_clrn ff2_clk ff2_d ff2_clrn unp_d sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_pk_b0 := Hψ.w_pk_b0
          w_pk_b1 := Hψ.w_pk_b1.trans (dffOut_mono Hψ.w_ff1_clk List.prefix_rfl List.prefix_rfl)
          w_pk_b2 := Hψ.w_pk_b2
          w_ff0_clk := Hψ.w_ff0_clk
          w_ff0_d := Hψ.w_ff0_d
          w_ff0_clrn := Hψ.w_ff0_clrn
          w_ff1_clk := List.prefix_rfl
          w_ff1_d := Hψ.w_ff1_d
          w_ff1_clrn := Hψ.w_ff1_clrn
          w_ff2_clk := Hψ.w_ff2_clk
          w_ff2_d := Hψ.w_ff2_d
          w_ff2_clrn := Hψ.w_ff2_clrn
          h_q := Hψ.h_q }

theorem int_2 (_h : ff2_clk ⊏ clkF_in) :
    Wf pk_b0 pk_b1 pk_b2 crF_in clkF_in ff0_clk ff0_d ff0_clrn ff1_clk ff1_d ff1_clrn (clkF_in) ff2_d ff2_clrn unp_d sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_pk_b0 := Hψ.w_pk_b0
          w_pk_b1 := Hψ.w_pk_b1
          w_pk_b2 := Hψ.w_pk_b2.trans (dffOut_mono Hψ.w_ff2_clk List.prefix_rfl List.prefix_rfl)
          w_ff0_clk := Hψ.w_ff0_clk
          w_ff0_d := Hψ.w_ff0_d
          w_ff0_clrn := Hψ.w_ff0_clrn
          w_ff1_clk := Hψ.w_ff1_clk
          w_ff1_d := Hψ.w_ff1_d
          w_ff1_clrn := Hψ.w_ff1_clrn
          w_ff2_clk := List.prefix_rfl
          w_ff2_d := Hψ.w_ff2_d
          w_ff2_clrn := Hψ.w_ff2_clrn
          h_q := Hψ.h_q }

theorem int_3 (_h : ff0_clrn ⊏ crF_in) :
    Wf pk_b0 pk_b1 pk_b2 crF_in clkF_in ff0_clk ff0_d (crF_in) ff1_clk ff1_d ff1_clrn ff2_clk ff2_d ff2_clrn unp_d sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_pk_b0 := Hψ.w_pk_b0.trans (dffOut_mono List.prefix_rfl List.prefix_rfl Hψ.w_ff0_clrn)
          w_pk_b1 := Hψ.w_pk_b1
          w_pk_b2 := Hψ.w_pk_b2
          w_ff0_clk := Hψ.w_ff0_clk
          w_ff0_d := Hψ.w_ff0_d
          w_ff0_clrn := List.prefix_rfl
          w_ff1_clk := Hψ.w_ff1_clk
          w_ff1_d := Hψ.w_ff1_d
          w_ff1_clrn := Hψ.w_ff1_clrn
          w_ff2_clk := Hψ.w_ff2_clk
          w_ff2_d := Hψ.w_ff2_d
          w_ff2_clrn := Hψ.w_ff2_clrn
          h_q := Hψ.h_q }

theorem int_4 (_h : ff1_clrn ⊏ crF_in) :
    Wf pk_b0 pk_b1 pk_b2 crF_in clkF_in ff0_clk ff0_d ff0_clrn ff1_clk ff1_d (crF_in) ff2_clk ff2_d ff2_clrn unp_d sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_pk_b0 := Hψ.w_pk_b0
          w_pk_b1 := Hψ.w_pk_b1.trans (dffOut_mono List.prefix_rfl List.prefix_rfl Hψ.w_ff1_clrn)
          w_pk_b2 := Hψ.w_pk_b2
          w_ff0_clk := Hψ.w_ff0_clk
          w_ff0_d := Hψ.w_ff0_d
          w_ff0_clrn := Hψ.w_ff0_clrn
          w_ff1_clk := Hψ.w_ff1_clk
          w_ff1_d := Hψ.w_ff1_d
          w_ff1_clrn := List.prefix_rfl
          w_ff2_clk := Hψ.w_ff2_clk
          w_ff2_d := Hψ.w_ff2_d
          w_ff2_clrn := Hψ.w_ff2_clrn
          h_q := Hψ.h_q }

theorem int_5 (_h : ff2_clrn ⊏ crF_in) :
    Wf pk_b0 pk_b1 pk_b2 crF_in clkF_in ff0_clk ff0_d ff0_clrn ff1_clk ff1_d ff1_clrn ff2_clk ff2_d (crF_in) unp_d sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_pk_b0 := Hψ.w_pk_b0
          w_pk_b1 := Hψ.w_pk_b1
          w_pk_b2 := Hψ.w_pk_b2.trans (dffOut_mono List.prefix_rfl List.prefix_rfl Hψ.w_ff2_clrn)
          w_ff0_clk := Hψ.w_ff0_clk
          w_ff0_d := Hψ.w_ff0_d
          w_ff0_clrn := Hψ.w_ff0_clrn
          w_ff1_clk := Hψ.w_ff1_clk
          w_ff1_d := Hψ.w_ff1_d
          w_ff1_clrn := Hψ.w_ff1_clrn
          w_ff2_clk := Hψ.w_ff2_clk
          w_ff2_d := Hψ.w_ff2_d
          w_ff2_clrn := List.prefix_rfl
          h_q := Hψ.h_q }

theorem int_6 (_h : ff0_d ⊏ bitsOf 0 unp_d) :
    Wf pk_b0 pk_b1 pk_b2 crF_in clkF_in ff0_clk (bitsOf 0 unp_d) ff0_clrn ff1_clk ff1_d ff1_clrn ff2_clk ff2_d ff2_clrn unp_d sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_pk_b0 := Hψ.w_pk_b0.trans (dffOut_mono List.prefix_rfl Hψ.w_ff0_d List.prefix_rfl)
          w_pk_b1 := Hψ.w_pk_b1
          w_pk_b2 := Hψ.w_pk_b2
          w_ff0_clk := Hψ.w_ff0_clk
          w_ff0_d := List.prefix_rfl
          w_ff0_clrn := Hψ.w_ff0_clrn
          w_ff1_clk := Hψ.w_ff1_clk
          w_ff1_d := Hψ.w_ff1_d
          w_ff1_clrn := Hψ.w_ff1_clrn
          w_ff2_clk := Hψ.w_ff2_clk
          w_ff2_d := Hψ.w_ff2_d
          w_ff2_clrn := Hψ.w_ff2_clrn
          h_q := Hψ.h_q }

theorem int_7 (_h : ff1_d ⊏ bitsOf 1 unp_d) :
    Wf pk_b0 pk_b1 pk_b2 crF_in clkF_in ff0_clk ff0_d ff0_clrn ff1_clk (bitsOf 1 unp_d) ff1_clrn ff2_clk ff2_d ff2_clrn unp_d sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_pk_b0 := Hψ.w_pk_b0
          w_pk_b1 := Hψ.w_pk_b1.trans (dffOut_mono List.prefix_rfl Hψ.w_ff1_d List.prefix_rfl)
          w_pk_b2 := Hψ.w_pk_b2
          w_ff0_clk := Hψ.w_ff0_clk
          w_ff0_d := Hψ.w_ff0_d
          w_ff0_clrn := Hψ.w_ff0_clrn
          w_ff1_clk := Hψ.w_ff1_clk
          w_ff1_d := List.prefix_rfl
          w_ff1_clrn := Hψ.w_ff1_clrn
          w_ff2_clk := Hψ.w_ff2_clk
          w_ff2_d := Hψ.w_ff2_d
          w_ff2_clrn := Hψ.w_ff2_clrn
          h_q := Hψ.h_q }

theorem int_8 (_h : ff2_d ⊏ bitsOf 2 unp_d) :
    Wf pk_b0 pk_b1 pk_b2 crF_in clkF_in ff0_clk ff0_d ff0_clrn ff1_clk ff1_d ff1_clrn ff2_clk (bitsOf 2 unp_d) ff2_clrn unp_d sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_pk_b0 := Hψ.w_pk_b0
          w_pk_b1 := Hψ.w_pk_b1
          w_pk_b2 := Hψ.w_pk_b2.trans (dffOut_mono List.prefix_rfl Hψ.w_ff2_d List.prefix_rfl)
          w_ff0_clk := Hψ.w_ff0_clk
          w_ff0_d := Hψ.w_ff0_d
          w_ff0_clrn := Hψ.w_ff0_clrn
          w_ff1_clk := Hψ.w_ff1_clk
          w_ff1_d := Hψ.w_ff1_d
          w_ff1_clrn := Hψ.w_ff1_clrn
          w_ff2_clk := Hψ.w_ff2_clk
          w_ff2_d := List.prefix_rfl
          w_ff2_clrn := Hψ.w_ff2_clrn
          h_q := Hψ.h_q }

theorem int_9 {out : List Bool} (_h : pk_b0 ⊏ out) (hout : out <+: dffOut ff0_clk ff0_d ff0_clrn) :
    Wf (out) pk_b1 pk_b2 crF_in clkF_in ff0_clk ff0_d ff0_clrn ff1_clk ff1_d ff1_clrn ff2_clk ff2_d ff2_clrn unp_d sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_pk_b0 := hout
          w_pk_b1 := Hψ.w_pk_b1
          w_pk_b2 := Hψ.w_pk_b2
          w_ff0_clk := Hψ.w_ff0_clk
          w_ff0_d := Hψ.w_ff0_d
          w_ff0_clrn := Hψ.w_ff0_clrn
          w_ff1_clk := Hψ.w_ff1_clk
          w_ff1_d := Hψ.w_ff1_d
          w_ff1_clrn := Hψ.w_ff1_clrn
          w_ff2_clk := Hψ.w_ff2_clk
          w_ff2_d := Hψ.w_ff2_d
          w_ff2_clrn := Hψ.w_ff2_clrn
          h_q := Hψ.h_q.trans (pack3Out_mono (_h.isPrefix) List.prefix_rfl List.prefix_rfl) }

theorem int_10 {out : List Bool} (_h : pk_b1 ⊏ out) (hout : out <+: dffOut ff1_clk ff1_d ff1_clrn) :
    Wf pk_b0 (out) pk_b2 crF_in clkF_in ff0_clk ff0_d ff0_clrn ff1_clk ff1_d ff1_clrn ff2_clk ff2_d ff2_clrn unp_d sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_pk_b0 := Hψ.w_pk_b0
          w_pk_b1 := hout
          w_pk_b2 := Hψ.w_pk_b2
          w_ff0_clk := Hψ.w_ff0_clk
          w_ff0_d := Hψ.w_ff0_d
          w_ff0_clrn := Hψ.w_ff0_clrn
          w_ff1_clk := Hψ.w_ff1_clk
          w_ff1_d := Hψ.w_ff1_d
          w_ff1_clrn := Hψ.w_ff1_clrn
          w_ff2_clk := Hψ.w_ff2_clk
          w_ff2_d := Hψ.w_ff2_d
          w_ff2_clrn := Hψ.w_ff2_clrn
          h_q := Hψ.h_q.trans (pack3Out_mono List.prefix_rfl (_h.isPrefix) List.prefix_rfl) }

theorem int_11 {out : List Bool} (_h : pk_b2 ⊏ out) (hout : out <+: dffOut ff2_clk ff2_d ff2_clrn) :
    Wf pk_b0 pk_b1 (out) crF_in clkF_in ff0_clk ff0_d ff0_clrn ff1_clk ff1_d ff1_clrn ff2_clk ff2_d ff2_clrn unp_d sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_pk_b0 := Hψ.w_pk_b0
          w_pk_b1 := Hψ.w_pk_b1
          w_pk_b2 := hout
          w_ff0_clk := Hψ.w_ff0_clk
          w_ff0_d := Hψ.w_ff0_d
          w_ff0_clrn := Hψ.w_ff0_clrn
          w_ff1_clk := Hψ.w_ff1_clk
          w_ff1_d := Hψ.w_ff1_d
          w_ff1_clrn := Hψ.w_ff1_clrn
          w_ff2_clk := Hψ.w_ff2_clk
          w_ff2_d := Hψ.w_ff2_d
          w_ff2_clrn := Hψ.w_ff2_clrn
          h_q := Hψ.h_q.trans (pack3Out_mono List.prefix_rfl List.prefix_rfl (_h.isPrefix)) }

/-- What the block reports is a prefix of the specification's stream: each bit is a prefix
of its flip-flop's output, and the flip-flops see prefixes of the block's own inputs. -/
theorem out_q : pack3Out pk_b0 pk_b1 pk_b2 <+: busOut sp.1 sp.2.1 sp.2.2.1 := by
  refine pack3Out_mono ?_ ?_ ?_
  · exact Hψ.w_pk_b0.trans (dffOut_mono (Hψ.w_ff0_clk.trans (Hψ.e_clk ▸ List.prefix_rfl))
      (Hψ.w_ff0_d.trans (bitsOf_mono (Hψ.e_d ▸ List.prefix_rfl)))
      (Hψ.w_ff0_clrn.trans (Hψ.e_crn ▸ List.prefix_rfl)))
  · exact Hψ.w_pk_b1.trans (dffOut_mono (Hψ.w_ff1_clk.trans (Hψ.e_clk ▸ List.prefix_rfl))
      (Hψ.w_ff1_d.trans (bitsOf_mono (Hψ.e_d ▸ List.prefix_rfl)))
      (Hψ.w_ff1_clrn.trans (Hψ.e_crn ▸ List.prefix_rfl)))
  · exact Hψ.w_pk_b2.trans (dffOut_mono (Hψ.w_ff2_clk.trans (Hψ.e_clk ▸ List.prefix_rfl))
      (Hψ.w_ff2_d.trans (bitsOf_mono (Hψ.e_d ▸ List.prefix_rfl)))
      (Hψ.w_ff2_clrn.trans (Hψ.e_crn ▸ List.prefix_rfl)))

/-- What it has reported it has reported: the report is the packer's, and the packer's
inputs only grow. -/
theorem out_wf : Wf pk_b0 pk_b1 pk_b2 crF_in clkF_in ff0_clk ff0_d ff0_clrn ff1_clk ff1_d ff1_clrn ff2_clk ff2_d ff2_clrn unp_d (sp.1, sp.2.1, sp.2.2.1, pack3Out pk_b0 pk_b1 pk_b2) := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          w_pk_b0 := Hψ.w_pk_b0
          w_pk_b1 := Hψ.w_pk_b1
          w_pk_b2 := Hψ.w_pk_b2
          w_ff0_clk := Hψ.w_ff0_clk
          w_ff0_d := Hψ.w_ff0_d
          w_ff0_clrn := Hψ.w_ff0_clrn
          w_ff1_clk := Hψ.w_ff1_clk
          w_ff1_d := Hψ.w_ff1_d
          w_ff1_clrn := Hψ.w_ff1_clrn
          w_ff2_clk := Hψ.w_ff2_clk
          w_ff2_d := Hψ.w_ff2_d
          w_ff2_clrn := Hψ.w_ff2_clrn
          h_q := List.prefix_rfl }

end Cases

/-! ### The refinement -/

theorem int_case_0 (s : List Bool × List (BitVec 3) × List Bool × List (BitVec 3)) (i mid : busT) (Hψ : ψ i s)
    (Hrule : (busNetlist.internals.getD 0 (fun _ _ => False)) i mid) :
    ∃ s', existSR busSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨pk_b0, pk_b1, pk_b2⟩, unp_d, crF_in, clkF_in, ⟨ff0_clk, ff0_d, ff0_clrn⟩, ⟨ff1_clk, ff1_d, ff1_clrn⟩, ⟨ff2_clk, ff2_d, ff2_clrn⟩⟩ := i
  obtain ⟨⟨m_pk_b0, m_pk_b1, m_pk_b2⟩, m_unp_d, m_crF_in, m_clkF_in, ⟨m_ff0_clk, m_ff0_d, m_ff0_clrn⟩, ⟨m_ff1_clk, m_ff1_d, m_ff1_clrn⟩, ⟨m_ff2_clk, m_ff2_d, m_ff2_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_pk_b0, c_pk_b1, c_pk_b2⟩, c_unp_d, c_crF_in, c_clkF_in, ⟨c_ff0_clk, c_ff0_d, c_ff0_clrn⟩, ⟨c_ff1_clk, c_ff1_d, c_ff1_clrn⟩, ⟨c_ff2_clk, c_ff2_d, c_ff2_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_0 Hψ ‹_›⟩

theorem int_case_1 (s : List Bool × List (BitVec 3) × List Bool × List (BitVec 3)) (i mid : busT) (Hψ : ψ i s)
    (Hrule : (busNetlist.internals.getD 1 (fun _ _ => False)) i mid) :
    ∃ s', existSR busSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨pk_b0, pk_b1, pk_b2⟩, unp_d, crF_in, clkF_in, ⟨ff0_clk, ff0_d, ff0_clrn⟩, ⟨ff1_clk, ff1_d, ff1_clrn⟩, ⟨ff2_clk, ff2_d, ff2_clrn⟩⟩ := i
  obtain ⟨⟨m_pk_b0, m_pk_b1, m_pk_b2⟩, m_unp_d, m_crF_in, m_clkF_in, ⟨m_ff0_clk, m_ff0_d, m_ff0_clrn⟩, ⟨m_ff1_clk, m_ff1_d, m_ff1_clrn⟩, ⟨m_ff2_clk, m_ff2_d, m_ff2_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_pk_b0, c_pk_b1, c_pk_b2⟩, c_unp_d, c_crF_in, c_clkF_in, ⟨c_ff0_clk, c_ff0_d, c_ff0_clrn⟩, ⟨c_ff1_clk, c_ff1_d, c_ff1_clrn⟩, ⟨c_ff2_clk, c_ff2_d, c_ff2_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_1 Hψ ‹_›⟩

theorem int_case_2 (s : List Bool × List (BitVec 3) × List Bool × List (BitVec 3)) (i mid : busT) (Hψ : ψ i s)
    (Hrule : (busNetlist.internals.getD 2 (fun _ _ => False)) i mid) :
    ∃ s', existSR busSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨pk_b0, pk_b1, pk_b2⟩, unp_d, crF_in, clkF_in, ⟨ff0_clk, ff0_d, ff0_clrn⟩, ⟨ff1_clk, ff1_d, ff1_clrn⟩, ⟨ff2_clk, ff2_d, ff2_clrn⟩⟩ := i
  obtain ⟨⟨m_pk_b0, m_pk_b1, m_pk_b2⟩, m_unp_d, m_crF_in, m_clkF_in, ⟨m_ff0_clk, m_ff0_d, m_ff0_clrn⟩, ⟨m_ff1_clk, m_ff1_d, m_ff1_clrn⟩, ⟨m_ff2_clk, m_ff2_d, m_ff2_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_pk_b0, c_pk_b1, c_pk_b2⟩, c_unp_d, c_crF_in, c_clkF_in, ⟨c_ff0_clk, c_ff0_d, c_ff0_clrn⟩, ⟨c_ff1_clk, c_ff1_d, c_ff1_clrn⟩, ⟨c_ff2_clk, c_ff2_d, c_ff2_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_2 Hψ ‹_›⟩

theorem int_case_3 (s : List Bool × List (BitVec 3) × List Bool × List (BitVec 3)) (i mid : busT) (Hψ : ψ i s)
    (Hrule : (busNetlist.internals.getD 3 (fun _ _ => False)) i mid) :
    ∃ s', existSR busSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨pk_b0, pk_b1, pk_b2⟩, unp_d, crF_in, clkF_in, ⟨ff0_clk, ff0_d, ff0_clrn⟩, ⟨ff1_clk, ff1_d, ff1_clrn⟩, ⟨ff2_clk, ff2_d, ff2_clrn⟩⟩ := i
  obtain ⟨⟨m_pk_b0, m_pk_b1, m_pk_b2⟩, m_unp_d, m_crF_in, m_clkF_in, ⟨m_ff0_clk, m_ff0_d, m_ff0_clrn⟩, ⟨m_ff1_clk, m_ff1_d, m_ff1_clrn⟩, ⟨m_ff2_clk, m_ff2_d, m_ff2_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_pk_b0, c_pk_b1, c_pk_b2⟩, c_unp_d, c_crF_in, c_clkF_in, ⟨c_ff0_clk, c_ff0_d, c_ff0_clrn⟩, ⟨c_ff1_clk, c_ff1_d, c_ff1_clrn⟩, ⟨c_ff2_clk, c_ff2_d, c_ff2_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_3 Hψ ‹_›⟩

theorem int_case_4 (s : List Bool × List (BitVec 3) × List Bool × List (BitVec 3)) (i mid : busT) (Hψ : ψ i s)
    (Hrule : (busNetlist.internals.getD 4 (fun _ _ => False)) i mid) :
    ∃ s', existSR busSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨pk_b0, pk_b1, pk_b2⟩, unp_d, crF_in, clkF_in, ⟨ff0_clk, ff0_d, ff0_clrn⟩, ⟨ff1_clk, ff1_d, ff1_clrn⟩, ⟨ff2_clk, ff2_d, ff2_clrn⟩⟩ := i
  obtain ⟨⟨m_pk_b0, m_pk_b1, m_pk_b2⟩, m_unp_d, m_crF_in, m_clkF_in, ⟨m_ff0_clk, m_ff0_d, m_ff0_clrn⟩, ⟨m_ff1_clk, m_ff1_d, m_ff1_clrn⟩, ⟨m_ff2_clk, m_ff2_d, m_ff2_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_pk_b0, c_pk_b1, c_pk_b2⟩, c_unp_d, c_crF_in, c_clkF_in, ⟨c_ff0_clk, c_ff0_d, c_ff0_clrn⟩, ⟨c_ff1_clk, c_ff1_d, c_ff1_clrn⟩, ⟨c_ff2_clk, c_ff2_d, c_ff2_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_4 Hψ ‹_›⟩

theorem int_case_5 (s : List Bool × List (BitVec 3) × List Bool × List (BitVec 3)) (i mid : busT) (Hψ : ψ i s)
    (Hrule : (busNetlist.internals.getD 5 (fun _ _ => False)) i mid) :
    ∃ s', existSR busSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨pk_b0, pk_b1, pk_b2⟩, unp_d, crF_in, clkF_in, ⟨ff0_clk, ff0_d, ff0_clrn⟩, ⟨ff1_clk, ff1_d, ff1_clrn⟩, ⟨ff2_clk, ff2_d, ff2_clrn⟩⟩ := i
  obtain ⟨⟨m_pk_b0, m_pk_b1, m_pk_b2⟩, m_unp_d, m_crF_in, m_clkF_in, ⟨m_ff0_clk, m_ff0_d, m_ff0_clrn⟩, ⟨m_ff1_clk, m_ff1_d, m_ff1_clrn⟩, ⟨m_ff2_clk, m_ff2_d, m_ff2_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_pk_b0, c_pk_b1, c_pk_b2⟩, c_unp_d, c_crF_in, c_clkF_in, ⟨c_ff0_clk, c_ff0_d, c_ff0_clrn⟩, ⟨c_ff1_clk, c_ff1_d, c_ff1_clrn⟩, ⟨c_ff2_clk, c_ff2_d, c_ff2_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_5 Hψ ‹_›⟩

theorem int_case_6 (s : List Bool × List (BitVec 3) × List Bool × List (BitVec 3)) (i mid : busT) (Hψ : ψ i s)
    (Hrule : (busNetlist.internals.getD 6 (fun _ _ => False)) i mid) :
    ∃ s', existSR busSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨pk_b0, pk_b1, pk_b2⟩, unp_d, crF_in, clkF_in, ⟨ff0_clk, ff0_d, ff0_clrn⟩, ⟨ff1_clk, ff1_d, ff1_clrn⟩, ⟨ff2_clk, ff2_d, ff2_clrn⟩⟩ := i
  obtain ⟨⟨m_pk_b0, m_pk_b1, m_pk_b2⟩, m_unp_d, m_crF_in, m_clkF_in, ⟨m_ff0_clk, m_ff0_d, m_ff0_clrn⟩, ⟨m_ff1_clk, m_ff1_d, m_ff1_clrn⟩, ⟨m_ff2_clk, m_ff2_d, m_ff2_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_pk_b0, c_pk_b1, c_pk_b2⟩, c_unp_d, c_crF_in, c_clkF_in, ⟨c_ff0_clk, c_ff0_d, c_ff0_clrn⟩, ⟨c_ff1_clk, c_ff1_d, c_ff1_clrn⟩, ⟨c_ff2_clk, c_ff2_d, c_ff2_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_6 Hψ ‹_›⟩

theorem int_case_7 (s : List Bool × List (BitVec 3) × List Bool × List (BitVec 3)) (i mid : busT) (Hψ : ψ i s)
    (Hrule : (busNetlist.internals.getD 7 (fun _ _ => False)) i mid) :
    ∃ s', existSR busSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨pk_b0, pk_b1, pk_b2⟩, unp_d, crF_in, clkF_in, ⟨ff0_clk, ff0_d, ff0_clrn⟩, ⟨ff1_clk, ff1_d, ff1_clrn⟩, ⟨ff2_clk, ff2_d, ff2_clrn⟩⟩ := i
  obtain ⟨⟨m_pk_b0, m_pk_b1, m_pk_b2⟩, m_unp_d, m_crF_in, m_clkF_in, ⟨m_ff0_clk, m_ff0_d, m_ff0_clrn⟩, ⟨m_ff1_clk, m_ff1_d, m_ff1_clrn⟩, ⟨m_ff2_clk, m_ff2_d, m_ff2_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_pk_b0, c_pk_b1, c_pk_b2⟩, c_unp_d, c_crF_in, c_clkF_in, ⟨c_ff0_clk, c_ff0_d, c_ff0_clrn⟩, ⟨c_ff1_clk, c_ff1_d, c_ff1_clrn⟩, ⟨c_ff2_clk, c_ff2_d, c_ff2_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_7 Hψ ‹_›⟩

theorem int_case_8 (s : List Bool × List (BitVec 3) × List Bool × List (BitVec 3)) (i mid : busT) (Hψ : ψ i s)
    (Hrule : (busNetlist.internals.getD 8 (fun _ _ => False)) i mid) :
    ∃ s', existSR busSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨pk_b0, pk_b1, pk_b2⟩, unp_d, crF_in, clkF_in, ⟨ff0_clk, ff0_d, ff0_clrn⟩, ⟨ff1_clk, ff1_d, ff1_clrn⟩, ⟨ff2_clk, ff2_d, ff2_clrn⟩⟩ := i
  obtain ⟨⟨m_pk_b0, m_pk_b1, m_pk_b2⟩, m_unp_d, m_crF_in, m_clkF_in, ⟨m_ff0_clk, m_ff0_d, m_ff0_clrn⟩, ⟨m_ff1_clk, m_ff1_d, m_ff1_clrn⟩, ⟨m_ff2_clk, m_ff2_d, m_ff2_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_pk_b0, c_pk_b1, c_pk_b2⟩, c_unp_d, c_crF_in, c_clkF_in, ⟨c_ff0_clk, c_ff0_d, c_ff0_clrn⟩, ⟨c_ff1_clk, c_ff1_d, c_ff1_clrn⟩, ⟨c_ff2_clk, c_ff2_d, c_ff2_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_8 Hψ ‹_›⟩

theorem int_case_9 (s : List Bool × List (BitVec 3) × List Bool × List (BitVec 3)) (i mid : busT) (Hψ : ψ i s)
    (Hrule : (busNetlist.internals.getD 9 (fun _ _ => False)) i mid) :
    ∃ s', existSR busSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨pk_b0, pk_b1, pk_b2⟩, unp_d, crF_in, clkF_in, ⟨ff0_clk, ff0_d, ff0_clrn⟩, ⟨ff1_clk, ff1_d, ff1_clrn⟩, ⟨ff2_clk, ff2_d, ff2_clrn⟩⟩ := i
  obtain ⟨⟨m_pk_b0, m_pk_b1, m_pk_b2⟩, m_unp_d, m_crF_in, m_clkF_in, ⟨m_ff0_clk, m_ff0_d, m_ff0_clrn⟩, ⟨m_ff1_clk, m_ff1_d, m_ff1_clrn⟩, ⟨m_ff2_clk, m_ff2_d, m_ff2_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_pk_b0, c_pk_b1, c_pk_b2⟩, c_unp_d, c_crF_in, c_clkF_in, ⟨c_ff0_clk, c_ff0_d, c_ff0_clrn⟩, ⟨c_ff1_clk, c_ff1_d, c_ff1_clrn⟩, ⟨c_ff2_clk, c_ff2_d, c_ff2_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_9 Hψ ‹_› ‹_›⟩

theorem int_case_10 (s : List Bool × List (BitVec 3) × List Bool × List (BitVec 3)) (i mid : busT) (Hψ : ψ i s)
    (Hrule : (busNetlist.internals.getD 10 (fun _ _ => False)) i mid) :
    ∃ s', existSR busSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨pk_b0, pk_b1, pk_b2⟩, unp_d, crF_in, clkF_in, ⟨ff0_clk, ff0_d, ff0_clrn⟩, ⟨ff1_clk, ff1_d, ff1_clrn⟩, ⟨ff2_clk, ff2_d, ff2_clrn⟩⟩ := i
  obtain ⟨⟨m_pk_b0, m_pk_b1, m_pk_b2⟩, m_unp_d, m_crF_in, m_clkF_in, ⟨m_ff0_clk, m_ff0_d, m_ff0_clrn⟩, ⟨m_ff1_clk, m_ff1_d, m_ff1_clrn⟩, ⟨m_ff2_clk, m_ff2_d, m_ff2_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_pk_b0, c_pk_b1, c_pk_b2⟩, c_unp_d, c_crF_in, c_clkF_in, ⟨c_ff0_clk, c_ff0_d, c_ff0_clrn⟩, ⟨c_ff1_clk, c_ff1_d, c_ff1_clrn⟩, ⟨c_ff2_clk, c_ff2_d, c_ff2_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_10 Hψ ‹_› ‹_›⟩

theorem int_case_11 (s : List Bool × List (BitVec 3) × List Bool × List (BitVec 3)) (i mid : busT) (Hψ : ψ i s)
    (Hrule : (busNetlist.internals.getD 11 (fun _ _ => False)) i mid) :
    ∃ s', existSR busSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨⟨pk_b0, pk_b1, pk_b2⟩, unp_d, crF_in, clkF_in, ⟨ff0_clk, ff0_d, ff0_clrn⟩, ⟨ff1_clk, ff1_d, ff1_clrn⟩, ⟨ff2_clk, ff2_d, ff2_clrn⟩⟩ := i
  obtain ⟨⟨m_pk_b0, m_pk_b1, m_pk_b2⟩, m_unp_d, m_crF_in, m_clkF_in, ⟨m_ff0_clk, m_ff0_d, m_ff0_clrn⟩, ⟨m_ff1_clk, m_ff1_d, m_ff1_clrn⟩, ⟨m_ff2_clk, m_ff2_d, m_ff2_clrn⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨⟨c_pk_b0, c_pk_b1, c_pk_b2⟩, c_unp_d, c_crF_in, c_clkF_in, ⟨c_ff0_clk, c_ff0_d, c_ff0_clrn⟩, ⟨c_ff1_clk, c_ff1_d, c_ff1_clrn⟩, ⟨c_ff2_clk, c_ff2_d, c_ff2_clrn⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_11 Hψ ‹_› ‹_›⟩

theorem busNetlist_internals_eq : busNetlist.internals = [busNetlist.internals.getD 0 (fun _ _ => False), busNetlist.internals.getD 1 (fun _ _ => False), busNetlist.internals.getD 2 (fun _ _ => False), busNetlist.internals.getD 3 (fun _ _ => False), busNetlist.internals.getD 4 (fun _ _ => False), busNetlist.internals.getD 5 (fun _ _ => False), busNetlist.internals.getD 6 (fun _ _ => False), busNetlist.internals.getD 7 (fun _ _ => False), busNetlist.internals.getD 8 (fun _ _ => False), busNetlist.internals.getD 9 (fun _ _ => False), busNetlist.internals.getD 10 (fun _ _ => False), busNetlist.internals.getD 11 (fun _ _ => False)] := rfl

theorem refines_ψ : busNetlist ⊑_{ψ} busSpec := by
  intro i s Hψ
  constructor
  · intro ident mid_i v Hrule
    obtain ⟨⟨pk_b0, pk_b1, pk_b2⟩, unp_d, crF_in, clkF_in, ⟨ff0_clk, ff0_d, ff0_clrn⟩, ⟨ff1_clk, ff1_d, ff1_clrn⟩, ⟨ff2_clk, ff2_d, ff2_clrn⟩⟩ := i
    dsimp only [ψ] at Hψ
    obtain ⟨⟨m_pk_b0, m_pk_b1, m_pk_b2⟩, m_unp_d, m_crF_in, m_clkF_in, ⟨m_ff0_clk, m_ff0_d, m_ff0_clrn⟩, ⟨m_ff1_clk, m_ff1_d, m_ff1_clrn⟩, ⟨m_ff2_clk, m_ff2_d, m_ff2_clrn⟩⟩ := mid_i
    case_transition Hcontains : Module.inputs busNetlist, ident, (PortMap.getIO_not_contained_false' Hrule)
    dsimp only [busNetlist] at Hcontains
    simp at Hcontains
    rcases Hcontains with h | h | h
    all_goals subst h
    all_goals rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule
    all_goals dsimp only at Hrule
    all_goals simp only [Prod.mk.injEq, and_assoc] at Hrule
    all_goals repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
    all_goals first
      | exact ⟨_, _, spec_in_clk s _ (by rw [← Hψ.e_clk]; assumption), existSR_reflexive, in_clk Hψ _ ‹_›⟩
      | exact ⟨_, _, spec_in_d s _ (by rw [← Hψ.e_d]; assumption), existSR_reflexive, in_d Hψ _ ‹_›⟩
      | exact ⟨_, _, spec_in_clrn s _ (by rw [← Hψ.e_crn]; assumption), existSR_reflexive, in_clrn Hψ _ ‹_›⟩
  · intro ident mid_i v Hrule
    obtain ⟨⟨pk_b0, pk_b1, pk_b2⟩, unp_d, crF_in, clkF_in, ⟨ff0_clk, ff0_d, ff0_clrn⟩, ⟨ff1_clk, ff1_d, ff1_clrn⟩, ⟨ff2_clk, ff2_d, ff2_clrn⟩⟩ := i
    dsimp only [ψ] at Hψ
    obtain ⟨⟨m_pk_b0, m_pk_b1, m_pk_b2⟩, m_unp_d, m_crF_in, m_clkF_in, ⟨m_ff0_clk, m_ff0_d, m_ff0_clrn⟩, ⟨m_ff1_clk, m_ff1_d, m_ff1_clrn⟩, ⟨m_ff2_clk, m_ff2_d, m_ff2_clrn⟩⟩ := mid_i
    case_transition Hcontains : Module.outputs busNetlist, ident, (PortMap.getIO_not_contained_false' Hrule)
    dsimp only [busNetlist] at Hcontains
    simp at Hcontains
    subst Hcontains
    rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule
    dsimp only at Hrule
    simp only [Prod.mk.injEq, and_assoc] at Hrule
    repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
    exact ⟨s, _, existSR_reflexive, spec_out_q s _ Hψ.h_q (out_q Hψ), out_wf Hψ⟩
  · intro rule mid_i Hin Hrule
    rw [busNetlist_internals_eq] at Hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at Hin
    rcases Hin with h | h | h | h | h | h | h | h | h | h | h | h
    · subst h; exact int_case_0 s i mid_i Hψ Hrule
    · subst h; exact int_case_1 s i mid_i Hψ Hrule
    · subst h; exact int_case_2 s i mid_i Hψ Hrule
    · subst h; exact int_case_3 s i mid_i Hψ Hrule
    · subst h; exact int_case_4 s i mid_i Hψ Hrule
    · subst h; exact int_case_5 s i mid_i Hψ Hrule
    · subst h; exact int_case_6 s i mid_i Hψ Hrule
    · subst h; exact int_case_7 s i mid_i Hψ Hrule
    · subst h; exact int_case_8 s i mid_i Hψ Hrule
    · subst h; exact int_case_9 s i mid_i Hψ Hrule
    · subst h; exact int_case_10 s i mid_i Hψ Hrule
    · subst h; exact int_case_11 s i mid_i Hψ Hrule

theorem refines_initial : Module.refines_initial busNetlist busSpec ψ := by
  intro i hi
  obtain ⟨⟨pk_b0, pk_b1, pk_b2⟩, unp_d, crF_in, clkF_in, ⟨ff0_clk, ff0_d, ff0_clrn⟩, ⟨ff1_clk, ff1_d, ff1_clrn⟩, ⟨ff2_clk, ff2_d, ff2_clrn⟩⟩ := i
  dsimp only [busNetlist] at hi
  simp only [Prod.mk.injEq, and_assoc] at hi
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hi
  exact ⟨([], [], [], []), rfl, Wf.init⟩

/-- **The 3 flip-flops refine a three-bit register.** -/
theorem reg_refines : busNetlist ⊑ busSpec :=
  ⟨inferInstance, ψ, refines_ψ, refines_initial⟩

end Graphiti.AsyncFifo.BusReg
