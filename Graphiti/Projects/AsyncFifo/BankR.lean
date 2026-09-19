/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.StRegR
import Graphiti.Projects.AsyncFifo.BusReg
import Graphiti.Projects.AsyncFifo.StRegRTiming
import Graphiti.Projects.AsyncFifo.BusRegTiming

/-!
# The read domain's register bank

`Timed.rregBank` is the read domain's state: a seven-bit state register, the three-bit Gray
pointer that crosses into the write domain, and the `empty` flag (a projection of the state).
This file wires the two registers together and unpacks the next-state bus that feeds them.

It is `Bank.lean` without the register file: the read domain holds no memory of its own, it only
addresses the write domain's.  So there are three output ports instead of four, and two
registers instead of three.

Like the write bank, it has one port the register-level model does not: the clear.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Graphiti.AsyncFifo.BankR

open Graphiti.AsyncFifo Graphiti.AsyncFifo.Gates Graphiti.AsyncFifo.Timed
  Graphiti.AsyncFifo.Dff

/-! ### The next-state bus and its fields -/

def stOf (d : List (RNext 2)) : List (RSt 2) := d.map (·.st)
def gnextOf (d : List (RNext 2)) : List (BitVec 3) := d.map (·.gnext)

@[simp] theorem stOf_length (d : List (RNext 2)) : (stOf d).length = d.length := by simp [stOf]
@[simp] theorem gnextOf_length (d : List (RNext 2)) : (gnextOf d).length = d.length := by
  simp [gnextOf]

theorem stOf_mono {d d' : List (RNext 2)} (h : d <+: d') : stOf d <+: stOf d' := h.map _
theorem gnextOf_mono {d d' : List (RNext 2)} (h : d <+: d') : gnextOf d <+: gnextOf d' :=
  h.map _

theorem stOf_getD (d : List (RNext 2)) (u : Nat) :
    (stOf d).getD u default = (d.getD u default).st := by
  by_cases h : u < d.length
  · simp [stOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [stOf]; omega),
      List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

theorem gnextOf_getD (d : List (RNext 2)) (u : Nat) :
    (gnextOf d).getD u 0#3 = (d.getD u default).gnext := by
  by_cases h : u < d.length
  · simp [gnextOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [gnextOf]; omega),
      List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

/-- Split the next-state bus into the two streams the bank's registers read. -/
@[drcomponents]
def unpackNext : StringModule (List (RNext 2)) :=
  { inputs := [ (↑"d", ⟨List (RNext 2), fun s v s' => s ⊏ v ∧ s' = v⟩) ].toAssocList
    outputs := [ (↑"st", ⟨List (RSt 2), fun s v s' => s' = s ∧ v = stOf s⟩)
               , (↑"gnext", ⟨List (BitVec 3), fun s v s' => s' = s ∧ v = gnextOf s⟩) ].toAssocList
    internals := []
    init_state := fun s => s = [] }

/-- The `empty` flag is a bit of the state register. -/
@[drcomponents]
def emptyOf : StringModule (List (RSt 2)) :=
  { inputs := [ (↑"q", ⟨List (RSt 2), fun s v s' => s ⊏ v ∧ s' = v⟩) ].toAssocList
    outputs := [ (↑"empty", ⟨List Bool, fun s v s' => s' = s ∧ v = s.map (·.empty)⟩) ].toAssocList
    internals := []
    init_state := fun s => s = [] }

/-! ### The bank's contracts

Each block was proved against its own contract over its own stream; here they are read back in
the bank's terms, where every field of the next-state bus has the bus's own horizon. -/

/-- How far the bank's inputs are known. -/
def bankLen (clk : List Bool) (d : List (RNext 2)) (crn : List Bool) : Nat :=
  min (min clk.length d.length) crn.length

theorem stLen_eq (clk : List Bool) (d : List (RNext 2)) (crn : List Bool) :
    StRegR.stLen clk (stOf d) crn = bankLen clk d crn := by simp [StRegR.stLen, bankLen]

theorem busLen_eq (clk : List Bool) (d : List (RNext 2)) (crn : List Bool) :
    BusReg.busLen clk (gnextOf d) crn = bankLen clk d crn := by simp [BusReg.busLen, bankLen]

/-- The filters the bank needs, at the bank's horizon. -/
structure BankOK (clk : List Bool) (d : List (RNext 2)) (crn : List Bool) (R : Nat) :
    Prop where
  hR : 6 ≤ R
  clear : ClearOK R crn crn.length
  reset : ResetOK (R + 3) clk clk.length
  pulse : PulseOK 3 clk clk.length
  period : ClockOK 12 clk clk.length

variable {clk : List Bool} {d : List (RNext 2)} {crn : List Bool} {R : Nat}

/-- **The state register's contract**, in the bank's terms. -/
theorem bank_st (H : BankOK clk d crn R) {v : List (RSt 2)}
    (hv : v <+: StRegR.stOut clk (stOf d) crn) :
    RegOut 4 1 default clk (fun u => (d.getD u default).st) d.length v := by
  have h := StRegR.stOut_regOut (clk := clk) (d := stOf d) (crn := crn) (R := R) (by have := H.hR; omega)
    (by rw [stLen_eq]; exact H.clear.mono (by unfold bankLen; omega))
    (by rw [stLen_eq]; exact H.reset.mono (by unfold bankLen; omega))
    (by rw [stLen_eq]; exact H.pulse.mono (by unfold bankLen; omega)) hv
  simpa only [stOf_getD, stOf_length] using h

/-- **The Gray pointer register's contract**: glitch-free across an edge, which is what makes it
safe to sample in the other clock domain. -/
theorem bank_gray (H : BankOK clk d crn R)
    (hstable : ∀ e, e < bankLen clk d crn → riseAt clk e = true →
      ∀ u, e - 2 ≤ u → u ≤ e → (d.getD u default).gnext = (d.getD e default).gnext)
    {v : List (BitVec 3)} (hv : v <+: BusReg.busOut clk (gnextOf d) crn) :
    BusRegOut 4 1 clk (fun u => (d.getD u default).gnext) d.length v := by
  have h := BusReg.busOut_busRegOut (clk := clk) (d := gnextOf d) (crn := crn) (R := R) (by have := H.hR; omega)
    (by rw [busLen_eq]; exact H.clear.mono (by unfold bankLen; omega))
    (by rw [busLen_eq]; exact H.reset.mono (by unfold bankLen; omega))
    (by rw [busLen_eq]; exact H.pulse.mono (by unfold bankLen; omega))
    (by
      intro e h1 h2 u h3 h4
      rw [busLen_eq] at h1
      rw [gnextOf_getD, gnextOf_getD]
      exact hstable e h1 h2 u h3 h4)
    (by
      intro e h1 h2 e' h3
      rw [busLen_eq] at h1
      have := H.period e' e (by have := h3.1; omega) (by unfold bankLen at h1; omega) h3.2.1 h2
      omega) hv
  simpa only [gnextOf_getD, gnextOf_length] using h

/-- **The Gray pointer register's value contract**, which needs no stability assumption: a
violated edge is forgotten at the next clean one.  Only the glitch-free clause needs the
history, and it carries it itself (`Timed.CleanEdges`). -/
theorem bank_gray_val (H : BankOK clk d crn R) {v : List (BitVec 3)}
    (hv : v <+: BusReg.busOut clk (gnextOf d) crn) :
    RegOut 4 1 0#3 clk (fun u => (d.getD u default).gnext) d.length v := by
  have h := BusReg.busOut_regOut (clk := clk) (d := gnextOf d) (crn := crn) (R := R)
    (by have := H.hR; omega)
    (by rw [busLen_eq]; exact H.clear.mono (by unfold bankLen; omega))
    (by rw [busLen_eq]; exact H.reset.mono (by unfold bankLen; omega))
    (by rw [busLen_eq]; exact H.pulse.mono (by unfold bankLen; omega)) hv
  simpa only [gnextOf_getD, gnextOf_length] using h

/-- **The `empty` flag** is a bit of the state register. -/
theorem bank_empty (H : BankOK clk d crn R) {q : List (RSt 2)}
    (hq : q <+: StRegR.stOut clk (stOf d) crn) :
    ∃ p, RegOut 4 1 default clk (fun u => (d.getD u default).st) d.length p ∧
      q.map (·.empty) = p.map (·.empty) :=
  ⟨q, bank_st H hq, rfl⟩

/-! ### The contracts, per instant

The block files prove their contracts over a block's whole known history: the filters hold
everywhere, so the contract holds everywhere.  What `Timed.regBank` asks for is the per-instant
form --- at each instant, under the filters *before* that instant --- because that is the
discipline the domains keep, and a violation at one instant must not excuse the circuit at an
earlier one.

A netlist is causal, so the two are the same statement, and the passage from one to the other is
purely a matter of which inputs the whole-history theorem is applied to.  To read a contract at
`t`, apply it to the inputs **cut at `t`**: the cut circuit computes the same value at `t`, the
filters over the cut history are exactly the filters before `t`, and every block of the bank
reports exactly one instant past its inputs, so the cut circuit still reaches `t`. -/

section PerInstant

variable {t : Nat}

/-- Cutting the bank's inputs at `t` leaves a block whose horizon is exactly `t`. -/
theorem bankLen_take (h : t ≤ bankLen clk d crn) :
    bankLen (clk.take t) (d.take t) (crn.take t) = t := by
  unfold bankLen at h ⊢
  rw [List.length_take, List.length_take, List.length_take]
  omega

/-- ... and the filters over the cut history are the filters before `t`. -/
theorem bankOK_take (hR : 6 ≤ R) (h : t ≤ bankLen clk d crn)
    (G : GateOK 12 3 (R + 3) R clk crn t) : BankOK (clk.take t) (d.take t) (crn.take t) R := by
  have hc : t ≤ clk.length := by unfold bankLen at h; omega
  have hr : t ≤ crn.length := by unfold bankLen at h; omega
  have lc : (clk.take t).length = t := by rw [List.length_take]; omega
  have lr : (crn.take t).length = t := by rw [List.length_take]; omega
  exact { hR := hR
          clear := by rw [lr]; exact ClearOK.congr (List.take_prefix _ _) (by omega) G.clear
          reset := by rw [lc]; exact ResetOK.congr (List.take_prefix _ _) (by omega) G.reset
          pulse := by rw [lc]; exact PulseOK.congr (List.take_prefix _ _) (by omega) G.pulse
          period := by rw [lc]; exact ClockOK.congr (List.take_prefix _ _) (by omega) G.period }

theorem take_getD_st (u : Nat) (hu : u < (d.take t).length) :
    ((d.take t).getD u default).st = (d.getD u default).st := by
  rw [(List.take_prefix t d).getD_eq_left hu]

theorem take_getD_gnext (u : Nat) (hu : u < (d.take t).length) :
    ((d.take t).getD u default).gnext = (d.getD u default).gnext := by
  rw [(List.take_prefix t d).getD_eq_left hu]

/-- **The state register's contract, per instant.** -/
theorem bank_stG (hR : 6 ≤ R) {v : List (RSt 2)} (hv : v <+: StRegR.stOut clk (stOf d) crn) :
    RegOutG 4 1 default (GateOK 12 3 (R + 3) R clk crn) clk (fun u => (d.getD u default).st)
      d.length (bankLen clk d crn) v := by
  have hl := hv.length_le
  rw [StRegR.stOut_length, stLen_eq] at hl
  refine ⟨hl, fun t ht G => ?_⟩
  have htb : t ≤ bankLen clk d crn := by omega
  have hlt := bankLen_take (d := d) htb
  have hcut := bank_st (bankOK_take hR htb G)
    (v := StRegR.stOut (clk.take t) (stOf (d.take t)) (crn.take t)) List.prefix_rfl
  have hcl : (StRegR.stOut (clk.take t) (stOf (d.take t)) (crn.take t)).length = t + 1 := by
    rw [StRegR.stOut_length, stLen_eq, hlt]
  have hp : StRegR.stOut (clk.take t) (stOf (d.take t)) (crn.take t) <+: StRegR.stOut clk (stOf d) crn :=
    StRegR.stOut_mono (List.take_prefix _ _) (stOf_mono (List.take_prefix _ _)) (List.take_prefix _ _)
  have hct : t ≤ clk.length := by unfold bankLen at htb; omega
  refine RegAt.congr_out ?_ ((hcut.2 t (by omega)).mono (List.take_prefix _ _) take_getD_st
    (by rw [List.length_take]; unfold bankLen at htb; omega)
    (by rw [List.length_take]; omega) (by rw [List.length_take]; unfold bankLen at htb; omega))
  rw [hp.getD_eq_left (by omega), hv.getD_eq_left ht]

/-- **The Gray pointer register's contract, per instant.**  The stability the glitch-free clause
needs is the clause's own `CleanEdges`: cut at `t`, it is exactly the whole-history hypothesis
the block file asks for. -/
theorem bank_grayG (hR : 6 ≤ R) {v : List (BitVec 3)}
    (hv : v <+: BusReg.busOut clk (gnextOf d) crn) :
    BusRegOutG 4 1 (GateOK 12 3 (R + 3) R clk crn) clk (fun u => (d.getD u default).gnext)
      d.length (bankLen clk d crn) v := by
  have hl := hv.length_le
  rw [BusReg.busOut_length, busLen_eq] at hl
  have hpre : ∀ t, BusReg.busOut (clk.take t) (gnextOf (d.take t)) (crn.take t)
      <+: BusReg.busOut clk (gnextOf d) crn :=
    fun t => BusReg.busOut_mono (List.take_prefix _ _) (gnextOf_mono (List.take_prefix _ _))
      (List.take_prefix _ _)
  have hcl : ∀ t, t ≤ bankLen clk d crn →
      (BusReg.busOut (clk.take t) (gnextOf (d.take t)) (crn.take t)).length = t + 1 := by
    intro t htb; rw [BusReg.busOut_length, busLen_eq, bankLen_take (d := d) htb]
  refine ⟨⟨hl, fun t ht G => ?_⟩, fun t ht G => ?_⟩
  · have htb : t ≤ bankLen clk d crn := by omega
    have hcut := bank_gray_val (bankOK_take hR htb G)
      (v := BusReg.busOut (clk.take t) (gnextOf (d.take t)) (crn.take t)) List.prefix_rfl
    refine RegAt.congr_out ?_ ((hcut.2 t (by rw [hcl t htb]; omega)).mono (List.take_prefix _ _)
      take_getD_gnext (by rw [List.length_take]; unfold bankLen at htb; omega)
      (by rw [List.length_take]; unfold bankLen at htb; omega)
      (by rw [List.length_take]; unfold bankLen at htb; omega))
    rw [(hpre t).getD_eq_left (by rw [hcl t htb]; omega), hv.getD_eq_left ht]
  · intro hclean
    have htb : t ≤ bankLen clk d crn := by omega
    have hlk : t ≤ clk.length := by unfold bankLen at htb; omega
    have hld : t ≤ d.length := by unfold bankLen at htb; omega
    have hst : ∀ e, e < bankLen (clk.take t) (d.take t) (crn.take t) →
        riseAt (clk.take t) e = true → ∀ u, e - 2 ≤ u → u ≤ e →
          ((d.take t).getD u default).gnext = ((d.take t).getD e default).gnext := by
      intro e h1 h2 u h3 h4
      rw [bankLen_take (d := d) htb] at h1
      have hce : riseAt clk e = true := by
        rw [← riseAt_prefix (List.take_prefix t clk) (by rw [List.length_take]; omega)]
        exact h2
      have hs := hclean e h1 hce
      rw [take_getD_gnext u (by rw [List.length_take]; omega),
        take_getD_gnext e (by rw [List.length_take]; omega)]
      exact hs.2 u h3 h4
    have hcut := bank_gray (bankOK_take hR htb G) hst
      (v := BusReg.busOut (clk.take t) (gnextOf (d.take t)) (crn.take t)) List.prefix_rfl
    have hval : ∀ u, u ≤ t →
        (BusReg.busOut (clk.take t) (gnextOf (d.take t)) (crn.take t)).getD u 0#3 = v.getD u 0#3 := by
      intro u hu
      rw [(hpre t).getD_eq_left (by rw [hcl t htb]; omega), hv.getD_eq_left (by omega)]
    exact BusWinAt.congr_out hval ((hcut.2 t (by rw [hcl t htb]; omega)).mono (List.take_prefix _ _)
      take_getD_gnext (by rw [List.length_take]; omega) (by rw [List.length_take]; omega)
      (by rw [List.length_take]; omega)) hclean

/-- **The `empty` flag, per instant.** -/
theorem bank_emptyG (hR : 6 ≤ R) {q : List (RSt 2)} (hq : q <+: StRegR.stOut clk (stOf d) crn) :
    ∃ p, RegOutG 4 1 default (GateOK 12 3 (R + 3) R clk crn) clk (fun u => (d.getD u default).st)
      d.length (bankLen clk d crn) p ∧ q.map (·.empty) = p.map (·.empty) :=
  ⟨q, bank_stG hR hq, rfl⟩

end PerInstant

/-! ### The netlist -/

def bankGraph := [graphEnv|
    clk [type="io"];
    d [type="io"];
    clrn [type="io"];
    st [type="io"];
    empty [type="io"];
    gray [type="io"];

    unpN [type="unpackNext", typeImp=$(⟨_, unpackNext⟩)];
    clkF [type="fork2", typeImp=$(⟨_, Timed.fork2 Bool⟩)];
    crF [type="fork2", typeImp=$(⟨_, Timed.fork2 Bool⟩)];
    stR [type="streg", typeImp=$(⟨_, StRegR.stSpec⟩)];
    stF [type="forkSt", typeImp=$(⟨_, Timed.fork2 (RSt 2)⟩)];
    emptyA [type="emptyOf", typeImp=$(⟨_, emptyOf⟩)];
    grR [type="busreg", typeImp=$(⟨_, BusReg.busSpec⟩)];

    clk -> clkF [to="in"];
    d -> unpN [to="d"];
    clrn -> crF [to="in"];

    clkF -> stR [from="out1", to="clk"];
    clkF -> grR [from="out2", to="clk"];
    crF -> stR [from="out1", to="clrn"];
    crF -> grR [from="out2", to="clrn"];
    unpN -> stR [from="st", to="d"];
    unpN -> grR [from="gnext", to="d"];
    stR -> stF [from="q", to="in"];
    stF -> emptyA [from="out2", to="q"];

    stF -> st [from="out1"];
    emptyA -> empty [from="empty"];
    grR -> gray [from="q"];
  ]

@[drunfold_defs]
def bankLowered := bankGraph.1.lower_TR |>.get rfl

def kenv := bankGraph.2

@[drenv] theorem kenv_unpackNext : kenv.find? "unpackNext" = .some ⟨_, unpackNext⟩ := rfl
@[drenv] theorem kenv_fork2 : kenv.find? "fork2" = .some ⟨_, Timed.fork2 Bool⟩ := rfl
@[drenv] theorem kenv_streg : kenv.find? "streg" = .some ⟨_, StRegR.stSpec⟩ := rfl
@[drenv] theorem kenv_forkSt : kenv.find? "forkSt" = .some ⟨_, Timed.fork2 (RSt 2)⟩ := rfl
@[drenv] theorem kenv_emptyOf : kenv.find? "emptyOf" = .some ⟨_, emptyOf⟩ := rfl
@[drenv] theorem kenv_busreg : kenv.find? "busreg" = .some ⟨_, BusReg.busSpec⟩ := rfl

seal kenv in
def_module bankT : Type :=
  [T| bankLowered, kenv.find? ]
reduction_by
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type,
         ExprLow.build_module, ExprLow.build_module', toString]
  simp only [drenv]
  dsimp

seal kenv in
def_module bankNetlist : StringModule bankT :=
  [e| bankLowered, kenv.find? ]

-- HEADER_END (everything below is generated by gen/gen_bankr.py)

/-! ### The specification -/

/-- The bank as a single block: the state register, the Gray pointer register and the `empty`
bit, over the fields of the next-state bus. -/
@[drcomponents]
def bankSpec : StringModule (List Bool × List (RNext 2) × List Bool × List (RSt 2) ×
    List Bool × List (BitVec 3)) :=
  { inputs := [ (↑"clk", ⟨List Bool, fun s v s' => s.1 ⊏ v ∧ s' = (v, s.2)⟩)
              , (↑"d", ⟨List (RNext 2), fun s v s' => s.2.1 ⊏ v ∧ s' = (s.1, v, s.2.2)⟩)
              , (↑"clrn", ⟨List Bool, fun s v s' => s.2.2.1 ⊏ v ∧
                  s' = (s.1, s.2.1, v, s.2.2.2)⟩)
              ].toAssocList
    outputs := [ (↑"st", ⟨List (RSt 2), fun s v s' => s.2.2.2.1 <+: v ∧
                    v <+: StRegR.stOut s.1 (stOf s.2.1) s.2.2.1 ∧
                    s' = (s.1, s.2.1, s.2.2.1, v, s.2.2.2.2)⟩)
               , (↑"empty", ⟨List Bool, fun s v s' => s.2.2.2.2.1 <+: v ∧
                    v <+: (StRegR.stOut s.1 (stOf s.2.1) s.2.2.1).map (·.empty) ∧
                    s' = (s.1, s.2.1, s.2.2.1, s.2.2.2.1, v, s.2.2.2.2.2)⟩)
               , (↑"gray", ⟨List (BitVec 3), fun s v s' => s.2.2.2.2.2 <+: v ∧
                    v <+: BusReg.busOut s.1 (gnextOf s.2.1) s.2.2.1 ∧
                    s' = (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, v)⟩)
               ].toAssocList
    internals := []
    init_state := fun s => s = ([], [], [], [], [], []) }

instance : MatchInterface bankNetlist bankSpec := by
  dsimp [bankNetlist, bankSpec]
  solve_match_interface

/-! ### The invariant -/

structure Wf (stF_in : List (RSt 2)) (crF_in : List Bool) (stR_clk : List Bool) (stR_d : List (RSt 2)) (stR_clrn : List Bool) (clkF_in : List Bool) (unpN_d : List (RNext 2)) (emptyA_q : List (RSt 2)) (grR_clk : List Bool) (grR_d : List (BitVec 3)) (grR_clrn : List Bool) (grR_qh : List (BitVec 3)) (s : List Bool × List (RNext 2) × List Bool × List (RSt 2) × List Bool × List (BitVec 3)) : Prop where
  e_clk : clkF_in = s.1
  e_d : unpN_d = s.2.1
  e_crn : crF_in = s.2.2.1
  e_grh : grR_qh = s.2.2.2.2.2
  h_st : s.2.2.2.1 <+: stF_in
  h_empty : s.2.2.2.2.1 <+: emptyA_q.map (·.empty)
  w_stF_in : stF_in <+: StRegR.stOut stR_clk stR_d stR_clrn
  w_stR_clk : stR_clk <+: clkF_in
  w_stR_d : stR_d <+: stOf unpN_d
  w_stR_clrn : stR_clrn <+: crF_in
  w_emptyA_q : emptyA_q <+: stF_in
  w_grR_clk : grR_clk <+: clkF_in
  w_grR_d : grR_d <+: gnextOf unpN_d
  w_grR_clrn : grR_clrn <+: crF_in

def ψ (i : bankT) (s : List Bool × List (RNext 2) × List Bool × List (RSt 2) × List Bool × List (BitVec 3)) : Prop :=
  Wf i.1 i.2.1 i.2.2.1.1 i.2.2.1.2.1 i.2.2.1.2.2.1 i.2.2.2.1 i.2.2.2.2.1 i.2.2.2.2.2.1 i.2.2.2.2.2.2.1 i.2.2.2.2.2.2.2.1 i.2.2.2.2.2.2.2.2.1 i.2.2.2.2.2.2.2.2.2 s

theorem Wf.init : Wf [] [] [] [] [] [] [] [] [] [] [] [] ([], [], [], [], [], []) :=
  ⟨rfl, rfl, rfl, rfl, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix, List.nil_prefix⟩

section SpecRules
variable (sp : List Bool × List (RNext 2) × List Bool × List (RSt 2) × List Bool × List (BitVec 3))

theorem spec_in_clk (v : List Bool) (h : sp.1 ⊏ v) :
    (bankSpec.inputs.getIO ↑"clk").2 sp v (v, sp.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem spec_in_d (v : List (RNext 2)) (h : sp.2.1 ⊏ v) :
    (bankSpec.inputs.getIO ↑"d").2 sp v (sp.1, v, sp.2.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem spec_in_clrn (v : List Bool) (h : sp.2.2.1 ⊏ v) :
    (bankSpec.inputs.getIO ↑"clrn").2 sp v (sp.1, sp.2.1, v, sp.2.2.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem spec_out_st (v : List (RSt 2)) (h1 : sp.2.2.2.1 <+: v)
    (h2 : v <+: StRegR.stOut sp.1 (stOf sp.2.1) sp.2.2.1) :
    (bankSpec.outputs.getIO ↑"st").2 sp v (sp.1, sp.2.1, sp.2.2.1, v, sp.2.2.2.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h1, h2, rfl⟩

theorem spec_out_empty (v : List Bool) (h1 : sp.2.2.2.2.1 <+: v)
    (h2 : v <+: (StRegR.stOut sp.1 (stOf sp.2.1) sp.2.2.1).map (·.empty)) :
    (bankSpec.outputs.getIO ↑"empty").2 sp v (sp.1, sp.2.1, sp.2.2.1, sp.2.2.2.1, v, sp.2.2.2.2.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h1, h2, rfl⟩

theorem spec_out_gray (v : List (BitVec 3)) (h1 : sp.2.2.2.2.2 <+: v)
    (h2 : v <+: BusReg.busOut sp.1 (gnextOf sp.2.1) sp.2.2.1) :
    (bankSpec.outputs.getIO ↑"gray").2 sp v (sp.1, sp.2.1, sp.2.2.1, sp.2.2.2.1, sp.2.2.2.2.1, v) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h1, h2, rfl⟩

end SpecRules

section Cases
variable {stF_in : List (RSt 2)} {crF_in : List Bool} {stR_clk : List Bool} {stR_d : List (RSt 2)} {stR_clrn : List Bool} {clkF_in : List Bool} {unpN_d : List (RNext 2)} {emptyA_q : List (RSt 2)} {grR_clk : List Bool} {grR_d : List (BitVec 3)} {grR_clrn : List Bool} {grR_qh : List (BitVec 3)} {sp : List Bool × List (RNext 2) × List Bool × List (RSt 2) × List Bool × List (BitVec 3)}
  (Hψ : Wf stF_in crF_in stR_clk stR_d stR_clrn clkF_in unpN_d emptyA_q grR_clk grR_d grR_clrn grR_qh sp)
include Hψ

theorem in_clk (v : List Bool) (h : clkF_in ⊏ v) :
    Wf stF_in crF_in stR_clk stR_d stR_clrn (v) unpN_d emptyA_q grR_clk grR_d grR_clrn grR_qh (v, sp.2) := by
  have hm : clkF_in <+: v := h.isPrefix
  exact { e_clk := rfl
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          e_grh := Hψ.e_grh
          h_st := Hψ.h_st
          h_empty := Hψ.h_empty
          w_stF_in := Hψ.w_stF_in
          w_stR_clk := Hψ.w_stR_clk.trans hm
          w_stR_d := Hψ.w_stR_d
          w_stR_clrn := Hψ.w_stR_clrn
          w_emptyA_q := Hψ.w_emptyA_q
          w_grR_clk := Hψ.w_grR_clk.trans hm
          w_grR_d := Hψ.w_grR_d
          w_grR_clrn := Hψ.w_grR_clrn }

theorem in_d (v : List (RNext 2)) (h : unpN_d ⊏ v) :
    Wf stF_in crF_in stR_clk stR_d stR_clrn clkF_in (v) emptyA_q grR_clk grR_d grR_clrn grR_qh (sp.1, v, sp.2.2) := by
  have hm : unpN_d <+: v := h.isPrefix
  exact { e_clk := Hψ.e_clk
          e_d := rfl
          e_crn := Hψ.e_crn
          e_grh := Hψ.e_grh
          h_st := Hψ.h_st
          h_empty := Hψ.h_empty
          w_stF_in := Hψ.w_stF_in
          w_stR_clk := Hψ.w_stR_clk
          w_stR_d := Hψ.w_stR_d.trans (stOf_mono hm)
          w_stR_clrn := Hψ.w_stR_clrn
          w_emptyA_q := Hψ.w_emptyA_q
          w_grR_clk := Hψ.w_grR_clk
          w_grR_d := Hψ.w_grR_d.trans (gnextOf_mono hm)
          w_grR_clrn := Hψ.w_grR_clrn }

theorem in_clrn (v : List Bool) (h : crF_in ⊏ v) :
    Wf stF_in (v) stR_clk stR_d stR_clrn clkF_in unpN_d emptyA_q grR_clk grR_d grR_clrn grR_qh (sp.1, sp.2.1, v, sp.2.2.2) := by
  have hm : crF_in <+: v := h.isPrefix
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := rfl
          e_grh := Hψ.e_grh
          h_st := Hψ.h_st
          h_empty := Hψ.h_empty
          w_stF_in := Hψ.w_stF_in
          w_stR_clk := Hψ.w_stR_clk
          w_stR_d := Hψ.w_stR_d
          w_stR_clrn := Hψ.w_stR_clrn.trans hm
          w_emptyA_q := Hψ.w_emptyA_q
          w_grR_clk := Hψ.w_grR_clk
          w_grR_d := Hψ.w_grR_d
          w_grR_clrn := Hψ.w_grR_clrn.trans hm }

theorem int_0 (_h : stR_clk ⊏ clkF_in) :
    Wf stF_in crF_in (clkF_in) stR_d stR_clrn clkF_in unpN_d emptyA_q grR_clk grR_d grR_clrn grR_qh sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          e_grh := Hψ.e_grh
          h_st := Hψ.h_st
          h_empty := Hψ.h_empty
          w_stF_in := Hψ.w_stF_in.trans (StRegR.stOut_mono Hψ.w_stR_clk List.prefix_rfl List.prefix_rfl)
          w_stR_clk := List.prefix_rfl
          w_stR_d := Hψ.w_stR_d
          w_stR_clrn := Hψ.w_stR_clrn
          w_emptyA_q := Hψ.w_emptyA_q
          w_grR_clk := Hψ.w_grR_clk
          w_grR_d := Hψ.w_grR_d
          w_grR_clrn := Hψ.w_grR_clrn }

theorem int_1 (_h : grR_clk ⊏ clkF_in) :
    Wf stF_in crF_in stR_clk stR_d stR_clrn clkF_in unpN_d emptyA_q (clkF_in) grR_d grR_clrn grR_qh sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          e_grh := Hψ.e_grh
          h_st := Hψ.h_st
          h_empty := Hψ.h_empty
          w_stF_in := Hψ.w_stF_in
          w_stR_clk := Hψ.w_stR_clk
          w_stR_d := Hψ.w_stR_d
          w_stR_clrn := Hψ.w_stR_clrn
          w_emptyA_q := Hψ.w_emptyA_q
          w_grR_clk := List.prefix_rfl
          w_grR_d := Hψ.w_grR_d
          w_grR_clrn := Hψ.w_grR_clrn }

theorem int_2 (_h : stR_clrn ⊏ crF_in) :
    Wf stF_in crF_in stR_clk stR_d (crF_in) clkF_in unpN_d emptyA_q grR_clk grR_d grR_clrn grR_qh sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          e_grh := Hψ.e_grh
          h_st := Hψ.h_st
          h_empty := Hψ.h_empty
          w_stF_in := Hψ.w_stF_in.trans (StRegR.stOut_mono List.prefix_rfl List.prefix_rfl Hψ.w_stR_clrn)
          w_stR_clk := Hψ.w_stR_clk
          w_stR_d := Hψ.w_stR_d
          w_stR_clrn := List.prefix_rfl
          w_emptyA_q := Hψ.w_emptyA_q
          w_grR_clk := Hψ.w_grR_clk
          w_grR_d := Hψ.w_grR_d
          w_grR_clrn := Hψ.w_grR_clrn }

theorem int_3 (_h : grR_clrn ⊏ crF_in) :
    Wf stF_in crF_in stR_clk stR_d stR_clrn clkF_in unpN_d emptyA_q grR_clk grR_d (crF_in) grR_qh sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          e_grh := Hψ.e_grh
          h_st := Hψ.h_st
          h_empty := Hψ.h_empty
          w_stF_in := Hψ.w_stF_in
          w_stR_clk := Hψ.w_stR_clk
          w_stR_d := Hψ.w_stR_d
          w_stR_clrn := Hψ.w_stR_clrn
          w_emptyA_q := Hψ.w_emptyA_q
          w_grR_clk := Hψ.w_grR_clk
          w_grR_d := Hψ.w_grR_d
          w_grR_clrn := List.prefix_rfl }

theorem int_4 (_h : stR_d ⊏ stOf unpN_d) :
    Wf stF_in crF_in stR_clk (stOf unpN_d) stR_clrn clkF_in unpN_d emptyA_q grR_clk grR_d grR_clrn grR_qh sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          e_grh := Hψ.e_grh
          h_st := Hψ.h_st
          h_empty := Hψ.h_empty
          w_stF_in := Hψ.w_stF_in.trans (StRegR.stOut_mono List.prefix_rfl Hψ.w_stR_d List.prefix_rfl)
          w_stR_clk := Hψ.w_stR_clk
          w_stR_d := List.prefix_rfl
          w_stR_clrn := Hψ.w_stR_clrn
          w_emptyA_q := Hψ.w_emptyA_q
          w_grR_clk := Hψ.w_grR_clk
          w_grR_d := Hψ.w_grR_d
          w_grR_clrn := Hψ.w_grR_clrn }

theorem int_5 (_h : grR_d ⊏ gnextOf unpN_d) :
    Wf stF_in crF_in stR_clk stR_d stR_clrn clkF_in unpN_d emptyA_q grR_clk (gnextOf unpN_d) grR_clrn grR_qh sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          e_grh := Hψ.e_grh
          h_st := Hψ.h_st
          h_empty := Hψ.h_empty
          w_stF_in := Hψ.w_stF_in
          w_stR_clk := Hψ.w_stR_clk
          w_stR_d := Hψ.w_stR_d
          w_stR_clrn := Hψ.w_stR_clrn
          w_emptyA_q := Hψ.w_emptyA_q
          w_grR_clk := Hψ.w_grR_clk
          w_grR_d := List.prefix_rfl
          w_grR_clrn := Hψ.w_grR_clrn }

theorem int_6 {out : List (RSt 2)} (_h : stF_in ⊏ out) (hout : out <+: StRegR.stOut stR_clk stR_d stR_clrn) :
    Wf (out) crF_in stR_clk stR_d stR_clrn clkF_in unpN_d emptyA_q grR_clk grR_d grR_clrn grR_qh sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          e_grh := Hψ.e_grh
          h_st := Hψ.h_st.trans (_h.isPrefix)
          h_empty := Hψ.h_empty
          w_stF_in := hout
          w_stR_clk := Hψ.w_stR_clk
          w_stR_d := Hψ.w_stR_d
          w_stR_clrn := Hψ.w_stR_clrn
          w_emptyA_q := Hψ.w_emptyA_q.trans (_h.isPrefix)
          w_grR_clk := Hψ.w_grR_clk
          w_grR_d := Hψ.w_grR_d
          w_grR_clrn := Hψ.w_grR_clrn }

theorem int_7 (_h : emptyA_q ⊏ stF_in) :
    Wf stF_in crF_in stR_clk stR_d stR_clrn clkF_in unpN_d (stF_in) grR_clk grR_d grR_clrn grR_qh sp := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          e_grh := Hψ.e_grh
          h_st := Hψ.h_st
          h_empty := Hψ.h_empty.trans (Hψ.w_emptyA_q.map _)
          w_stF_in := Hψ.w_stF_in
          w_stR_clk := Hψ.w_stR_clk
          w_stR_d := Hψ.w_stR_d
          w_stR_clrn := Hψ.w_stR_clrn
          w_emptyA_q := List.prefix_rfl
          w_grR_clk := Hψ.w_grR_clk
          w_grR_d := Hψ.w_grR_d
          w_grR_clrn := Hψ.w_grR_clrn }

/-- Each block sees prefixes of the bank's own inputs. -/
theorem out_st : stF_in <+: StRegR.stOut sp.1 (stOf sp.2.1) sp.2.2.1 :=
  Hψ.w_stF_in.trans (StRegR.stOut_mono (Hψ.w_stR_clk.trans (Hψ.e_clk ▸ List.prefix_rfl))
    (Hψ.w_stR_d.trans (stOf_mono (Hψ.e_d ▸ List.prefix_rfl)))
    (Hψ.w_stR_clrn.trans (Hψ.e_crn ▸ List.prefix_rfl)))

theorem out_empty : emptyA_q.map (·.empty) <+: (StRegR.stOut sp.1 (stOf sp.2.1) sp.2.2.1).map (·.empty) :=
  (Hψ.w_emptyA_q.trans (out_st Hψ)).map _

theorem out_gray {v : List (BitVec 3)} (h : v <+: BusReg.busOut grR_clk grR_d grR_clrn) :
    v <+: BusReg.busOut sp.1 (gnextOf sp.2.1) sp.2.2.1 :=
  h.trans (BusReg.busOut_mono (Hψ.w_grR_clk.trans (Hψ.e_clk ▸ List.prefix_rfl))
    (Hψ.w_grR_d.trans (gnextOf_mono (Hψ.e_d ▸ List.prefix_rfl)))
    (Hψ.w_grR_clrn.trans (Hψ.e_crn ▸ List.prefix_rfl)))

/-! What it has reported it has reported: two ports leave through an adapter, which keeps
no record, so the block keeps it; the third leaves through a register that keeps its own,
and the block's record is that one. -/

theorem out_st_wf : Wf stF_in crF_in stR_clk stR_d stR_clrn clkF_in unpN_d emptyA_q grR_clk grR_d grR_clrn grR_qh (sp.1, sp.2.1, sp.2.2.1, stF_in, sp.2.2.2.2) := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          e_grh := Hψ.e_grh
          h_st := List.prefix_rfl
          h_empty := Hψ.h_empty
          w_stF_in := Hψ.w_stF_in
          w_stR_clk := Hψ.w_stR_clk
          w_stR_d := Hψ.w_stR_d
          w_stR_clrn := Hψ.w_stR_clrn
          w_emptyA_q := Hψ.w_emptyA_q
          w_grR_clk := Hψ.w_grR_clk
          w_grR_d := Hψ.w_grR_d
          w_grR_clrn := Hψ.w_grR_clrn }

theorem out_empty_wf : Wf stF_in crF_in stR_clk stR_d stR_clrn clkF_in unpN_d emptyA_q grR_clk grR_d grR_clrn grR_qh (sp.1, sp.2.1, sp.2.2.1, sp.2.2.2.1, emptyA_q.map (·.empty), sp.2.2.2.2.2) := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          e_grh := Hψ.e_grh
          h_st := Hψ.h_st
          h_empty := List.prefix_rfl
          w_stF_in := Hψ.w_stF_in
          w_stR_clk := Hψ.w_stR_clk
          w_stR_d := Hψ.w_stR_d
          w_stR_clrn := Hψ.w_stR_clrn
          w_emptyA_q := Hψ.w_emptyA_q
          w_grR_clk := Hψ.w_grR_clk
          w_grR_d := Hψ.w_grR_d
          w_grR_clrn := Hψ.w_grR_clrn }

theorem out_gray_wf {v : List (BitVec 3)} : Wf stF_in crF_in stR_clk stR_d stR_clrn clkF_in unpN_d emptyA_q grR_clk grR_d grR_clrn (v) (sp.1, sp.2.1, sp.2.2.1, sp.2.2.2.1, sp.2.2.2.2.1, v) := by
  exact { e_clk := Hψ.e_clk
          e_d := Hψ.e_d
          e_crn := Hψ.e_crn
          e_grh := rfl
          h_st := Hψ.h_st
          h_empty := Hψ.h_empty
          w_stF_in := Hψ.w_stF_in
          w_stR_clk := Hψ.w_stR_clk
          w_stR_d := Hψ.w_stR_d
          w_stR_clrn := Hψ.w_stR_clrn
          w_emptyA_q := Hψ.w_emptyA_q
          w_grR_clk := Hψ.w_grR_clk
          w_grR_d := Hψ.w_grR_d
          w_grR_clrn := Hψ.w_grR_clrn }

end Cases

/-! ### The refinement -/

theorem int_case_0 (s : List Bool × List (RNext 2) × List Bool × List (RSt 2) × List Bool × List (BitVec 3)) (i mid : bankT) (Hψ : ψ i s)
    (Hrule : (bankNetlist.internals.getD 0 (fun _ _ => False)) i mid) :
    ∃ s', existSR bankSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨stF_in, crF_in, ⟨stR_clk, stR_d, stR_clrn, stR_qh⟩, clkF_in, unpN_d, emptyA_q, ⟨grR_clk, grR_d, grR_clrn, grR_qh⟩⟩ := i
  obtain ⟨m_stF_in, m_crF_in, ⟨m_stR_clk, m_stR_d, m_stR_clrn, m_stR_qh⟩, m_clkF_in, m_unpN_d, m_emptyA_q, ⟨m_grR_clk, m_grR_d, m_grR_clrn, m_grR_qh⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨c_stF_in, c_crF_in, ⟨c_stR_clk, c_stR_d, c_stR_clrn, c_stR_qh⟩, c_clkF_in, c_unpN_d, c_emptyA_q, ⟨c_grR_clk, c_grR_d, c_grR_clrn, c_grR_qh⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_0 Hψ ‹_›⟩

theorem int_case_1 (s : List Bool × List (RNext 2) × List Bool × List (RSt 2) × List Bool × List (BitVec 3)) (i mid : bankT) (Hψ : ψ i s)
    (Hrule : (bankNetlist.internals.getD 1 (fun _ _ => False)) i mid) :
    ∃ s', existSR bankSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨stF_in, crF_in, ⟨stR_clk, stR_d, stR_clrn, stR_qh⟩, clkF_in, unpN_d, emptyA_q, ⟨grR_clk, grR_d, grR_clrn, grR_qh⟩⟩ := i
  obtain ⟨m_stF_in, m_crF_in, ⟨m_stR_clk, m_stR_d, m_stR_clrn, m_stR_qh⟩, m_clkF_in, m_unpN_d, m_emptyA_q, ⟨m_grR_clk, m_grR_d, m_grR_clrn, m_grR_qh⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨c_stF_in, c_crF_in, ⟨c_stR_clk, c_stR_d, c_stR_clrn, c_stR_qh⟩, c_clkF_in, c_unpN_d, c_emptyA_q, ⟨c_grR_clk, c_grR_d, c_grR_clrn, c_grR_qh⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_1 Hψ ‹_›⟩

theorem int_case_2 (s : List Bool × List (RNext 2) × List Bool × List (RSt 2) × List Bool × List (BitVec 3)) (i mid : bankT) (Hψ : ψ i s)
    (Hrule : (bankNetlist.internals.getD 2 (fun _ _ => False)) i mid) :
    ∃ s', existSR bankSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨stF_in, crF_in, ⟨stR_clk, stR_d, stR_clrn, stR_qh⟩, clkF_in, unpN_d, emptyA_q, ⟨grR_clk, grR_d, grR_clrn, grR_qh⟩⟩ := i
  obtain ⟨m_stF_in, m_crF_in, ⟨m_stR_clk, m_stR_d, m_stR_clrn, m_stR_qh⟩, m_clkF_in, m_unpN_d, m_emptyA_q, ⟨m_grR_clk, m_grR_d, m_grR_clrn, m_grR_qh⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨c_stF_in, c_crF_in, ⟨c_stR_clk, c_stR_d, c_stR_clrn, c_stR_qh⟩, c_clkF_in, c_unpN_d, c_emptyA_q, ⟨c_grR_clk, c_grR_d, c_grR_clrn, c_grR_qh⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_2 Hψ ‹_›⟩

theorem int_case_3 (s : List Bool × List (RNext 2) × List Bool × List (RSt 2) × List Bool × List (BitVec 3)) (i mid : bankT) (Hψ : ψ i s)
    (Hrule : (bankNetlist.internals.getD 3 (fun _ _ => False)) i mid) :
    ∃ s', existSR bankSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨stF_in, crF_in, ⟨stR_clk, stR_d, stR_clrn, stR_qh⟩, clkF_in, unpN_d, emptyA_q, ⟨grR_clk, grR_d, grR_clrn, grR_qh⟩⟩ := i
  obtain ⟨m_stF_in, m_crF_in, ⟨m_stR_clk, m_stR_d, m_stR_clrn, m_stR_qh⟩, m_clkF_in, m_unpN_d, m_emptyA_q, ⟨m_grR_clk, m_grR_d, m_grR_clrn, m_grR_qh⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨c_stF_in, c_crF_in, ⟨c_stR_clk, c_stR_d, c_stR_clrn, c_stR_qh⟩, c_clkF_in, c_unpN_d, c_emptyA_q, ⟨c_grR_clk, c_grR_d, c_grR_clrn, c_grR_qh⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_3 Hψ ‹_›⟩

theorem int_case_4 (s : List Bool × List (RNext 2) × List Bool × List (RSt 2) × List Bool × List (BitVec 3)) (i mid : bankT) (Hψ : ψ i s)
    (Hrule : (bankNetlist.internals.getD 4 (fun _ _ => False)) i mid) :
    ∃ s', existSR bankSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨stF_in, crF_in, ⟨stR_clk, stR_d, stR_clrn, stR_qh⟩, clkF_in, unpN_d, emptyA_q, ⟨grR_clk, grR_d, grR_clrn, grR_qh⟩⟩ := i
  obtain ⟨m_stF_in, m_crF_in, ⟨m_stR_clk, m_stR_d, m_stR_clrn, m_stR_qh⟩, m_clkF_in, m_unpN_d, m_emptyA_q, ⟨m_grR_clk, m_grR_d, m_grR_clrn, m_grR_qh⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨c_stF_in, c_crF_in, ⟨c_stR_clk, c_stR_d, c_stR_clrn, c_stR_qh⟩, c_clkF_in, c_unpN_d, c_emptyA_q, ⟨c_grR_clk, c_grR_d, c_grR_clrn, c_grR_qh⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_4 Hψ ‹_›⟩

theorem int_case_5 (s : List Bool × List (RNext 2) × List Bool × List (RSt 2) × List Bool × List (BitVec 3)) (i mid : bankT) (Hψ : ψ i s)
    (Hrule : (bankNetlist.internals.getD 5 (fun _ _ => False)) i mid) :
    ∃ s', existSR bankSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨stF_in, crF_in, ⟨stR_clk, stR_d, stR_clrn, stR_qh⟩, clkF_in, unpN_d, emptyA_q, ⟨grR_clk, grR_d, grR_clrn, grR_qh⟩⟩ := i
  obtain ⟨m_stF_in, m_crF_in, ⟨m_stR_clk, m_stR_d, m_stR_clrn, m_stR_qh⟩, m_clkF_in, m_unpN_d, m_emptyA_q, ⟨m_grR_clk, m_grR_d, m_grR_clrn, m_grR_qh⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨c_stF_in, c_crF_in, ⟨c_stR_clk, c_stR_d, c_stR_clrn, c_stR_qh⟩, c_clkF_in, c_unpN_d, c_emptyA_q, ⟨c_grR_clk, c_grR_d, c_grR_clrn, c_grR_qh⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_5 Hψ ‹_›⟩

theorem int_case_6 (s : List Bool × List (RNext 2) × List Bool × List (RSt 2) × List Bool × List (BitVec 3)) (i mid : bankT) (Hψ : ψ i s)
    (Hrule : (bankNetlist.internals.getD 6 (fun _ _ => False)) i mid) :
    ∃ s', existSR bankSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨stF_in, crF_in, ⟨stR_clk, stR_d, stR_clrn, stR_qh⟩, clkF_in, unpN_d, emptyA_q, ⟨grR_clk, grR_d, grR_clrn, grR_qh⟩⟩ := i
  obtain ⟨m_stF_in, m_crF_in, ⟨m_stR_clk, m_stR_d, m_stR_clrn, m_stR_qh⟩, m_clkF_in, m_unpN_d, m_emptyA_q, ⟨m_grR_clk, m_grR_d, m_grR_clrn, m_grR_qh⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨c_stF_in, c_crF_in, ⟨c_stR_clk, c_stR_d, c_stR_clrn, c_stR_qh⟩, c_clkF_in, c_unpN_d, c_emptyA_q, ⟨c_grR_clk, c_grR_d, c_grR_clrn, c_grR_qh⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_6 Hψ ‹_› ‹_›⟩

theorem int_case_7 (s : List Bool × List (RNext 2) × List Bool × List (RSt 2) × List Bool × List (BitVec 3)) (i mid : bankT) (Hψ : ψ i s)
    (Hrule : (bankNetlist.internals.getD 7 (fun _ _ => False)) i mid) :
    ∃ s', existSR bankSpec.internals s s' ∧ ψ mid s' := by
  obtain ⟨stF_in, crF_in, ⟨stR_clk, stR_d, stR_clrn, stR_qh⟩, clkF_in, unpN_d, emptyA_q, ⟨grR_clk, grR_d, grR_clrn, grR_qh⟩⟩ := i
  obtain ⟨m_stF_in, m_crF_in, ⟨m_stR_clk, m_stR_d, m_stR_clrn, m_stR_qh⟩, m_clkF_in, m_unpN_d, m_emptyA_q, ⟨m_grR_clk, m_grR_d, m_grR_clrn, m_grR_qh⟩⟩ := mid
  dsimp only [ψ] at Hψ ⊢
  have H := Hrule.1 rfl
  clear Hrule
  obtain ⟨⟨c_stF_in, c_crF_in, ⟨c_stR_clk, c_stR_d, c_stR_clrn, c_stR_qh⟩, c_clkF_in, c_unpN_d, c_emptyA_q, ⟨c_grR_clk, c_grR_d, c_grR_clrn, c_grR_qh⟩⟩, out, Hrule⟩ := H
  simp only [Prod.mk.injEq, and_assoc, and_true, true_and] at Hrule
  repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
  exact ⟨s, existSR_reflexive, int_7 Hψ ‹_›⟩

theorem bankNetlist_internals_eq : bankNetlist.internals = [bankNetlist.internals.getD 0 (fun _ _ => False), bankNetlist.internals.getD 1 (fun _ _ => False), bankNetlist.internals.getD 2 (fun _ _ => False), bankNetlist.internals.getD 3 (fun _ _ => False), bankNetlist.internals.getD 4 (fun _ _ => False), bankNetlist.internals.getD 5 (fun _ _ => False), bankNetlist.internals.getD 6 (fun _ _ => False), bankNetlist.internals.getD 7 (fun _ _ => False)] := rfl

theorem refines_ψ : bankNetlist ⊑_{ψ} bankSpec := by
  intro i s Hψ
  constructor
  · intro ident mid_i v Hrule
    obtain ⟨stF_in, crF_in, ⟨stR_clk, stR_d, stR_clrn, stR_qh⟩, clkF_in, unpN_d, emptyA_q, ⟨grR_clk, grR_d, grR_clrn, grR_qh⟩⟩ := i
    dsimp only [ψ] at Hψ
    obtain ⟨m_stF_in, m_crF_in, ⟨m_stR_clk, m_stR_d, m_stR_clrn, m_stR_qh⟩, m_clkF_in, m_unpN_d, m_emptyA_q, ⟨m_grR_clk, m_grR_d, m_grR_clrn, m_grR_qh⟩⟩ := mid_i
    case_transition Hcontains : Module.inputs bankNetlist, ident, (PortMap.getIO_not_contained_false' Hrule)
    dsimp only [bankNetlist] at Hcontains
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
    obtain ⟨stF_in, crF_in, ⟨stR_clk, stR_d, stR_clrn, stR_qh⟩, clkF_in, unpN_d, emptyA_q, ⟨grR_clk, grR_d, grR_clrn, grR_qh⟩⟩ := i
    dsimp only [ψ] at Hψ
    obtain ⟨m_stF_in, m_crF_in, ⟨m_stR_clk, m_stR_d, m_stR_clrn, m_stR_qh⟩, m_clkF_in, m_unpN_d, m_emptyA_q, ⟨m_grR_clk, m_grR_d, m_grR_clrn, m_grR_qh⟩⟩ := mid_i
    case_transition Hcontains : Module.outputs bankNetlist, ident, (PortMap.getIO_not_contained_false' Hrule)
    dsimp only [bankNetlist] at Hcontains
    simp at Hcontains
    rcases Hcontains with h | h | h
    all_goals subst h
    all_goals rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule
    all_goals dsimp only at Hrule
    all_goals simp only [Prod.mk.injEq, and_assoc] at Hrule
    all_goals repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
    all_goals first
      | exact ⟨s, _, existSR_reflexive, spec_out_st s _ Hψ.h_st (out_st Hψ), out_st_wf Hψ⟩
      | exact ⟨s, _, existSR_reflexive, spec_out_empty s _ Hψ.h_empty (out_empty Hψ),
          out_empty_wf Hψ⟩
      | exact ⟨s, _, existSR_reflexive, spec_out_gray s _ (Hψ.e_grh ▸ ‹_›)
          (out_gray Hψ ‹_›), out_gray_wf Hψ⟩
  · intro rule mid_i Hin Hrule
    rw [bankNetlist_internals_eq] at Hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at Hin
    rcases Hin with h | h | h | h | h | h | h | h
    · subst h; exact int_case_0 s i mid_i Hψ Hrule
    · subst h; exact int_case_1 s i mid_i Hψ Hrule
    · subst h; exact int_case_2 s i mid_i Hψ Hrule
    · subst h; exact int_case_3 s i mid_i Hψ Hrule
    · subst h; exact int_case_4 s i mid_i Hψ Hrule
    · subst h; exact int_case_5 s i mid_i Hψ Hrule
    · subst h; exact int_case_6 s i mid_i Hψ Hrule
    · subst h; exact int_case_7 s i mid_i Hψ Hrule

theorem refines_initial : Module.refines_initial bankNetlist bankSpec ψ := by
  intro i hi
  obtain ⟨stF_in, crF_in, ⟨stR_clk, stR_d, stR_clrn, stR_qh⟩, clkF_in, unpN_d, emptyA_q, ⟨grR_clk, grR_d, grR_clrn, grR_qh⟩⟩ := i
  dsimp only [bankNetlist] at hi
  simp only [Prod.mk.injEq, and_assoc] at hi
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hi
  exact ⟨([], [], [], [], [], []), rfl, Wf.init⟩

/-- **The two registers refine the read domain's register bank.** -/
theorem bank_refines : bankNetlist ⊑ bankSpec :=
  ⟨inferInstance, ψ, refines_ψ, refines_initial⟩

end Graphiti.AsyncFifo.BankR
