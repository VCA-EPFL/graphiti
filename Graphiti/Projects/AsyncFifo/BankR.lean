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

/-! ### The netlist, as an index type

Each wire holds a prefix of what drives it.  The wires carry different things -- bits, state
words, the Gray bus -- so this is `Netlist.Het`'s invariant, indexed by what each wire
carries. -/

open Graphiti.AsyncFifo.Netlist

/-- The eight driven wires.  The bank's own clock, next-state bus and clear are not among them:
they are inputs, closed over by `drv`. -/
inductive W
  | stR_clk | stR_d | stR_clrn
  | grR_clk | grR_d | grR_clrn
  | stF_in | emptyA_q
  deriving DecidableEq

/-- What each wire carries. -/
def Ty : W → Type
  | .stR_d | .stF_in | .emptyA_q => RSt 2
  | .grR_d => BitVec 3
  | _ => Bool

/-- What drives each wire, and the only place the shape of this netlist is written down: the
forks hand both registers the clock and the clear, `unpN` splits the next-state bus, the state
register feeds its own fork, and the `empty` adapter reads that fork. -/
def drv (clk crn : List Bool) (d : List (RNext 2)) : Het.Drv Ty
  | _, .stR_clk | _, .grR_clk => clk
  | _, .stR_clrn | _, .grR_clrn => crn
  | _, .stR_d => stOf d
  | _, .grR_d => gnextOf d
  | w, .stF_in => StRegR.stOut (w .stR_clk) (w .stR_d) (w .stR_clrn)
  | w, .emptyA_q => w .stF_in

/-- The two cases that are not the identity are named: trying `StRegR.stOut_mono` on a wire it
does not drive makes the unifier unfold `stOut`, which is seven `dffOut`s deep. -/
theorem drv_mono {clk crn d} : Het.Mono (drv clk crn d) := by
  intro a b h k
  cases k <;> simp only [drv]
  case stF_in => exact StRegR.stOut_mono (h .stR_clk) (h .stR_d) (h .stR_clrn)
  case emptyA_q => exact h .stF_in
  all_goals exact List.prefix_rfl

/-- Growing the bank's own inputs grows every driver. -/
theorem drv_env {clk clk' crn crn' : List Bool} {d d' : List (RNext 2)}
    (hc : clk <+: clk') (hr : crn <+: crn') (hd : d <+: d') (w : Het.Wires Ty) (k : W) :
    drv clk crn d w k <+: drv clk' crn' d' w k := by
  cases k <;> simp only [drv] <;>
    first
      | exact List.prefix_rfl | exact hc | exact hr
      | exact stOf_mono hd | exact gnextOf_mono hd

/-- The reduced state is a nested product; `wires` reads it as an assignment. -/
def wires (i : bankT) : Het.Wires Ty
  | .stF_in => i.1 | .emptyA_q => i.2.2.2.2.2.1
  | .stR_clk => i.2.2.1.1 | .stR_d => i.2.2.1.2.1 | .stR_clrn => i.2.2.1.2.2.1
  | .grR_clk => i.2.2.2.2.2.2.1 | .grR_d => i.2.2.2.2.2.2.2.1
  | .grR_clrn => i.2.2.2.2.2.2.2.2.1

/-- The invariant: the wires are well formed, the three inputs the netlist holds are the
specification's, the registered output is what it has reported, and the two combinational
outputs have reported no more than the wire behind them holds. -/
def ψ (i : bankT) (s : List Bool × List (RNext 2) × List Bool × List (RSt 2) × List Bool ×
    List (BitVec 3)) : Prop :=
  Het.Wf (drv s.1 s.2.2.1 s.2.1) (wires i)
    ∧ i.2.2.2.1 = s.1 ∧ i.2.2.2.2.1 = s.2.1 ∧ i.2.1 = s.2.2.1
    ∧ i.2.2.2.2.2.2.2.2.2 = s.2.2.2.2.2
    ∧ s.2.2.2.1 <+: wires i .stF_in
    ∧ s.2.2.2.2.1 <+: (wires i .emptyA_q).map (·.empty)

/-! ### Each block sees prefixes of the bank's own inputs -/

theorem out_st {clk crn d} {w : Het.Wires Ty} (hw : Het.Wf (drv clk crn d) w) :
    w .stF_in <+: StRegR.stOut clk (stOf d) crn :=
  (hw .stF_in).trans (StRegR.stOut_mono (hw .stR_clk) (hw .stR_d) (hw .stR_clrn))

theorem out_empty {clk crn d} {w : Het.Wires Ty} (hw : Het.Wf (drv clk crn d) w) :
    (w .emptyA_q).map (·.empty) <+: (StRegR.stOut clk (stOf d) crn).map (·.empty) :=
  ((hw .emptyA_q).trans (out_st hw)).map _

theorem out_gray {clk crn d} {w : Het.Wires Ty} (hw : Het.Wf (drv clk crn d) w)
    {v : List (BitVec 3)} (h : v <+: BusReg.busOut (w .grR_clk) (w .grR_d) (w .grR_clrn)) :
    v <+: BusReg.busOut clk (gnextOf d) crn :=
  h.trans (BusReg.busOut_mono (hw .grR_clk) (hw .grR_d) (hw .grR_clrn))

/-! ### One tactic for every connection -/

syntax "bankr_case" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| bankr_case) => `(tactic| (
      obtain ⟨stF_in, crF_in, ⟨stR_clk, stR_d, stR_clrn, stR_qh⟩, clkF_in, unpN_d, emptyA_q,
        ⟨grR_clk, grR_d, grR_clrn, grR_qh⟩⟩ := i
      obtain ⟨_, _, ⟨_, _, _, _⟩, _, _, _, ⟨_, _, _, _⟩⟩ := mid
      have Hr := Hrule.1 rfl; clear Hrule
      obtain ⟨⟨_, _, ⟨_, _, _, _⟩, _, _, _, ⟨_, _, _, _⟩⟩, out, Hr⟩ := Hr
      simp only [Prod.mk.injEq, and_assoc] at Hr
      repeat' (obtain ⟨hh, Hr⟩ := Hr; try subst hh)
      obtain ⟨hw, e1, e2, e3, e4, h5, h6⟩ := H
      refine ⟨s, existSR_reflexive, Het.step hw drv_mono ?_ ?_, e1, e2, e3, e4, ?_, ?_⟩
      · intro j
        cases j <;> dsimp only [wires] <;>
          first | exact List.prefix_rfl | exact (‹_ ⊏ _›).isPrefix
      · intro j
        have hj := hw j
        cases j <;> (try dsimp only [wires, drv] at hj) <;> dsimp only [wires, drv] <;>
          first
            | exact hj
            | assumption
            | exact List.prefix_rfl
            | exact e1 ▸ List.prefix_rfl
            | exact e3 ▸ List.prefix_rfl
            | exact e2 ▸ List.prefix_rfl
      · dsimp only [wires] at h5 ⊢
        first | exact h5 | exact h5.trans (‹_ ⊏ _›).isPrefix
      · dsimp only [wires] at h6 ⊢
        first | exact h6 | exact h6.trans ((‹_ ⊏ _›).isPrefix.map _)))

theorem bankNetlist_internals_eq : bankNetlist.internals = [bankNetlist.internals.getD 0 (fun _ _ => False), bankNetlist.internals.getD 1 (fun _ _ => False), bankNetlist.internals.getD 2 (fun _ _ => False), bankNetlist.internals.getD 3 (fun _ _ => False), bankNetlist.internals.getD 4 (fun _ _ => False), bankNetlist.internals.getD 5 (fun _ _ => False), bankNetlist.internals.getD 6 (fun _ _ => False), bankNetlist.internals.getD 7 (fun _ _ => False)] := rfl

/-! All eight connections, one line each. -/

theorem case_0 (s) (i mid : bankT) (H : ψ i s)
    (Hrule : (bankNetlist.internals.getD 0 (fun _ _ => False)) i mid) :
    ∃ s', existSR bankSpec.internals s s' ∧ ψ mid s' := by bankr_case

theorem case_1 (s) (i mid : bankT) (H : ψ i s)
    (Hrule : (bankNetlist.internals.getD 1 (fun _ _ => False)) i mid) :
    ∃ s', existSR bankSpec.internals s s' ∧ ψ mid s' := by bankr_case

theorem case_2 (s) (i mid : bankT) (H : ψ i s)
    (Hrule : (bankNetlist.internals.getD 2 (fun _ _ => False)) i mid) :
    ∃ s', existSR bankSpec.internals s s' ∧ ψ mid s' := by bankr_case

theorem case_3 (s) (i mid : bankT) (H : ψ i s)
    (Hrule : (bankNetlist.internals.getD 3 (fun _ _ => False)) i mid) :
    ∃ s', existSR bankSpec.internals s s' ∧ ψ mid s' := by bankr_case

theorem case_4 (s) (i mid : bankT) (H : ψ i s)
    (Hrule : (bankNetlist.internals.getD 4 (fun _ _ => False)) i mid) :
    ∃ s', existSR bankSpec.internals s s' ∧ ψ mid s' := by bankr_case

theorem case_5 (s) (i mid : bankT) (H : ψ i s)
    (Hrule : (bankNetlist.internals.getD 5 (fun _ _ => False)) i mid) :
    ∃ s', existSR bankSpec.internals s s' ∧ ψ mid s' := by bankr_case

theorem case_6 (s) (i mid : bankT) (H : ψ i s)
    (Hrule : (bankNetlist.internals.getD 6 (fun _ _ => False)) i mid) :
    ∃ s', existSR bankSpec.internals s s' ∧ ψ mid s' := by bankr_case

theorem case_7 (s) (i mid : bankT) (H : ψ i s)
    (Hrule : (bankNetlist.internals.getD 7 (fun _ _ => False)) i mid) :
    ∃ s', existSR bankSpec.internals s s' ∧ ψ mid s' := by bankr_case

/-! ### The specification's own rules -/

section SpecRules
variable (sp : List Bool × List (RNext 2) × List Bool × List (RSt 2) × List Bool ×
  List (BitVec 3))

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
    (bankSpec.outputs.getIO ↑"empty").2 sp v
      (sp.1, sp.2.1, sp.2.2.1, sp.2.2.2.1, v, sp.2.2.2.2.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h1, h2, rfl⟩

theorem spec_out_gray (v : List (BitVec 3)) (h1 : sp.2.2.2.2.2 <+: v)
    (h2 : v <+: BusReg.busOut sp.1 (gnextOf sp.2.1) sp.2.2.1) :
    (bankSpec.outputs.getIO ↑"gray").2 sp v
      (sp.1, sp.2.1, sp.2.2.1, sp.2.2.2.1, sp.2.2.2.2.1, v) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h1, h2, rfl⟩
end SpecRules

/-! ### The refinement -/

set_option maxHeartbeats 1000000 in
theorem refines_ψ : bankNetlist ⊑_{ψ} bankSpec := by
  intro i s H
  constructor
  · intro ident mid_i v Hrule
    obtain ⟨stF_in, crF_in, ⟨stR_clk, stR_d, stR_clrn, stR_qh⟩, clkF_in, unpN_d, emptyA_q,
      ⟨grR_clk, grR_d, grR_clrn, grR_qh⟩⟩ := i
    obtain ⟨_, _, ⟨_, _, _, _⟩, _, _, _, ⟨_, _, _, _⟩⟩ := mid_i
    obtain ⟨hw, e1, e2, e3, e4, h5, h6⟩ := H
    case_transition Hcontains : Module.inputs bankNetlist, ident,
      (PortMap.getIO_not_contained_false' Hrule)
    dsimp only [bankNetlist] at Hcontains
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
          rfl, e2, e3, e4, h5, h6⟩
      | exact ⟨_, _, spec_in_d s _ (by rw [← e2]; exact hpre), existSR_reflexive,
          Het.drv_le hw (drv_env List.prefix_rfl List.prefix_rfl (e2 ▸ hpre.isPrefix) _),
          e1, rfl, e3, e4, h5, h6⟩
      | exact ⟨_, _, spec_in_clrn s _ (by rw [← e3]; exact hpre), existSR_reflexive,
          Het.drv_le hw (drv_env List.prefix_rfl (e3 ▸ hpre.isPrefix) List.prefix_rfl _),
          e1, e2, rfl, e4, h5, h6⟩
  · intro ident mid_i v Hrule
    obtain ⟨stF_in, crF_in, ⟨stR_clk, stR_d, stR_clrn, stR_qh⟩, clkF_in, unpN_d, emptyA_q,
      ⟨grR_clk, grR_d, grR_clrn, grR_qh⟩⟩ := i
    obtain ⟨_, _, ⟨_, _, _, _⟩, _, _, _, ⟨_, _, _, _⟩⟩ := mid_i
    obtain ⟨hw, e1, e2, e3, e4, h5, h6⟩ := H
    have hst := out_st hw
    have hem := out_empty hw
    dsimp only [wires] at hst hem h5 h6
    case_transition Hcontains : Module.outputs bankNetlist, ident,
      (PortMap.getIO_not_contained_false' Hrule)
    dsimp only [bankNetlist] at Hcontains
    simp at Hcontains
    rcases Hcontains with h | h | h <;> subst h <;>
      rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule <;>
      dsimp only at Hrule <;>
      simp only [Prod.mk.injEq, and_assoc] at Hrule <;>
      repeat' (obtain ⟨hh, Hrule⟩ := Hrule; try subst hh)
    all_goals first
      | exact ⟨s, _, existSR_reflexive, spec_out_st s _ h5 hst,
          hw, e1, e2, e3, e4, List.prefix_rfl, h6⟩
      | exact ⟨s, _, existSR_reflexive, spec_out_empty s _ h6 hem,
          hw, e1, e2, e3, e4, h5, List.prefix_rfl⟩
      | exact ⟨s, _, existSR_reflexive, spec_out_gray s _ (e4 ▸ ‹_›) (out_gray hw ‹_›),
          hw, e1, e2, e3, rfl, h5, h6⟩
  · intro rule mid_i Hin Hrule
    rw [bankNetlist_internals_eq] at Hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at Hin
    rcases Hin with h|h|h|h|h|h|h|h
    · subst h; exact case_0 s i mid_i H Hrule
    · subst h; exact case_1 s i mid_i H Hrule
    · subst h; exact case_2 s i mid_i H Hrule
    · subst h; exact case_3 s i mid_i H Hrule
    · subst h; exact case_4 s i mid_i H Hrule
    · subst h; exact case_5 s i mid_i H Hrule
    · subst h; exact case_6 s i mid_i H Hrule
    · subst h; exact case_7 s i mid_i H Hrule

theorem refines_initial : Module.refines_initial bankNetlist bankSpec ψ := by
  intro i hi
  obtain ⟨stF_in, crF_in, ⟨stR_clk, stR_d, stR_clrn, stR_qh⟩, clkF_in, unpN_d, emptyA_q,
    ⟨grR_clk, grR_d, grR_clrn, grR_qh⟩⟩ := i
  dsimp only [bankNetlist] at hi
  simp only [Prod.mk.injEq, and_assoc] at hi
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hi
  refine ⟨([], [], [], [], [], []), rfl, ?_, rfl, rfl, rfl, rfl,
    List.nil_prefix, List.nil_prefix⟩
  intro k; cases k <;> exact List.nil_prefix

/-- **The two registers refine the read domain's register bank.** -/
theorem bank_refines : bankNetlist ⊑ bankSpec :=
  ⟨inferInstance, ψ, refines_ψ, refines_initial⟩

end Graphiti.AsyncFifo.BankR
