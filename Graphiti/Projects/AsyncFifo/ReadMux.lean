/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.NetlistWf
import Graphiti.Projects.AsyncFifo.Gates
import Graphiti.Projects.AsyncFifo.Timed

/-!
# The read port as gates

The read domain's data output is `mem[ptr]`: combinational, and at depth 4 with one-bit data it
is a two-bit address decode and a four-way multiplexer --- eleven gates.

The one thing that has to be said about it is why the memory can be gates at all.  The wire that
carries it from the write domain has type `List (BitVec 2 → Bool)`: at each instant a *function*
from address to value.  That is what makes `Timed.MemOut` sayable --- a write to one entry is
invisible to another --- but gates carry `Bool`.  The bridge is a projection: a function-valued
wire *is* four wires, and `entry a` picks one of them, exactly as `StReg.bitsOf` picks a bit out
of a record.  It computes nothing; it is the same kind of adapter as `unpackSt` or `unpackNext`.

The other thing worth naming is why the contract is `Timed.ReadOut` and not `Comb`.  A
multiplexer depends combinationally on *all four* entries, so a `Comb` argument would demand the
whole memory stand still over the delay window --- which is precisely what a memory is for not
having to do.  The gate-level argument is the one `Mem.W_en_false` already makes for the write
decoder: once the address has settled, the three disabled AND gates are `false` whatever their
data, so only the selected entry reaches the output.  `ReadOut`'s two hypotheses (the address
stable, the *selected* word held) are exactly what that argument consumes.

The window is `[3, 5]`: an entry reaches the output through one AND and two ORs, and the address
through an inverter first.
-/

set_option linter.unusedSectionVars false

namespace Graphiti.AsyncFifo.ReadMux

open Graphiti.AsyncFifo Graphiti.AsyncFifo.Gates Graphiti.AsyncFifo.Timed

/-! ### The two projections

Neither is logic: both are the identity on the wires the stream stands for. -/

/-- Bit `i` of the read address. -/
def addrBit (i : Nat) (st : List (RSt 2)) : List Bool :=
  st.map (fun x => (x.ptr.setWidth 2).getLsbD i)

/-- Entry `a` of the memory, as its own wire. -/
def entry (a : BitVec 2) (mem : List (BitVec 2 → Bool)) : List Bool :=
  mem.map (fun f => f a)

@[simp] theorem addrBit_length (i : Nat) (st : List (RSt 2)) :
    (addrBit i st).length = st.length := by simp [addrBit]

@[simp] theorem entry_length (a : BitVec 2) (mem : List (BitVec 2 → Bool)) :
    (entry a mem).length = mem.length := by simp [entry]

theorem addrBit_mono {i : Nat} {st st' : List (RSt 2)} (h : st <+: st') :
    addrBit i st <+: addrBit i st' := h.map _

theorem entry_mono {a : BitVec 2} {mem mem' : List (BitVec 2 → Bool)} (h : mem <+: mem') :
    entry a mem <+: entry a mem' := h.map _

theorem addrBit_getD {i : Nat} {st : List (RSt 2)} {u : Nat} (h : u < st.length) :
    (addrBit i st).getD u false = ((st.getD u default).ptr.setWidth 2).getLsbD i := by
  simp [addrBit, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]

theorem entry_getD {a : BitVec 2} {mem : List (BitVec 2 → Bool)} {u : Nat} (h : u < mem.length) :
    (entry a mem).getD u false = (mem.getD u (fun _ => default)) a := by
  simp [entry, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]

/-! ### The netlist's wires -/

/-- The complement of an address bit. -/
def na (i : Nat) (st : List (RSt 2)) : List Bool := gate1Out not (addrBit i st)

/-- The four decoded selects. -/
def sel0 (st : List (RSt 2)) : List Bool := gateOut Bool.and (na 0 st) (na 1 st)
def sel1 (st : List (RSt 2)) : List Bool := gateOut Bool.and (addrBit 0 st) (na 1 st)
def sel2 (st : List (RSt 2)) : List Bool := gateOut Bool.and (na 0 st) (addrBit 1 st)
def sel3 (st : List (RSt 2)) : List Bool := gateOut Bool.and (addrBit 0 st) (addrBit 1 st)

/-- The four gated entries. -/
def gd0 (st : List (RSt 2)) (mem : List (BitVec 2 → Bool)) : List Bool :=
  gateOut Bool.and (sel0 st) (entry 0#2 mem)
def gd1 (st : List (RSt 2)) (mem : List (BitVec 2 → Bool)) : List Bool :=
  gateOut Bool.and (sel1 st) (entry 1#2 mem)
def gd2 (st : List (RSt 2)) (mem : List (BitVec 2 → Bool)) : List Bool :=
  gateOut Bool.and (sel2 st) (entry 2#2 mem)
def gd3 (st : List (RSt 2)) (mem : List (BitVec 2 → Bool)) : List Bool :=
  gateOut Bool.and (sel3 st) (entry 3#2 mem)

def or01 (st : List (RSt 2)) (mem : List (BitVec 2 → Bool)) : List Bool :=
  gateOut Bool.or (gd0 st mem) (gd1 st mem)
def or23 (st : List (RSt 2)) (mem : List (BitVec 2 → Bool)) : List Bool :=
  gateOut Bool.or (gd2 st mem) (gd3 st mem)

/-- What the eleven gates compute. -/
def muxWire (st : List (RSt 2)) (mem : List (BitVec 2 → Bool)) : List Bool :=
  gateOut Bool.or (or01 st mem) (or23 st mem)

/-- The boundary cut: the block reports only as far as its own inputs are known.  `ReadOut`'s
length clause has no `+ 1` --- a combinational block is not entitled to the instant a Moore
block is --- so the cut is exact. -/
def cutOut (o r1 r2 : List Bool) : List Bool := o.take (min r1.length r2.length)

/-- What the read port *reports*. -/
def muxOut (st : List (RSt 2)) (mem : List (BitVec 2 → Bool)) : List Bool :=
  cutOut (muxWire st mem) (addrBit 0 st) (entry 0#2 mem)

@[simp] theorem muxOut_length (st : List (RSt 2)) (mem : List (BitVec 2 → Bool)) :
    (muxOut st mem).length = min (min st.length mem.length) (muxWire st mem).length := by
  simp only [muxOut, cutOut, List.length_take, addrBit_length, entry_length]

/-! ### Lengths

Every wire reaches at least `min st.length mem.length + 1`, so every instant the block reports
is one the gates have computed. -/

theorem len_step {a b N : Nat} (ha : N + 1 ≤ a) (hb : N ≤ b) : N + 1 ≤ min a b + 1 := by
  have : N ≤ min a b := Nat.le_min.mpr ⟨by omega, hb⟩
  omega

/-- A gate reaches every instant the block reports, if both its inputs do. -/
theorem gate_reaches {a b : List Bool} (N : Nat) {u : Nat}
    (ha : N ≤ a.length) (hb : N ≤ b.length) (hu : u ≤ N) : u < min a.length b.length + 1 := by
  have : N ≤ min a.length b.length := Nat.le_min.mpr ⟨ha, hb⟩
  omega

section Lengths

variable {st : List (RSt 2)} {mem : List (BitVec 2 → Bool)}

theorem le_na (i : Nat) : min st.length mem.length + 1 ≤ (na i st).length := by
  rw [na, gate1Out_length, addrBit_length]; omega

theorem le_addrBit (i : Nat) : min st.length mem.length ≤ (addrBit i st).length := by
  rw [addrBit_length]; omega

theorem le_entry (a : BitVec 2) : min st.length mem.length ≤ (entry a mem).length := by
  rw [entry_length]; omega

theorem le_sel0 : min st.length mem.length + 1 ≤ (sel0 st).length := by
  rw [sel0, gateOut_length]; exact len_step (le_na 0) (by have := le_na (st := st) (mem := mem) 1; omega)

theorem le_sel1 : min st.length mem.length + 1 ≤ (sel1 st).length := by
  rw [sel1, gateOut_length]
  exact Nat.succ_le_succ (Nat.le_min.mpr ⟨le_addrBit 0, by have := le_na (st := st) (mem := mem) 1; omega⟩)

theorem le_sel2 : min st.length mem.length + 1 ≤ (sel2 st).length := by
  rw [sel2, gateOut_length]
  exact Nat.succ_le_succ (Nat.le_min.mpr ⟨by have := le_na (st := st) (mem := mem) 0; omega, le_addrBit 1⟩)

theorem le_sel3 : min st.length mem.length + 1 ≤ (sel3 st).length := by
  rw [sel3, gateOut_length]
  exact Nat.succ_le_succ (Nat.le_min.mpr ⟨le_addrBit 0, le_addrBit 1⟩)

theorem le_gd0 : min st.length mem.length + 1 ≤ (gd0 st mem).length := by
  rw [gd0, gateOut_length]; exact len_step le_sel0 (le_entry 0#2)
theorem le_gd1 : min st.length mem.length + 1 ≤ (gd1 st mem).length := by
  rw [gd1, gateOut_length]; exact len_step le_sel1 (le_entry 1#2)
theorem le_gd2 : min st.length mem.length + 1 ≤ (gd2 st mem).length := by
  rw [gd2, gateOut_length]; exact len_step le_sel2 (le_entry 2#2)
theorem le_gd3 : min st.length mem.length + 1 ≤ (gd3 st mem).length := by
  rw [gd3, gateOut_length]; exact len_step le_sel3 (le_entry 3#2)

theorem le_or01 : min st.length mem.length + 1 ≤ (or01 st mem).length := by
  rw [or01, gateOut_length]; exact len_step le_gd0 (by have := le_gd1 (st := st) (mem := mem); omega)
theorem le_or23 : min st.length mem.length + 1 ≤ (or23 st mem).length := by
  rw [or23, gateOut_length]; exact len_step le_gd2 (by have := le_gd3 (st := st) (mem := mem); omega)

theorem le_muxWire : min st.length mem.length + 1 ≤ (muxWire st mem).length := by
  rw [muxWire, gateOut_length]; exact len_step le_or01 (by have := le_or23 (st := st) (mem := mem); omega)

end Lengths

/-! ### What the gates compute -/

theorem bv2_cases (a : BitVec 2) : a = 0#2 ∨ a = 1#2 ∨ a = 2#2 ∨ a = 3#2 := by revert a; decide

section Value

variable {st : List (RSt 2)} {mem : List (BitVec 2 → Bool)} {t : Nat}

/-- **The multiplexer selects.**  With the address stable over `[t-5, t-3]`, the output at `t` is
the entry that address names, read at `t - 3` --- and nothing is assumed about the other three
entries, because their AND gates are disabled. -/
theorem muxWire_getD (h5 : 5 ≤ t) (hS : t < st.length) (hM : t < mem.length)
    (hstab : ∀ u, t - 5 ≤ u → u ≤ t - 3 →
      (st.getD u default).ptr.setWidth 2 = (st.getD (t - 3) default).ptr.setWidth 2) :
    (muxWire st mem).getD t false =
      (mem.getD (t - 3) (fun _ => default)) ((st.getD (t - 3) default).ptr.setWidth 2) := by
  have hN : min st.length mem.length + 1 ≤ st.length + 1 := by omega
  have hNt : t < min st.length mem.length := by omega
  -- the address bits, everywhere in the window
  have hab : ∀ i u, t - 5 ≤ u → u ≤ t - 3 → (addrBit i st).getD u false =
      ((st.getD (t - 3) default).ptr.setWidth 2).getLsbD i := by
    intro i u h1 h2
    rw [addrBit_getD (by omega), hstab u h1 h2]
  have hna : ∀ i, (na i st).getD (t - 4) false =
      !((st.getD (t - 3) default).ptr.setWidth 2).getLsbD i := by
    intro i
    rw [na, gate1Out_getD _ _ (t := t - 4) (by omega) (by rw [addrBit_length]; omega)]
    have : t - 4 - 1 = t - 5 := by omega
    rw [this, hab i (t - 5) (by omega) (by omega)]
  set A := (st.getD (t - 3) default).ptr.setWidth 2 with hA
  have e4 : t - 3 - 1 = t - 4 := by omega
  have hs0 : (sel0 st).getD (t - 3) false = (!A.getLsbD 0 && !A.getLsbD 1) := by
    rw [sel0, gateOut_getD _ _ _ (t := t - 3) (by omega)
      (gate_reaches (min st.length mem.length)
        (by have := le_na (st := st) (mem := mem) 0; omega)
        (by have := le_na (st := st) (mem := mem) 1; omega) (by omega))]
    rw [e4, hna 0, hna 1]
  have hs1 : (sel1 st).getD (t - 3) false = (A.getLsbD 0 && !A.getLsbD 1) := by
    rw [sel1, gateOut_getD _ _ _ (t := t - 3) (by omega)
      (gate_reaches (min st.length mem.length) (by rw [addrBit_length]; omega)
        (by have := le_na (st := st) (mem := mem) 1; omega) (by omega))]
    rw [e4, hab 0 (t - 4) (by omega) (by omega), hna 1]
  have hs2 : (sel2 st).getD (t - 3) false = (!A.getLsbD 0 && A.getLsbD 1) := by
    rw [sel2, gateOut_getD _ _ _ (t := t - 3) (by omega)
      (gate_reaches (min st.length mem.length)
        (by have := le_na (st := st) (mem := mem) 0; omega)
        (by rw [addrBit_length]; omega) (by omega))]
    rw [e4, hna 0, hab 1 (t - 4) (by omega) (by omega)]
  have hs3 : (sel3 st).getD (t - 3) false = (A.getLsbD 0 && A.getLsbD 1) := by
    rw [sel3, gateOut_getD _ _ _ (t := t - 3) (by omega)
      (gate_reaches (min st.length mem.length) (by rw [addrBit_length]; omega)
        (by rw [addrBit_length]; omega) (by omega))]
    rw [e4, hab 0 (t - 4) (by omega) (by omega), hab 1 (t - 4) (by omega) (by omega)]
  -- the gated entries
  have hg : ∀ (s : List Bool) (a : BitVec 2) (b : Bool),
      min st.length mem.length + 1 ≤ s.length → s.getD (t - 3) false = b →
      (gateOut Bool.and s (entry a mem)).getD (t - 2) false =
        (b && (mem.getD (t - 3) (fun _ => default)) a) := by
    intro s a b hls hsv
    rw [gateOut_getD _ _ _ (t := t - 2) (by omega)
      (gate_reaches (min st.length mem.length) (by omega) (le_entry a) (by omega))]
    have h21 : t - 2 - 1 = t - 3 := by omega
    rw [h21, hsv, entry_getD (by omega)]
  have hgd0 := hg _ 0#2 _ le_sel0 hs0
  have hgd1 := hg _ 1#2 _ le_sel1 hs1
  have hgd2 := hg _ 2#2 _ le_sel2 hs2
  have hgd3 := hg _ 3#2 _ le_sel3 hs3
  -- the OR tree
  have ho : ∀ (x y : List Bool) (bx byy : Bool),
      min st.length mem.length + 1 ≤ x.length → min st.length mem.length + 1 ≤ y.length →
      x.getD (t - 2) false = bx → y.getD (t - 2) false = byy →
      (gateOut Bool.or x y).getD (t - 1) false = (bx || byy) := by
    intro x y bx byy hx hy hxv hyv
    rw [gateOut_getD _ _ _ (t := t - 1) (by omega)
      (gate_reaches (min st.length mem.length) (by omega) (by omega) (by omega))]
    have h11 : t - 1 - 1 = t - 2 := by omega
    rw [h11, hxv, hyv]
  have ho01 := ho _ _ _ _ le_gd0 le_gd1 hgd0 hgd1
  have ho23 := ho _ _ _ _ le_gd2 le_gd3 hgd2 hgd3
  rw [muxWire, gateOut_getD _ _ _ (t := t) (by omega)
    (gate_reaches (min st.length mem.length)
      (by have := le_or01 (st := st) (mem := mem); omega)
      (by have := le_or23 (st := st) (mem := mem); omega) (by omega))]
  simp only [or01, or23]
  rw [ho01, ho23]
  rcases bv2_cases A with h | h | h | h <;> rw [h] <;> simp

/-- **The read port's contract**: an asynchronous read with delay window `[3, 5]`. -/
theorem muxOut_readOut {v : List Bool} (hv : v <+: muxOut st mem) :
    ReadOut 3 5 (fun u => (st.getD u default).ptr.setWidth 2)
      (fun u => mem.getD u (fun _ => default)) (min st.length mem.length) v := by
  have hvl := hv.length_le
  rw [muxOut_length] at hvl
  refine ⟨by omega, fun t h5 ht hstab _ => ?_⟩
  have hlt : t < min st.length mem.length := by omega
  have hmw := le_muxWire (st := st) (mem := mem)
  have htk : t < ((muxWire st mem).take
      (min (addrBit 0 st).length (entry 0#2 mem).length)).length := by
    simp only [List.length_take, addrBit_length, entry_length]
    omega
  rw [hv.getD_eq_left ht, muxOut, cutOut, (List.take_prefix _ _).getD_eq_left htk]
  exact muxWire_getD h5 (by omega) (by omega) (fun u h1 h2 => hstab.2 u h1 h2)

end Value

/-! ### The netlist -/

/-- The two projections as a block: no logic, only wiring.  `a0c`/`m0c` are the same wires as
`a0`/`m0`, offered a second time for the boundary cut. -/
@[drcomponents]
def unpRD : StringModule (List (RSt 2) × List (BitVec 2 → Bool)) :=
  { inputs := [ (↑"st", ⟨List (RSt 2), fun s v s' => s.1 ⊏ v ∧ s' = (v, s.2)⟩)
              , (↑"mem", ⟨List (BitVec 2 → Bool), fun s v s' => s.2 ⊏ v ∧ s' = (s.1, v)⟩)
              ].toAssocList
    outputs := [ (↑"a0", ⟨List Bool, fun s v s' => s' = s ∧ v = addrBit 0 s.1⟩)
               , (↑"a0c", ⟨List Bool, fun s v s' => s' = s ∧ v = addrBit 0 s.1⟩)
               , (↑"a1", ⟨List Bool, fun s v s' => s' = s ∧ v = addrBit 1 s.1⟩)
               , (↑"m0", ⟨List Bool, fun s v s' => s' = s ∧ v = entry 0#2 s.2⟩)
               , (↑"m0c", ⟨List Bool, fun s v s' => s' = s ∧ v = entry 0#2 s.2⟩)
               , (↑"m1", ⟨List Bool, fun s v s' => s' = s ∧ v = entry 1#2 s.2⟩)
               , (↑"m2", ⟨List Bool, fun s v s' => s' = s ∧ v = entry 2#2 s.2⟩)
               , (↑"m3", ⟨List Bool, fun s v s' => s' = s ∧ v = entry 3#2 s.2⟩)
               ].toAssocList
    internals := []
    init_state := fun s => s = ([], []) }

/-- The boundary cut as a block. -/
@[drcomponents]
def cutRD : StringModule (List Bool × List Bool × List Bool) :=
  { inputs := [ (↑"in", ⟨List Bool, fun s v s' => s.1 ⊏ v ∧ s' = (v, s.2)⟩)
              , (↑"r1", ⟨List Bool, fun s v s' => s.2.1 ⊏ v ∧ s' = (s.1, v, s.2.2)⟩)
              , (↑"r2", ⟨List Bool, fun s v s' => s.2.2 ⊏ v ∧ s' = (s.1, s.2.1, v)⟩)
              ].toAssocList
    outputs := [ (↑"out", ⟨List Bool, fun s v s' => s' = s ∧ v = cutOut s.1 s.2.1 s.2.2⟩)
               ].toAssocList
    internals := []
    init_state := fun s => s = ([], [], []) }

theorem cutOut_mono {o o' r1 r1' r2 r2' : List Bool} (ho : o <+: o') (h1 : r1 <+: r1')
    (h2 : r2 <+: r2') : cutOut o r1 r2 <+: cutOut o' r1' r2' := by
  have l1 := h1.length_le; have l2 := h2.length_le; have lo := ho.length_le
  rw [prefix_iff_length_getD false]
  refine ⟨by simp only [cutOut, List.length_take]; omega, fun t ht => ?_⟩
  simp only [cutOut, List.length_take] at ht
  show (o.take _).getD t false = (o'.take _).getD t false
  rw [(List.take_prefix _ _).getD_eq_left (by simp only [List.length_take]; omega),
    (List.take_prefix _ _).getD_eq_left (by simp only [List.length_take]; omega),
    ho.getD_eq_left (by omega)]

def muxGraph := [graphEnv|
    st [type="io"];
    mem [type="io"];
    q [type="io"];

    unpRD [type="unpRD", typeImp=$(⟨_, unpRD⟩)];
    fa0 [type="fork3", typeImp=$(⟨_, fork3⟩)];
    fa1 [type="fork3", typeImp=$(⟨_, fork3⟩)];
    na0 [type="inv", typeImp=$(⟨_, gate1 not⟩)];
    na1 [type="inv", typeImp=$(⟨_, gate1 not⟩)];
    fn0 [type="fork2", typeImp=$(⟨_, Timed.fork2 Bool⟩)];
    fn1 [type="fork2", typeImp=$(⟨_, Timed.fork2 Bool⟩)];
    s0 [type="and2", typeImp=$(⟨_, gate2 Bool.and⟩)];
    s1 [type="and2", typeImp=$(⟨_, gate2 Bool.and⟩)];
    s2 [type="and2", typeImp=$(⟨_, gate2 Bool.and⟩)];
    s3 [type="and2", typeImp=$(⟨_, gate2 Bool.and⟩)];
    g0 [type="and2", typeImp=$(⟨_, gate2 Bool.and⟩)];
    g1 [type="and2", typeImp=$(⟨_, gate2 Bool.and⟩)];
    g2 [type="and2", typeImp=$(⟨_, gate2 Bool.and⟩)];
    g3 [type="and2", typeImp=$(⟨_, gate2 Bool.and⟩)];
    o01 [type="or2", typeImp=$(⟨_, gate2 Bool.or⟩)];
    o23 [type="or2", typeImp=$(⟨_, gate2 Bool.or⟩)];
    outg [type="or2", typeImp=$(⟨_, gate2 Bool.or⟩)];
    cut [type="cutRD", typeImp=$(⟨_, cutRD⟩)];

    st -> unpRD [to="st"];
    mem -> unpRD [to="mem"];

    unpRD -> fa0 [from="a0", to="in"];
    unpRD -> fa1 [from="a1", to="in"];
    unpRD -> cut [from="a0c", to="r1"];
    unpRD -> cut [from="m0c", to="r2"];
    fa0 -> na0 [from="out1", to="a"];
    fa1 -> na1 [from="out1", to="a"];
    na0 -> fn0 [from="out", to="in"];
    na1 -> fn1 [from="out", to="in"];
    fn0 -> s0 [from="out1", to="a"];
    fn1 -> s0 [from="out1", to="b"];
    fa0 -> s1 [from="out2", to="a"];
    fn1 -> s1 [from="out2", to="b"];
    fn0 -> s2 [from="out2", to="a"];
    fa1 -> s2 [from="out2", to="b"];
    fa0 -> s3 [from="out3", to="a"];
    fa1 -> s3 [from="out3", to="b"];
    s0 -> g0 [from="out", to="a"];
    unpRD -> g0 [from="m0", to="b"];
    s1 -> g1 [from="out", to="a"];
    unpRD -> g1 [from="m1", to="b"];
    s2 -> g2 [from="out", to="a"];
    unpRD -> g2 [from="m2", to="b"];
    s3 -> g3 [from="out", to="a"];
    unpRD -> g3 [from="m3", to="b"];
    g0 -> o01 [from="out", to="a"];
    g1 -> o01 [from="out", to="b"];
    g2 -> o23 [from="out", to="a"];
    g3 -> o23 [from="out", to="b"];
    o01 -> outg [from="out", to="a"];
    o23 -> outg [from="out", to="b"];
    outg -> cut [from="out", to="in"];

    cut -> q [from="out"];
  ]

@[drunfold_defs]
def muxLowered := muxGraph.1.lower_TR |>.get rfl

def rdenv := muxGraph.2

@[drenv] theorem rdenv_unpRD : rdenv.find? "unpRD" = .some ⟨_, unpRD⟩ := rfl
@[drenv] theorem rdenv_cutRD : rdenv.find? "cutRD" = .some ⟨_, cutRD⟩ := rfl
@[drenv] theorem rdenv_fork3 : rdenv.find? "fork3" = .some ⟨_, fork3⟩ := rfl
@[drenv] theorem rdenv_fork2 : rdenv.find? "fork2" = .some ⟨_, Timed.fork2 Bool⟩ := rfl
@[drenv] theorem rdenv_inv : rdenv.find? "inv" = .some ⟨_, gate1 not⟩ := rfl
@[drenv] theorem rdenv_and2 : rdenv.find? "and2" = .some ⟨_, gate2 Bool.and⟩ := rfl
@[drenv] theorem rdenv_or2 : rdenv.find? "or2" = .some ⟨_, gate2 Bool.or⟩ := rfl

seal rdenv in
def_module muxT : Type :=
  [T| muxLowered, rdenv.find? ]
reduction_by
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type,
         ExprLow.build_module, ExprLow.build_module', toString]
  simp only [drenv]
  dsimp

seal rdenv in
def_module muxNetlist : StringModule muxT :=
  [e| muxLowered, rdenv.find? ]

/-! ### The specification -/

/-- The read port as a single block: what the eleven gates compute, cut at the block's own
inputs. -/
@[drcomponents]
def readMuxSpec : StringModule (List (RSt 2) × List (BitVec 2 → Bool) × List Bool) :=
  { inputs := [ (↑"st", ⟨List (RSt 2), fun s v s' => s.1 ⊏ v ∧ s' = (v, s.2)⟩)
              , (↑"mem", ⟨List (BitVec 2 → Bool), fun s v s' => s.2.1 ⊏ v ∧
                  s' = (s.1, v, s.2.2)⟩) ].toAssocList
    outputs := [ (↑"q", ⟨List Bool, fun s v s' => s.2.2 <+: v ∧ v <+: muxOut s.1 s.2.1 ∧
                    s' = (s.1, s.2.1, v)⟩) ].toAssocList
    internals := []
    init_state := fun s => s = ([], [], []) }

instance : MatchInterface muxNetlist readMuxSpec := by
  dsimp [muxNetlist, readMuxSpec]
  solve_match_interface

/-! ### The netlist, as an index type

Each wire holds a prefix of what drives it.  Over an index rather than a record with one
field per wire, the per-rule lemmas collapse into `Netlist.Wf_set` and `Netlist.Wf_drv`, so
what is written here is the circuit and nothing else. -/

open Graphiti.AsyncFifo.Netlist

/-- The 31 driven wires. -/
inductive W
  | o23_a
  | o23_b
  | outg_a
  | outg_b
  | s0_a
  | s0_b
  | s2_a
  | s2_b
  | s3_a
  | s3_b
  | fn1_in
  | na1_a
  | g1_a
  | g1_b
  | fn0_in
  | fa0_in
  | g2_a
  | g2_b
  | na0_a
  | fa1_in
  | o01_a
  | o01_b
  | g3_a
  | g3_b
  | cut_in
  | cut_r1
  | cut_r2
  | g0_a
  | g0_b
  | s1_a
  | s1_b
  deriving DecidableEq

/-- What drives each wire: one line per wire, and the only place the shape of this netlist
is written down. -/
def drv (st : List (RSt 2)) (mem : List (BitVec 2 → Bool)) : Drv W
  | w, .o23_a => gateOut Bool.and (w .g2_a) (w .g2_b)
  | w, .o23_b => gateOut Bool.and (w .g3_a) (w .g3_b)
  | w, .outg_a => gateOut Bool.or (w .o01_a) (w .o01_b)
  | w, .outg_b => gateOut Bool.or (w .o23_a) (w .o23_b)
  | w, .s0_a => (w .fn0_in)
  | w, .s0_b => (w .fn1_in)
  | w, .s2_a => (w .fn0_in)
  | w, .s2_b => (w .fa1_in)
  | w, .s3_a => (w .fa0_in)
  | w, .s3_b => (w .fa1_in)
  | w, .fn1_in => gate1Out not (w .na1_a)
  | w, .na1_a => (w .fa1_in)
  | w, .g1_a => gateOut Bool.and (w .s1_a) (w .s1_b)
  | w, .g1_b => entry 1#2 mem
  | w, .fn0_in => gate1Out not (w .na0_a)
  | w, .fa0_in => addrBit 0 st
  | w, .g2_a => gateOut Bool.and (w .s2_a) (w .s2_b)
  | w, .g2_b => entry 2#2 mem
  | w, .na0_a => (w .fa0_in)
  | w, .fa1_in => addrBit 1 st
  | w, .o01_a => gateOut Bool.and (w .g0_a) (w .g0_b)
  | w, .o01_b => gateOut Bool.and (w .g1_a) (w .g1_b)
  | w, .g3_a => gateOut Bool.and (w .s3_a) (w .s3_b)
  | w, .g3_b => entry 3#2 mem
  | w, .cut_in => gateOut Bool.or (w .outg_a) (w .outg_b)
  | w, .cut_r1 => addrBit 0 st
  | w, .cut_r2 => entry 0#2 mem
  | w, .g0_a => gateOut Bool.and (w .s0_a) (w .s0_b)
  | w, .g0_b => entry 0#2 mem
  | w, .s1_a => (w .fa0_in)
  | w, .s1_b => (w .fn1_in)

theorem drv_mono {st mem} :
    Mono (drv st mem) := by
  intro a b h k
  cases k <;> simp only [drv]
  case o23_a => exact gateOut_mono _ (h .g2_a) (h .g2_b)
  case o23_b => exact gateOut_mono _ (h .g3_a) (h .g3_b)
  case outg_a => exact gateOut_mono _ (h .o01_a) (h .o01_b)
  case outg_b => exact gateOut_mono _ (h .o23_a) (h .o23_b)
  case s0_a => exact h .fn0_in
  case s0_b => exact h .fn1_in
  case s2_a => exact h .fn0_in
  case s2_b => exact h .fa1_in
  case s3_a => exact h .fa0_in
  case s3_b => exact h .fa1_in
  case fn1_in => exact gate1Out_mono _ (h .na1_a)
  case na1_a => exact h .fa1_in
  case g1_a => exact gateOut_mono _ (h .s1_a) (h .s1_b)
  case g1_b => exact entry_mono (List.prefix_rfl)
  case fn0_in => exact gate1Out_mono _ (h .na0_a)
  case fa0_in => exact addrBit_mono (List.prefix_rfl)
  case g2_a => exact gateOut_mono _ (h .s2_a) (h .s2_b)
  case g2_b => exact entry_mono (List.prefix_rfl)
  case na0_a => exact h .fa0_in
  case fa1_in => exact addrBit_mono (List.prefix_rfl)
  case o01_a => exact gateOut_mono _ (h .g0_a) (h .g0_b)
  case o01_b => exact gateOut_mono _ (h .g1_a) (h .g1_b)
  case g3_a => exact gateOut_mono _ (h .s3_a) (h .s3_b)
  case g3_b => exact entry_mono (List.prefix_rfl)
  case cut_in => exact gateOut_mono _ (h .outg_a) (h .outg_b)
  case cut_r1 => exact addrBit_mono (List.prefix_rfl)
  case cut_r2 => exact entry_mono (List.prefix_rfl)
  case g0_a => exact gateOut_mono _ (h .s0_a) (h .s0_b)
  case g0_b => exact entry_mono (List.prefix_rfl)
  case s1_a => exact h .fa0_in
  case s1_b => exact h .fn1_in

/-- Growing the block's own inputs grows every driver. -/
theorem drv_env {st st' : List (RSt 2)} {mem mem' : List (BitVec 2 → Bool)}
    (hst : st <+: st') (hmem : mem <+: mem') (w : Wires W) (k : W) :
    drv st mem w k <+:
      drv st' mem' w k := by
  cases k <;> simp only [drv]
  case o23_a => exact gateOut_mono _ (List.prefix_rfl) (List.prefix_rfl)
  case o23_b => exact gateOut_mono _ (List.prefix_rfl) (List.prefix_rfl)
  case outg_a => exact gateOut_mono _ (List.prefix_rfl) (List.prefix_rfl)
  case outg_b => exact gateOut_mono _ (List.prefix_rfl) (List.prefix_rfl)
  case s0_a => exact List.prefix_rfl
  case s0_b => exact List.prefix_rfl
  case s2_a => exact List.prefix_rfl
  case s2_b => exact List.prefix_rfl
  case s3_a => exact List.prefix_rfl
  case s3_b => exact List.prefix_rfl
  case fn1_in => exact gate1Out_mono _ (List.prefix_rfl)
  case na1_a => exact List.prefix_rfl
  case g1_a => exact gateOut_mono _ (List.prefix_rfl) (List.prefix_rfl)
  case g1_b => exact entry_mono (hmem)
  case fn0_in => exact gate1Out_mono _ (List.prefix_rfl)
  case fa0_in => exact addrBit_mono (hst)
  case g2_a => exact gateOut_mono _ (List.prefix_rfl) (List.prefix_rfl)
  case g2_b => exact entry_mono (hmem)
  case na0_a => exact List.prefix_rfl
  case fa1_in => exact addrBit_mono (hst)
  case o01_a => exact gateOut_mono _ (List.prefix_rfl) (List.prefix_rfl)
  case o01_b => exact gateOut_mono _ (List.prefix_rfl) (List.prefix_rfl)
  case g3_a => exact gateOut_mono _ (List.prefix_rfl) (List.prefix_rfl)
  case g3_b => exact entry_mono (hmem)
  case cut_in => exact gateOut_mono _ (List.prefix_rfl) (List.prefix_rfl)
  case cut_r1 => exact addrBit_mono (hst)
  case cut_r2 => exact entry_mono (hmem)
  case g0_a => exact gateOut_mono _ (List.prefix_rfl) (List.prefix_rfl)
  case g0_b => exact entry_mono (hmem)
  case s1_a => exact List.prefix_rfl
  case s1_b => exact List.prefix_rfl

/-- The reduced state is a nested product; `wires` reads it as an assignment. -/
def wires (i : muxT) : Wires W
  | .o23_a => i.1.1
  | .o23_b => i.1.2
  | .outg_a => i.2.1.1
  | .outg_b => i.2.1.2
  | .s0_a => i.2.2.1.1
  | .s0_b => i.2.2.1.2
  | .s2_a => i.2.2.2.1.1
  | .s2_b => i.2.2.2.1.2
  | .s3_a => i.2.2.2.2.1.1
  | .s3_b => i.2.2.2.2.1.2
  | .fn1_in => i.2.2.2.2.2.1
  | .na1_a => i.2.2.2.2.2.2.1
  | .g1_a => i.2.2.2.2.2.2.2.2.1.1
  | .g1_b => i.2.2.2.2.2.2.2.2.1.2
  | .fn0_in => i.2.2.2.2.2.2.2.2.2.1
  | .fa0_in => i.2.2.2.2.2.2.2.2.2.2.1
  | .g2_a => i.2.2.2.2.2.2.2.2.2.2.2.1.1
  | .g2_b => i.2.2.2.2.2.2.2.2.2.2.2.1.2
  | .na0_a => i.2.2.2.2.2.2.2.2.2.2.2.2.1
  | .fa1_in => i.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | .o01_a => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
  | .o01_b => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2
  | .g3_a => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
  | .g3_b => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2
  | .cut_in => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
  | .cut_r1 => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.1
  | .cut_r2 => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2
  | .g0_a => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
  | .g0_b => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2
  | .s1_a => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | .s1_b => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

def ψ (i : muxT) (s : List (RSt 2) × List (BitVec 2 → Bool) × List Bool) : Prop :=
  Wf (drv s.1 s.2.1) (wires i)
    ∧ i.2.2.2.2.2.2.2.1.1 = s.1
    ∧ i.2.2.2.2.2.2.2.1.2 = s.2.1
    ∧ s.2.2 <+: cutOut (wires i .cut_in) (wires i .cut_r1) (wires i .cut_r2)

/-! ### The invariant, clause by clause

`hw .k` already says this, but with `drv` unapplied; spelling each driver out lets the
proofs below rewrite with it exactly as they did against the old record. -/

section Clauses
variable {st : List (RSt 2)} {mem : List (BitVec 2 → Bool)} {w : Wires W} (hInv : Wf (drv st mem) w)
include hInv

theorem wf_o23_a : w .o23_a <+: gateOut Bool.and (w .g2_a) (w .g2_b) := hInv .o23_a
theorem wf_o23_b : w .o23_b <+: gateOut Bool.and (w .g3_a) (w .g3_b) := hInv .o23_b
theorem wf_outg_a : w .outg_a <+: gateOut Bool.or (w .o01_a) (w .o01_b) := hInv .outg_a
theorem wf_outg_b : w .outg_b <+: gateOut Bool.or (w .o23_a) (w .o23_b) := hInv .outg_b
theorem wf_s0_a : w .s0_a <+: (w .fn0_in) := hInv .s0_a
theorem wf_s0_b : w .s0_b <+: (w .fn1_in) := hInv .s0_b
theorem wf_s2_a : w .s2_a <+: (w .fn0_in) := hInv .s2_a
theorem wf_s2_b : w .s2_b <+: (w .fa1_in) := hInv .s2_b
theorem wf_s3_a : w .s3_a <+: (w .fa0_in) := hInv .s3_a
theorem wf_s3_b : w .s3_b <+: (w .fa1_in) := hInv .s3_b
theorem wf_fn1_in : w .fn1_in <+: gate1Out not (w .na1_a) := hInv .fn1_in
theorem wf_na1_a : w .na1_a <+: (w .fa1_in) := hInv .na1_a
theorem wf_g1_a : w .g1_a <+: gateOut Bool.and (w .s1_a) (w .s1_b) := hInv .g1_a
theorem wf_g1_b : w .g1_b <+: entry 1#2 mem := hInv .g1_b
theorem wf_fn0_in : w .fn0_in <+: gate1Out not (w .na0_a) := hInv .fn0_in
theorem wf_fa0_in : w .fa0_in <+: addrBit 0 st := hInv .fa0_in
theorem wf_g2_a : w .g2_a <+: gateOut Bool.and (w .s2_a) (w .s2_b) := hInv .g2_a
theorem wf_g2_b : w .g2_b <+: entry 2#2 mem := hInv .g2_b
theorem wf_na0_a : w .na0_a <+: (w .fa0_in) := hInv .na0_a
theorem wf_fa1_in : w .fa1_in <+: addrBit 1 st := hInv .fa1_in
theorem wf_o01_a : w .o01_a <+: gateOut Bool.and (w .g0_a) (w .g0_b) := hInv .o01_a
theorem wf_o01_b : w .o01_b <+: gateOut Bool.and (w .g1_a) (w .g1_b) := hInv .o01_b
theorem wf_g3_a : w .g3_a <+: gateOut Bool.and (w .s3_a) (w .s3_b) := hInv .g3_a
theorem wf_g3_b : w .g3_b <+: entry 3#2 mem := hInv .g3_b
theorem wf_cut_in : w .cut_in <+: gateOut Bool.or (w .outg_a) (w .outg_b) := hInv .cut_in
theorem wf_cut_r1 : w .cut_r1 <+: addrBit 0 st := hInv .cut_r1
theorem wf_cut_r2 : w .cut_r2 <+: entry 0#2 mem := hInv .cut_r2
theorem wf_g0_a : w .g0_a <+: gateOut Bool.and (w .s0_a) (w .s0_b) := hInv .g0_a
theorem wf_g0_b : w .g0_b <+: entry 0#2 mem := hInv .g0_b
theorem wf_s1_a : w .s1_a <+: (w .fa0_in) := hInv .s1_a
theorem wf_s1_b : w .s1_b <+: (w .fn1_in) := hInv .s1_b

end Clauses

/-! ### What the netlist computes

This is the block's actual content; only the per-rule bookkeeping around it collapsed. -/

theorem out_q {st : List (RSt 2)} {mem : List (BitVec 2 → Bool)} {w : Wires W} (hInv : Wf (drv st mem) w) : cutOut (w .cut_in) (w .cut_r1) (w .cut_r2) <+: muxOut st mem := by
  have ha0 : (w .fa0_in) <+: addrBit 0 st :=
    (wf_fa0_in hInv).trans (addrBit_mono (List.prefix_rfl))
  have ha1 : (w .fa1_in) <+: addrBit 1 st :=
    (wf_fa1_in hInv).trans (addrBit_mono (List.prefix_rfl))
  have hn0 : (w .fn0_in) <+: na 0 st :=
    (wf_fn0_in hInv).trans (gate1Out_mono _ ((wf_na0_a hInv).trans ha0))
  have hn1 : (w .fn1_in) <+: na 1 st :=
    (wf_fn1_in hInv).trans (gate1Out_mono _ ((wf_na1_a hInv).trans ha1))
  have hs0 : gateOut Bool.and (w .s0_a) (w .s0_b) <+: sel0 st :=
    gateOut_mono _ ((wf_s0_a hInv).trans hn0) ((wf_s0_b hInv).trans hn1)
  have hs1 : gateOut Bool.and (w .s1_a) (w .s1_b) <+: sel1 st :=
    gateOut_mono _ ((wf_s1_a hInv).trans ha0) ((wf_s1_b hInv).trans hn1)
  have hs2 : gateOut Bool.and (w .s2_a) (w .s2_b) <+: sel2 st :=
    gateOut_mono _ ((wf_s2_a hInv).trans hn0) ((wf_s2_b hInv).trans ha1)
  have hs3 : gateOut Bool.and (w .s3_a) (w .s3_b) <+: sel3 st :=
    gateOut_mono _ ((wf_s3_a hInv).trans ha0) ((wf_s3_b hInv).trans ha1)
  have hm0 : (w .g0_b) <+: entry 0#2 mem :=
    (wf_g0_b hInv).trans (entry_mono (List.prefix_rfl))
  have hg0 : gateOut Bool.and (w .g0_a) (w .g0_b) <+: gd0 st mem :=
    gateOut_mono _ ((wf_g0_a hInv).trans hs0) hm0
  have hm1 : (w .g1_b) <+: entry 1#2 mem :=
    (wf_g1_b hInv).trans (entry_mono (List.prefix_rfl))
  have hg1 : gateOut Bool.and (w .g1_a) (w .g1_b) <+: gd1 st mem :=
    gateOut_mono _ ((wf_g1_a hInv).trans hs1) hm1
  have hm2 : (w .g2_b) <+: entry 2#2 mem :=
    (wf_g2_b hInv).trans (entry_mono (List.prefix_rfl))
  have hg2 : gateOut Bool.and (w .g2_a) (w .g2_b) <+: gd2 st mem :=
    gateOut_mono _ ((wf_g2_a hInv).trans hs2) hm2
  have hm3 : (w .g3_b) <+: entry 3#2 mem :=
    (wf_g3_b hInv).trans (entry_mono (List.prefix_rfl))
  have hg3 : gateOut Bool.and (w .g3_a) (w .g3_b) <+: gd3 st mem :=
    gateOut_mono _ ((wf_g3_a hInv).trans hs3) hm3
  have ho01 : gateOut Bool.or (w .o01_a) (w .o01_b) <+: or01 st mem :=
    gateOut_mono _ ((wf_o01_a hInv).trans hg0) ((wf_o01_b hInv).trans hg1)
  have ho23 : gateOut Bool.or (w .o23_a) (w .o23_b) <+: or23 st mem :=
    gateOut_mono _ ((wf_o23_a hInv).trans hg2) ((wf_o23_b hInv).trans hg3)
  have hw : gateOut Bool.or (w .outg_a) (w .outg_b) <+: muxWire st mem :=
    gateOut_mono _ ((wf_outg_a hInv).trans ho01) ((wf_outg_b hInv).trans ho23)
  exact cutOut_mono ((wf_cut_in hInv).trans hw)
    ((wf_cut_r1 hInv).trans (addrBit_mono (List.prefix_rfl)))
    ((wf_cut_r2 hInv).trans (entry_mono (List.prefix_rfl)))

/-! ### One tactic for every connection -/

syntax "mux_case " term : tactic
set_option hygiene false in
macro_rules
  | `(tactic| mux_case $w:term) => `(tactic| (
      obtain ⟨⟨o23_a, o23_b⟩, ⟨outg_a, outg_b⟩, ⟨s0_a, s0_b⟩, ⟨s2_a, s2_b⟩, ⟨s3_a, s3_b⟩, fn1_in, na1_a, ⟨unpRD_st, unpRD_mem⟩, ⟨g1_a, g1_b⟩, fn0_in, fa0_in, ⟨g2_a, g2_b⟩, na0_a, fa1_in, ⟨o01_a, o01_b⟩, ⟨g3_a, g3_b⟩, ⟨cut_in, cut_r1, cut_r2⟩, ⟨g0_a, g0_b⟩, ⟨s1_a, s1_b⟩⟩ := i
      obtain ⟨⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, _, _, ⟨_, _⟩, ⟨_, _⟩, _, _, ⟨_, _⟩, _, _, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _, _⟩, ⟨_, _⟩, ⟨_, _⟩⟩ := mid
      have Hr := Hrule.1 rfl; clear Hrule
      obtain ⟨⟨⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, _, _, ⟨_, _⟩, ⟨_, _⟩, _, _, ⟨_, _⟩, _, _, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _, _⟩, ⟨_, _⟩, ⟨_, _⟩⟩, out, Hr⟩ := Hr
      simp only [Prod.mk.injEq, and_assoc] at Hr
      repeat' (obtain ⟨hh, Hr⟩ := Hr; try subst hh)
      obtain ⟨hw, e0, e1, hq⟩ := H
      refine ⟨s, existSR_reflexive, ?_, e0, e1, ?_⟩
      · have key := Wf_set drv_mono hw $w _ (‹_ ⊏ _›).isPrefix (by
          simp only [drv, wires]
          first
            | exact List.prefix_rfl
            | exact List.prefix_rfl
            | exact e0 ▸ List.prefix_rfl
            | exact e1 ▸ List.prefix_rfl
            | exact (‹_ ⊏ _›).isPrefix
            | exact (‹_ ⊏ _›).isPrefix
            | assumption)
        intro j; have hj := key j
        cases j <;> simpa [wires, upd, drv] using hj
      · have key := hq.trans (cutOut_mono (upd_ge (k := $w) (‹_ ⊏ _›).isPrefix _) (upd_ge (k := $w) (‹_ ⊏ _›).isPrefix _) (upd_ge (k := $w) (‹_ ⊏ _›).isPrefix _))
        revert key; simp [wires, upd]))

theorem muxNetlist_internals_eq : muxNetlist.internals =
    [muxNetlist.internals.getD 0 (fun _ _ => False), muxNetlist.internals.getD 1 (fun _ _ => False), muxNetlist.internals.getD 2 (fun _ _ => False),
     muxNetlist.internals.getD 3 (fun _ _ => False), muxNetlist.internals.getD 4 (fun _ _ => False), muxNetlist.internals.getD 5 (fun _ _ => False),
     muxNetlist.internals.getD 6 (fun _ _ => False), muxNetlist.internals.getD 7 (fun _ _ => False), muxNetlist.internals.getD 8 (fun _ _ => False),
     muxNetlist.internals.getD 9 (fun _ _ => False), muxNetlist.internals.getD 10 (fun _ _ => False), muxNetlist.internals.getD 11 (fun _ _ => False),
     muxNetlist.internals.getD 12 (fun _ _ => False), muxNetlist.internals.getD 13 (fun _ _ => False), muxNetlist.internals.getD 14 (fun _ _ => False),
     muxNetlist.internals.getD 15 (fun _ _ => False), muxNetlist.internals.getD 16 (fun _ _ => False), muxNetlist.internals.getD 17 (fun _ _ => False),
     muxNetlist.internals.getD 18 (fun _ _ => False), muxNetlist.internals.getD 19 (fun _ _ => False), muxNetlist.internals.getD 20 (fun _ _ => False),
     muxNetlist.internals.getD 21 (fun _ _ => False), muxNetlist.internals.getD 22 (fun _ _ => False), muxNetlist.internals.getD 23 (fun _ _ => False),
     muxNetlist.internals.getD 24 (fun _ _ => False), muxNetlist.internals.getD 25 (fun _ _ => False), muxNetlist.internals.getD 26 (fun _ _ => False),
     muxNetlist.internals.getD 27 (fun _ _ => False), muxNetlist.internals.getD 28 (fun _ _ => False), muxNetlist.internals.getD 29 (fun _ _ => False),
     muxNetlist.internals.getD 30 (fun _ _ => False)] := rfl

/-! All 31 connections, one line each. -/

theorem case_0 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 0 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.fa0_in

theorem case_1 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 1 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.fa1_in

theorem case_2 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 2 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.cut_r1

theorem case_3 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 3 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.cut_r2

theorem case_4 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 4 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.na0_a

theorem case_5 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 5 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.na1_a

theorem case_6 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 6 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.fn0_in

theorem case_7 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 7 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.fn1_in

theorem case_8 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 8 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.s0_a

theorem case_9 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 9 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.s0_b

theorem case_10 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 10 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.s1_a

theorem case_11 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 11 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.s1_b

theorem case_12 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 12 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.s2_a

theorem case_13 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 13 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.s2_b

theorem case_14 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 14 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.s3_a

theorem case_15 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 15 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.s3_b

theorem case_16 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 16 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.g0_a

theorem case_17 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 17 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.g0_b

theorem case_18 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 18 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.g1_a

theorem case_19 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 19 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.g1_b

theorem case_20 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 20 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.g2_a

theorem case_21 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 21 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.g2_b

theorem case_22 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 22 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.g3_a

theorem case_23 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 23 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.g3_b

theorem case_24 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 24 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.o01_a

theorem case_25 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 25 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.o01_b

theorem case_26 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 26 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.o23_a

theorem case_27 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 27 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.o23_b

theorem case_28 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 28 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.outg_a

theorem case_29 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 29 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.outg_b

theorem case_30 (s) (i mid : muxT) (H : ψ i s)
    (Hrule : (muxNetlist.internals.getD 30 (fun _ _ => False)) i mid) :
    ∃ s', existSR readMuxSpec.internals s s' ∧ ψ mid s' := by mux_case W.cut_in

section SpecRules
variable (sp : List (RSt 2) × List (BitVec 2 → Bool) × List Bool)

theorem spec_in_st (v : List (RSt 2)) (h : sp.1 ⊏ v) :
    (readMuxSpec.inputs.getIO ↑"st").2 sp v (v, sp.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem spec_in_mem (v : List (BitVec 2 → Bool)) (h : sp.2.1 ⊏ v) :
    (readMuxSpec.inputs.getIO ↑"mem").2 sp v (sp.1, v, sp.2.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem spec_out_q (v : List Bool) (h1 : sp.2.2 <+: v) (h2 : v <+: muxOut sp.1 sp.2.1) :
    (readMuxSpec.outputs.getIO ↑"q").2 sp v (sp.1, sp.2.1, v) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h1, h2, rfl⟩
end SpecRules

/-! ### The refinement -/

set_option maxHeartbeats 4000000 in
theorem refines_ψ : muxNetlist ⊑_{ψ} readMuxSpec := by
  intro i s H
  constructor
  · intro ident mid_i v Hrule
    obtain ⟨⟨o23_a, o23_b⟩, ⟨outg_a, outg_b⟩, ⟨s0_a, s0_b⟩, ⟨s2_a, s2_b⟩, ⟨s3_a, s3_b⟩, fn1_in, na1_a, ⟨unpRD_st, unpRD_mem⟩, ⟨g1_a, g1_b⟩, fn0_in, fa0_in, ⟨g2_a, g2_b⟩, na0_a, fa1_in, ⟨o01_a, o01_b⟩, ⟨g3_a, g3_b⟩, ⟨cut_in, cut_r1, cut_r2⟩, ⟨g0_a, g0_b⟩, ⟨s1_a, s1_b⟩⟩ := i
    obtain ⟨⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, _, _, ⟨_, _⟩, ⟨_, _⟩, _, _, ⟨_, _⟩, _, _, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _, _⟩, ⟨_, _⟩, ⟨_, _⟩⟩ := mid_i
    obtain ⟨hw, e0, e1, hq⟩ := H
    case_transition Hcontains : Module.inputs muxNetlist, ident,
      (PortMap.getIO_not_contained_false' Hrule)
    dsimp only [muxNetlist] at Hcontains
    simp at Hcontains
    rcases Hcontains with h | h <;> subst h <;>
      rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule <;>
      dsimp only at Hrule <;>
      simp only [Prod.mk.injEq, and_assoc] at Hrule <;>
      obtain ⟨hpre, Hrule⟩ := Hrule <;>
      repeat' (obtain ⟨hh, Hrule⟩ := Hrule; try subst hh)
    all_goals simp only [eq_mp_eq_cast] at hpre
    -- The port's identity is decided by `hpre`'s type; the proofs are one shape.
    all_goals first
      | exact ⟨_, _, spec_in_st s _ (by rw [← e0]; exact hpre), existSR_reflexive,
          Wf_drv hw (drv_env (e0 ▸ hpre.isPrefix) List.prefix_rfl _), rfl, e1, hq⟩
      | exact ⟨_, _, spec_in_mem s _ (by rw [← e1]; exact hpre), existSR_reflexive,
          Wf_drv hw (drv_env List.prefix_rfl (e1 ▸ hpre.isPrefix) _), e0, rfl, hq⟩
  · intro ident mid_i v Hrule
    obtain ⟨⟨o23_a, o23_b⟩, ⟨outg_a, outg_b⟩, ⟨s0_a, s0_b⟩, ⟨s2_a, s2_b⟩, ⟨s3_a, s3_b⟩, fn1_in, na1_a, ⟨unpRD_st, unpRD_mem⟩, ⟨g1_a, g1_b⟩, fn0_in, fa0_in, ⟨g2_a, g2_b⟩, na0_a, fa1_in, ⟨o01_a, o01_b⟩, ⟨g3_a, g3_b⟩, ⟨cut_in, cut_r1, cut_r2⟩, ⟨g0_a, g0_b⟩, ⟨s1_a, s1_b⟩⟩ := i
    obtain ⟨⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, _, _, ⟨_, _⟩, ⟨_, _⟩, _, _, ⟨_, _⟩, _, _, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _, _⟩, ⟨_, _⟩, ⟨_, _⟩⟩ := mid_i
    obtain ⟨hw, e0, e1, hq⟩ := H
    case_transition Hcontains : Module.outputs muxNetlist, ident,
      (PortMap.getIO_not_contained_false' Hrule)
    dsimp only [muxNetlist] at Hcontains
    simp at Hcontains
    subst Hcontains
    rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule
    dsimp only at Hrule
    simp only [Prod.mk.injEq, and_assoc] at Hrule
    repeat' (obtain ⟨hh, Hrule⟩ := Hrule; try subst hh)
    simp only [eq_mp_eq_cast, cast_self]
    dsimp only [wires] at hq
    have ho := out_q hw
    dsimp only [wires] at ho
    exact ⟨s, _, existSR_reflexive, spec_out_q s _ hq ho, hw, e0, e1, List.prefix_rfl⟩
  · intro rule mid_i Hin Hrule
    rw [muxNetlist_internals_eq] at Hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at Hin
    rcases Hin with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
    · subst h; exact case_0 s i mid_i H Hrule
    · subst h; exact case_1 s i mid_i H Hrule
    · subst h; exact case_2 s i mid_i H Hrule
    · subst h; exact case_3 s i mid_i H Hrule
    · subst h; exact case_4 s i mid_i H Hrule
    · subst h; exact case_5 s i mid_i H Hrule
    · subst h; exact case_6 s i mid_i H Hrule
    · subst h; exact case_7 s i mid_i H Hrule
    · subst h; exact case_8 s i mid_i H Hrule
    · subst h; exact case_9 s i mid_i H Hrule
    · subst h; exact case_10 s i mid_i H Hrule
    · subst h; exact case_11 s i mid_i H Hrule
    · subst h; exact case_12 s i mid_i H Hrule
    · subst h; exact case_13 s i mid_i H Hrule
    · subst h; exact case_14 s i mid_i H Hrule
    · subst h; exact case_15 s i mid_i H Hrule
    · subst h; exact case_16 s i mid_i H Hrule
    · subst h; exact case_17 s i mid_i H Hrule
    · subst h; exact case_18 s i mid_i H Hrule
    · subst h; exact case_19 s i mid_i H Hrule
    · subst h; exact case_20 s i mid_i H Hrule
    · subst h; exact case_21 s i mid_i H Hrule
    · subst h; exact case_22 s i mid_i H Hrule
    · subst h; exact case_23 s i mid_i H Hrule
    · subst h; exact case_24 s i mid_i H Hrule
    · subst h; exact case_25 s i mid_i H Hrule
    · subst h; exact case_26 s i mid_i H Hrule
    · subst h; exact case_27 s i mid_i H Hrule
    · subst h; exact case_28 s i mid_i H Hrule
    · subst h; exact case_29 s i mid_i H Hrule
    · subst h; exact case_30 s i mid_i H Hrule

theorem refines_initial : Module.refines_initial muxNetlist readMuxSpec ψ := by
  intro i hi
  obtain ⟨⟨o23_a, o23_b⟩, ⟨outg_a, outg_b⟩, ⟨s0_a, s0_b⟩, ⟨s2_a, s2_b⟩, ⟨s3_a, s3_b⟩, fn1_in, na1_a, ⟨unpRD_st, unpRD_mem⟩, ⟨g1_a, g1_b⟩, fn0_in, fa0_in, ⟨g2_a, g2_b⟩, na0_a, fa1_in, ⟨o01_a, o01_b⟩, ⟨g3_a, g3_b⟩, ⟨cut_in, cut_r1, cut_r2⟩, ⟨g0_a, g0_b⟩, ⟨s1_a, s1_b⟩⟩ := i
  dsimp only [muxNetlist] at hi
  simp only [Prod.mk.injEq, and_assoc] at hi
  repeat' (obtain ⟨rfl, hi⟩ := hi)
  refine ⟨([], [], []), rfl, ?_, rfl, rfl, List.nil_prefix⟩
  intro k; cases k <;> exact List.nil_prefix

theorem mux_refines : muxNetlist ⊑ readMuxSpec :=
  ⟨inferInstance, ψ, refines_ψ, refines_initial⟩

end Graphiti.AsyncFifo.ReadMux
