/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.ProofWriteOnly.NetlistWf
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.Gates
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.SyncOutMono
import Graphiti.Projects.AsyncFifo.components.level4.ReadPort

/-! # `ReadPort`: the lemmas

Facts about the definitions in `components/level4/ReadPort.lean`.  The statement of the
main theorem names none of them. -/

namespace Graphiti.AsyncFifo.ReadPort
open Graphiti.AsyncFifo Graphiti.AsyncFifo.Gates Graphiti.AsyncFifo.Contracts Graphiti.AsyncFifo.Timed

section NetlistAsModule

/-! ### The circuit reduced to a single module, for the proofs -/

@[drenv] theorem rdenv_unpRD : rdenv.find? "unpRD" = .some ⟨_, unpRD⟩ := rfl
@[drenv] theorem rdenv_cutRD : rdenv.find? "cutRD" = .some ⟨_, cutRD⟩ := rfl
@[drenv] theorem rdenv_fork3 : rdenv.find? "fork3" = .some ⟨_, fork3⟩ := rfl
@[drenv] theorem rdenv_fork2 : rdenv.find? "fork2" = .some ⟨_, fork2 Bool⟩ := rfl
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

seal rdenv in
/-- The `def_module` above is the `[e| … ]` circuit `components/` names, reduced. -/
theorem muxNetlist_sigma :
    (⟨_, muxNetlist⟩ : Σ T, StringModule T) = ExprLow.build_module rdenv.find? muxLowered := by
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
end Graphiti.AsyncFifo.ReadPort