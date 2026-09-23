/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.ProofWriteOnly.Modules
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.Invariant

/-!
# The composed circuit refines the FIFO specification

`refinesF` : the circuit built from the *filtered* domains (`asyncFifoF`) refines `fifoSpec`
whenever each clock period is longer than the synchroniser settling time and than a clk-to-q
window followed by a sampling window.  This is `asyncFifoImpl_refines`,
the top layer's theorem: the domains' own implementations (`wdomImpl`, `rdomImpl`) are proved
against their specifications separately, and every lower stage plugs in by substitution.

The simulation relation `Phi` says that the specification's streams are the circuit's, that
every stream a domain has emitted satisfies its relaxed relation with respect to the inputs
the domain currently holds (the relations are monotone, so this survives input growth), and
that each cross-domain wire is a prefix of the stream its driver emitted.  The relaxed
relations are prefix-closed, so this gives `ConsistentF`, and `fifo_correctF` gives `FifoOK`
for whatever the circuit outputs.  The specification never needs to buffer or speculate:
`FifoOK` is prefix-closed and length-agnostic.
-/

set_option linter.unusedSectionVars false

namespace Graphiti.AsyncFifo

variable {α : Type} [Inhabited α] {n lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r : Nat}

instance : MatchInterface (asyncFifoF α n lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r) (fifoSpec α P_w P_r S_w S_r R_w R_r pw_w pw_r) := by
  dsimp [asyncFifoF, fifoSpec]
  solve_match_interface

/-- The wires seen by the invariant, read off the two domain states. -/
def wires (rd : RStateF α n) (wd : WStateF α n) : Wires α n :=
  ⟨wd.clk, wd.inc, wd.data, wd.rgray, wd.orc, rd.clk, rd.inc, rd.wgray, rd.orc, rd.mem⟩

/-- The simulation relation. -/
structure Phi (lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r : Nat) (rd : RStateF α n) (wd : WStateF α n) (s : FifoIO α) : Prop where
  wclk : wd.clk = s.wclk
  winc : wd.inc = s.winc
  wdata : wd.data = s.wdata
  rclk : rd.clk = s.rclk
  rinc : rd.inc = s.rinc
  full : s.full = wd.full_q
  empty : s.empty = rd.empty_q
  rdata : s.rdata = rd.rdata_q
  gF : WGrayF lat stl su kq P_w S_w R_w pw_w wd.clk wd.inc wd.data wd.rgray wd.orc wd.gray_q
  fF : WFullF lat stl su kq P_w S_w R_w pw_w wd.clk wd.inc wd.data wd.rgray wd.orc wd.full_q
  mF : WMemF lat stl su kq P_w S_w R_w pw_w wd.clk wd.inc wd.data wd.rgray wd.orc wd.mem_q
  rgF : RGrayF lat stl su kq P_r S_r R_r pw_r rd.clk rd.inc rd.wgray rd.orc rd.gray_q
  reF : REmptyF lat stl su kq P_r S_r R_r pw_r rd.clk rd.inc rd.wgray rd.orc rd.empty_q
  rdF : RDataF lat stl su kq rdly P_r S_r R_r pw_r rd.clk rd.inc rd.wgray rd.orc rd.mem rd.rdata_q
  wire_wg : rd.wgray <+: wd.gray_q
  wire_mem : rd.mem <+: wd.mem_q
  wire_rg : wd.rgray <+: rd.gray_q

def φ (lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r : Nat) (i : asyncFifoFT α n) (s : FifoIO α) : Prop :=
  Phi lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r i.2.1 i.2.2.1 s

namespace Phi

variable {rd : RStateF α n} {wd : WStateF α n} {s : FifoIO α}

theorem cons (h : Phi lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r rd wd s) :
    ConsistentF lat stl su P_w P_r S_w S_r R_w R_r pw_w pw_r kq (wires rd wd) :=
  ⟨WGrayF.of_prefix h.wire_wg h.gF, WMemF.of_prefix h.wire_mem h.mF,
   RGrayF.of_prefix h.wire_rg h.rgF⟩

/-- The write domain's state changes: its inputs grow and its outputs are re-established. -/
theorem wgrow (h : Phi lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r rd wd s) {wd' : WStateF α n} {s' : FifoIO α}
    (h1 : wd.clk <+: wd'.clk) (h2 : wd.inc <+: wd'.inc) (h3 : wd.data <+: wd'.data) (h4 : wd.rgray <+: wd'.rgray)
    (h5 : wd.orc <+: wd'.orc)
    (hg : WGrayF lat stl su kq P_w S_w R_w pw_w wd'.clk wd'.inc wd'.data wd'.rgray wd'.orc wd'.gray_q)
    (hf : WFullF lat stl su kq P_w S_w R_w pw_w wd'.clk wd'.inc wd'.data wd'.rgray wd'.orc wd'.full_q)
    (hm : WMemF lat stl su kq P_w S_w R_w pw_w wd'.clk wd'.inc wd'.data wd'.rgray wd'.orc wd'.mem_q)
    (hwg : rd.wgray <+: wd'.gray_q) (hwm : rd.mem <+: wd'.mem_q) (hrg : wd'.rgray <+: rd.gray_q)
    (e1 : s'.wclk = wd'.clk) (e2 : s'.winc = wd'.inc) (e3 : s'.wdata = wd'.data)
    (e4 : s'.rclk = s.rclk) (e5 : s'.rinc = s.rinc) (e6 : s'.full = wd'.full_q) (e7 : s'.empty = s.empty)
    (e8 : s'.rdata = s.rdata) :
    Phi lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r rd wd' s' where
  wclk := e1.symm
  winc := e2.symm
  wdata := e3.symm
  rclk := by rw [e4]; exact h.rclk
  rinc := by rw [e5]; exact h.rinc
  full := e6
  empty := by rw [e7]; exact h.empty
  rdata := by rw [e8]; exact h.rdata
  gF := hg
  fF := hf
  mF := hm
  rgF := h.rgF
  reF := h.reF
  rdF := h.rdF
  wire_wg := hwg
  wire_mem := hwm
  wire_rg := hrg

/-- Only the write domain's inputs grow (outputs unchanged). -/
theorem winputs (h : Phi lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r rd wd s) {wd' : WStateF α n} {s' : FifoIO α}
    (h1 : wd.clk <+: wd'.clk) (h2 : wd.inc <+: wd'.inc) (h3 : wd.data <+: wd'.data) (h4 : wd.rgray <+: wd'.rgray)
    (h5 : wd.orc <+: wd'.orc) (hrg : wd'.rgray <+: rd.gray_q)
    (o1 : wd'.gray_q = wd.gray_q) (o2 : wd'.full_q = wd.full_q) (o3 : wd'.mem_q = wd.mem_q)
    (e1 : s'.wclk = wd'.clk) (e2 : s'.winc = wd'.inc) (e3 : s'.wdata = wd'.data)
    (e4 : s'.rclk = s.rclk) (e5 : s'.rinc = s.rinc) (e6 : s'.full = s.full) (e7 : s'.empty = s.empty)
    (e8 : s'.rdata = s.rdata) :
    Phi lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r rd wd' s' :=
  h.wgrow h1 h2 h3 h4 h5 (by rw [o1]; exact h.gF.mono h1 h2 h3 h4 h5)
    (by rw [o2]; exact h.fF.mono h1 h2 h3 h4 h5)
    (by rw [o3]; exact h.mF.mono h1 h2 h3 h4 h5)
    (by rw [o1]; exact h.wire_wg) (by rw [o3]; exact h.wire_mem) hrg e1 e2 e3 e4 e5 (by rw [e6, o2]; exact h.full) e7 e8

/-- The read domain's state changes. -/
theorem rgrow (h : Phi lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r rd wd s) {rd' : RStateF α n} {s' : FifoIO α}
    (h1 : rd.clk <+: rd'.clk) (h2 : rd.inc <+: rd'.inc) (h3 : rd.wgray <+: rd'.wgray) (h4 : rd.orc <+: rd'.orc)
    (h5 : rd.mem <+: rd'.mem)
    (hg : RGrayF lat stl su kq P_r S_r R_r pw_r rd'.clk rd'.inc rd'.wgray rd'.orc rd'.gray_q)
    (he : REmptyF lat stl su kq P_r S_r R_r pw_r rd'.clk rd'.inc rd'.wgray rd'.orc rd'.empty_q)
    (hd : RDataF lat stl su kq rdly P_r S_r R_r pw_r rd'.clk rd'.inc rd'.wgray rd'.orc rd'.mem rd'.rdata_q)
    (hwg : rd'.wgray <+: wd.gray_q) (hwm : rd'.mem <+: wd.mem_q) (hrg : wd.rgray <+: rd'.gray_q)
    (e1 : s'.wclk = s.wclk) (e2 : s'.winc = s.winc) (e3 : s'.wdata = s.wdata)
    (e4 : s'.rclk = rd'.clk) (e5 : s'.rinc = rd'.inc) (e6 : s'.full = s.full) (e7 : s'.empty = rd'.empty_q)
    (e8 : s'.rdata = rd'.rdata_q) :
    Phi lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r rd' wd s' where
  wclk := by rw [e1]; exact h.wclk
  winc := by rw [e2]; exact h.winc
  wdata := by rw [e3]; exact h.wdata
  rclk := e4.symm
  rinc := e5.symm
  full := by rw [e6]; exact h.full
  empty := e7
  rdata := e8
  gF := h.gF
  fF := h.fF
  mF := h.mF
  rgF := hg
  reF := he
  rdF := hd
  wire_wg := hwg
  wire_mem := hwm
  wire_rg := hrg

theorem rinputs (h : Phi lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r rd wd s) {rd' : RStateF α n} {s' : FifoIO α}
    (h1 : rd.clk <+: rd'.clk) (h2 : rd.inc <+: rd'.inc) (h3 : rd.wgray <+: rd'.wgray) (h4 : rd.orc <+: rd'.orc)
    (h5 : rd.mem <+: rd'.mem) (hwg : rd'.wgray <+: wd.gray_q) (hwm : rd'.mem <+: wd.mem_q)
    (o1 : rd'.gray_q = rd.gray_q) (o2 : rd'.empty_q = rd.empty_q) (o3 : rd'.rdata_q = rd.rdata_q)
    (e1 : s'.wclk = s.wclk) (e2 : s'.winc = s.winc) (e3 : s'.wdata = s.wdata)
    (e4 : s'.rclk = rd'.clk) (e5 : s'.rinc = rd'.inc) (e6 : s'.full = s.full) (e7 : s'.empty = s.empty)
    (e8 : s'.rdata = s.rdata) :
    Phi lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r rd' wd s' :=
  h.rgrow h1 h2 h3 h4 h5 (by rw [o1]; exact h.rgF.mono h1 h2 h3 h4)
    (by rw [o2]; exact h.reF.mono h1 h2 h3 h4)
    (by rw [o3]; exact h.rdF.mono h1 h2 h3 h4 h5)
    hwg hwm (by rw [o1]; exact h.wire_rg) e1 e2 e3 e4 e5 e6 (by rw [e7, o2]; exact h.empty) (by rw [e8, o3]; exact h.rdata)

/-- The circuit's current outputs satisfy the specification. -/
theorem fifoOK (hkw : kq + su < P_w) (hkr : kq + su < P_r) (hstlw : stl < P_w) (hstlr : stl < P_r)
    (hkrd : kq + rdly < P_r) (hrd : kq + rdly ≤ P_r + lat + 1) (hrdR : rdly ≤ R_r)
    (h : Phi lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r rd wd s) : FifoOK P_w P_r S_w S_r R_w R_r pw_w pw_r s := by
  obtain ⟨wclk, winc, wdata, rclk, rinc, full, empty, rdata⟩ := s
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, hgF, hfF, hmF, hrgF, hreF, hrdF, w1, w2, w3⟩ := h
  dsimp only at e1 e2 e3 e4 e5 e6 e7 e8
  subst e1 e2 e3 e4 e5 e6 e7 e8
  exact fifo_correctF (W := wires rd wd) hkw hkr hstlw hstlr hkrd hrd hrdR
    ⟨WGrayF.of_prefix w1 hgF, WMemF.of_prefix w2 hmF,
     RGrayF.of_prefix w3 hrgF⟩ hfF hreF hrdF

theorem init : Phi (n := n) lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r (⟨[], [], [], [], [], [], [], []⟩ : RStateF α n)
    (⟨[], [], [], [], [], [], [], []⟩ : WStateF α n) FifoIO.empty_io where
  wclk := rfl
  winc := rfl
  wdata := rfl
  rclk := rfl
  rinc := rfl
  full := rfl
  empty := rfl
  rdata := rfl
  gF := ⟨Nat.zero_le _, fun t ht => absurd ht (Nat.not_lt_zero t)⟩
  fF := ⟨Nat.zero_le _, fun t ht => absurd ht (Nat.not_lt_zero t)⟩
  mF := ⟨Nat.zero_le _, fun t ht => absurd ht (Nat.not_lt_zero t)⟩
  rgF := ⟨Nat.zero_le _, fun t ht => absurd ht (Nat.not_lt_zero t)⟩
  reF := ⟨Nat.zero_le _, fun t ht => absurd ht (Nat.not_lt_zero t)⟩
  rdF := ⟨Nat.zero_le _, fun t _ ht => absurd ht (Nat.not_lt_zero t)⟩
  wire_wg := List.nil_prefix
  wire_mem := List.nil_prefix
  wire_rg := List.nil_prefix

end Phi

/-! ### The specification's rules, one lemma per port -/

section SpecRules
variable (s : FifoIO α)

theorem spec_in_wclk (v : List Bool) (h : s.wclk ⊏ v) :
    ((fifoSpec α P_w P_r S_w S_r R_w R_r pw_w pw_r).inputs.getIO ↑"wclk").2 s v { s with wclk := v } := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩
theorem spec_in_winc (v : List Bool) (h : s.winc ⊏ v) :
    ((fifoSpec α P_w P_r S_w S_r R_w R_r pw_w pw_r).inputs.getIO ↑"winc").2 s v { s with winc := v } := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩
theorem spec_in_wdata (v : List α) (h : s.wdata ⊏ v) :
    ((fifoSpec α P_w P_r S_w S_r R_w R_r pw_w pw_r).inputs.getIO ↑"wdata").2 s v { s with wdata := v } := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩
theorem spec_in_rclk (v : List Bool) (h : s.rclk ⊏ v) :
    ((fifoSpec α P_w P_r S_w S_r R_w R_r pw_w pw_r).inputs.getIO ↑"rclk").2 s v { s with rclk := v } := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩
theorem spec_in_rinc (v : List Bool) (h : s.rinc ⊏ v) :
    ((fifoSpec α P_w P_r S_w S_r R_w R_r pw_w pw_r).inputs.getIO ↑"rinc").2 s v { s with rinc := v } := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem spec_out_full (v : List Bool) (h1 : s.full <+: v) (h2 : FifoOK P_w P_r S_w S_r R_w R_r pw_w pw_r { s with full := v }) :
    ((fifoSpec α P_w P_r S_w S_r R_w R_r pw_w pw_r).outputs.getIO ↑"full").2 s v { s with full := v } := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h1, h2, rfl⟩
theorem spec_out_empty (v : List Bool) (h1 : s.empty <+: v) (h2 : FifoOK P_w P_r S_w S_r R_w R_r pw_w pw_r { s with empty := v }) :
    ((fifoSpec α P_w P_r S_w S_r R_w R_r pw_w pw_r).outputs.getIO ↑"empty").2 s v { s with empty := v } := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h1, h2, rfl⟩
theorem spec_out_rdata (v : List α) (h1 : s.rdata <+: v) (h2 : FifoOK P_w P_r S_w S_r R_w R_r pw_w pw_r { s with rdata := v }) :
    ((fifoSpec α P_w P_r S_w S_r R_w R_r pw_w pw_r).outputs.getIO ↑"rdata").2 s v { s with rdata := v } := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h1, h2, rfl⟩

end SpecRules

/-! ### The transitions -/

section Cases

variable {rd : RStateF α n} {wd : WStateF α n} {s : FifoIO α} {u_r u_w : Unit}
  (Hφ : Phi lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r rd wd s)
include Hφ

theorem case_in_wclk (v : List Bool) (hlt : wd.clk ⊏ v) :
    ∃ almost mid, ((fifoSpec α P_w P_r S_w S_r R_w R_r pw_w pw_r).inputs.getIO ↑"wclk").2 s v almost ∧
      existSR (fifoSpec α P_w P_r S_w S_r R_w R_r pw_w pw_r).internals almost mid ∧
      φ lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r (u_r, rd, { wd with clk := v }, u_w) mid :=
  ⟨_, _, spec_in_wclk s v (by rw [← Hφ.wclk]; exact hlt), existSR_reflexive,
    Hφ.winputs hlt.isPrefix List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl Hφ.wire_rg rfl rfl rfl
      rfl Hφ.winc.symm Hφ.wdata.symm rfl rfl rfl rfl rfl⟩

theorem case_in_winc (v : List Bool) (hlt : wd.inc ⊏ v) :
    ∃ almost mid, ((fifoSpec α P_w P_r S_w S_r R_w R_r pw_w pw_r).inputs.getIO ↑"winc").2 s v almost ∧
      existSR (fifoSpec α P_w P_r S_w S_r R_w R_r pw_w pw_r).internals almost mid ∧
      φ lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r (u_r, rd, { wd with inc := v }, u_w) mid :=
  ⟨_, _, spec_in_winc s v (by rw [← Hφ.winc]; exact hlt), existSR_reflexive,
    Hφ.winputs List.prefix_rfl hlt.isPrefix List.prefix_rfl List.prefix_rfl List.prefix_rfl Hφ.wire_rg rfl rfl rfl
      Hφ.wclk.symm rfl Hφ.wdata.symm rfl rfl rfl rfl rfl⟩

theorem case_in_wdata (v : List α) (hlt : wd.data ⊏ v) :
    ∃ almost mid, ((fifoSpec α P_w P_r S_w S_r R_w R_r pw_w pw_r).inputs.getIO ↑"wdata").2 s v almost ∧
      existSR (fifoSpec α P_w P_r S_w S_r R_w R_r pw_w pw_r).internals almost mid ∧
      φ lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r (u_r, rd, { wd with data := v }, u_w) mid :=
  ⟨_, _, spec_in_wdata s v (by rw [← Hφ.wdata]; exact hlt), existSR_reflexive,
    Hφ.winputs List.prefix_rfl List.prefix_rfl hlt.isPrefix List.prefix_rfl List.prefix_rfl Hφ.wire_rg rfl rfl rfl
      Hφ.wclk.symm Hφ.winc.symm rfl rfl rfl rfl rfl rfl⟩

theorem case_in_rclk (v : List Bool) (hlt : rd.clk ⊏ v) :
    ∃ almost mid, ((fifoSpec α P_w P_r S_w S_r R_w R_r pw_w pw_r).inputs.getIO ↑"rclk").2 s v almost ∧
      existSR (fifoSpec α P_w P_r S_w S_r R_w R_r pw_w pw_r).internals almost mid ∧
      φ lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r (u_r, { rd with clk := v }, wd, u_w) mid :=
  ⟨_, _, spec_in_rclk s v (by rw [← Hφ.rclk]; exact hlt), existSR_reflexive,
    Hφ.rinputs hlt.isPrefix List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl Hφ.wire_wg Hφ.wire_mem
      rfl rfl rfl rfl rfl rfl rfl Hφ.rinc.symm rfl rfl rfl⟩

theorem case_in_rinc (v : List Bool) (hlt : rd.inc ⊏ v) :
    ∃ almost mid, ((fifoSpec α P_w P_r S_w S_r R_w R_r pw_w pw_r).inputs.getIO ↑"rinc").2 s v almost ∧
      existSR (fifoSpec α P_w P_r S_w S_r R_w R_r pw_w pw_r).internals almost mid ∧
      φ lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r (u_r, { rd with inc := v }, wd, u_w) mid :=
  ⟨_, _, spec_in_rinc s v (by rw [← Hφ.rinc]; exact hlt), existSR_reflexive,
    Hφ.rinputs List.prefix_rfl hlt.isPrefix List.prefix_rfl List.prefix_rfl List.prefix_rfl Hφ.wire_wg Hφ.wire_mem
      rfl rfl rfl rfl rfl rfl Hφ.rclk.symm rfl rfl rfl rfl⟩

variable (hkw : kq + su < P_w) (hkr : kq + su < P_r) (hstlw : stl < P_w) (hstlr : stl < P_r)
  (hkrd : kq + rdly < P_r) (hrd : kq + rdly ≤ P_r + lat + 1) (hrdR : rdly ≤ R_r)
include hkw hkr hstlw hstlr hkrd hrd hrdR

theorem case_out_full (v : List Bool) (h1 : wd.full_q <+: v)
    (h2 : WFullF lat stl su kq P_w S_w R_w pw_w wd.clk wd.inc wd.data wd.rgray wd.orc v) :
    ∃ almost mid, existSR (fifoSpec α P_w P_r S_w S_r R_w R_r pw_w pw_r).internals s almost ∧
      ((fifoSpec α P_w P_r S_w S_r R_w R_r pw_w pw_r).outputs.getIO ↑"full").2 almost v mid ∧
      φ lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r (u_r, rd, { wd with full_q := v }, u_w) mid := by
  have hφ : Phi lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r rd { wd with full_q := v } { s with full := v } :=
    Hφ.wgrow List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl Hφ.gF h2 Hφ.mF
      Hφ.wire_wg Hφ.wire_mem Hφ.wire_rg Hφ.wclk.symm Hφ.winc.symm Hφ.wdata.symm rfl rfl rfl rfl rfl
  exact ⟨s, _, existSR_reflexive, spec_out_full s v (by rw [Hφ.full]; exact h1) (hφ.fifoOK hkw hkr hstlw hstlr hkrd hrd hrdR), hφ⟩

theorem case_out_empty (v : List Bool) (h1 : rd.empty_q <+: v)
    (h2 : REmptyF lat stl su kq P_r S_r R_r pw_r rd.clk rd.inc rd.wgray rd.orc v) :
    ∃ almost mid, existSR (fifoSpec α P_w P_r S_w S_r R_w R_r pw_w pw_r).internals s almost ∧
      ((fifoSpec α P_w P_r S_w S_r R_w R_r pw_w pw_r).outputs.getIO ↑"empty").2 almost v mid ∧
      φ lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r (u_r, { rd with empty_q := v }, wd, u_w) mid := by
  have hφ : Phi lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r { rd with empty_q := v } wd { s with empty := v } :=
    Hφ.rgrow List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl Hφ.rgF h2 Hφ.rdF
      Hφ.wire_wg Hφ.wire_mem Hφ.wire_rg rfl rfl rfl Hφ.rclk.symm Hφ.rinc.symm rfl rfl Hφ.rdata
  exact ⟨s, _, existSR_reflexive, spec_out_empty s v (by rw [Hφ.empty]; exact h1) (hφ.fifoOK hkw hkr hstlw hstlr hkrd hrd hrdR), hφ⟩

theorem case_out_rdata (v : List α) (h1 : rd.rdata_q <+: v)
    (h2 : RDataF lat stl su kq rdly P_r S_r R_r pw_r rd.clk rd.inc rd.wgray rd.orc rd.mem v) :
    ∃ almost mid, existSR (fifoSpec α P_w P_r S_w S_r R_w R_r pw_w pw_r).internals s almost ∧
      ((fifoSpec α P_w P_r S_w S_r R_w R_r pw_w pw_r).outputs.getIO ↑"rdata").2 almost v mid ∧
      φ lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r (u_r, { rd with rdata_q := v }, wd, u_w) mid := by
  have hφ : Phi lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r { rd with rdata_q := v } wd { s with rdata := v } :=
    Hφ.rgrow List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl Hφ.rgF Hφ.reF h2
      Hφ.wire_wg Hφ.wire_mem Hφ.wire_rg rfl rfl rfl Hφ.rclk.symm Hφ.rinc.symm rfl Hφ.empty rfl
  exact ⟨s, _, existSR_reflexive, spec_out_rdata s v (by rw [Hφ.rdata]; exact h1) (hφ.fifoOK hkw hkr hstlw hstlr hkrd hrd hrdR), hφ⟩

end Cases

section Internal

variable {rd : RStateF α n} {wd : WStateF α n} {s : FifoIO α}
  (Hφ : Phi lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r rd wd s)
include Hφ

/-- The write domain's Gray pointer reaches the read domain. -/
theorem int_wgray (v : List (BitVec (n+1))) (h1 : wd.gray_q <+: v)
    (h2 : WGrayF lat stl su kq P_w S_w R_w pw_w wd.clk wd.inc wd.data wd.rgray wd.orc v) (h3 : rd.wgray ⊏ v) :
    Phi lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r { rd with wgray := v } { wd with gray_q := v } s :=
  (Hφ.wgrow (wd' := { wd with gray_q := v }) (s' := s) List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl
      List.prefix_rfl h2 Hφ.fF Hφ.mF (Hφ.wire_wg.trans h1) Hφ.wire_mem Hφ.wire_rg Hφ.wclk.symm Hφ.winc.symm Hφ.wdata.symm
      rfl rfl Hφ.full rfl rfl).rinputs (rd' := { rd with wgray := v }) (s' := s)
    List.prefix_rfl List.prefix_rfl h3.isPrefix List.prefix_rfl List.prefix_rfl List.prefix_rfl Hφ.wire_mem
    rfl rfl rfl rfl rfl rfl Hφ.rclk.symm Hφ.rinc.symm rfl rfl rfl

/-- The read domain's Gray pointer reaches the write domain. -/
theorem int_rgray (v : List (BitVec (n+1))) (h1 : rd.gray_q <+: v)
    (h2 : RGrayF lat stl su kq P_r S_r R_r pw_r rd.clk rd.inc rd.wgray rd.orc v) (h3 : wd.rgray ⊏ v) :
    Phi lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r { rd with gray_q := v } { wd with rgray := v } s :=
  (Hφ.rgrow (rd' := { rd with gray_q := v }) (s' := s) List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl
      List.prefix_rfl h2 Hφ.reF Hφ.rdF Hφ.wire_wg Hφ.wire_mem (Hφ.wire_rg.trans h1) rfl rfl rfl Hφ.rclk.symm Hφ.rinc.symm
      rfl Hφ.empty Hφ.rdata).winputs (wd' := { wd with rgray := v }) (s' := s)
    List.prefix_rfl List.prefix_rfl List.prefix_rfl h3.isPrefix List.prefix_rfl List.prefix_rfl
    rfl rfl rfl Hφ.wclk.symm Hφ.winc.symm Hφ.wdata.symm rfl rfl rfl rfl rfl

/-- The memory reaches the read domain. -/
theorem int_mem (v : List (BitVec n → α)) (h1 : wd.mem_q <+: v)
    (h2 : WMemF lat stl su kq P_w S_w R_w pw_w wd.clk wd.inc wd.data wd.rgray wd.orc v) (h3 : rd.mem ⊏ v) :
    Phi lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r { rd with mem := v } { wd with mem_q := v } s :=
  (Hφ.wgrow (wd' := { wd with mem_q := v }) (s' := s) List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl
      List.prefix_rfl Hφ.gF Hφ.fF h2 Hφ.wire_wg (Hφ.wire_mem.trans h1) Hφ.wire_rg Hφ.wclk.symm Hφ.winc.symm Hφ.wdata.symm
      rfl rfl Hφ.full rfl rfl).rinputs (rd' := { rd with mem := v }) (s' := s)
    List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl h3.isPrefix Hφ.wire_wg List.prefix_rfl
    rfl rfl rfl rfl rfl rfl Hφ.rclk.symm Hφ.rinc.symm rfl rfl rfl

theorem int_orcw (v : List (Orc n)) (h3 : wd.orc ⊏ v) :
    Phi lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r rd { wd with orc := v } s :=
  Hφ.winputs (wd' := { wd with orc := v }) (s' := s) List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl
    h3.isPrefix Hφ.wire_rg rfl rfl rfl Hφ.wclk.symm Hφ.winc.symm Hφ.wdata.symm rfl rfl rfl rfl rfl

theorem int_orcr (v : List (Orc n)) (h3 : rd.orc ⊏ v) :
    Phi lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r { rd with orc := v } wd s :=
  Hφ.rinputs (rd' := { rd with orc := v }) (s' := s) List.prefix_rfl List.prefix_rfl List.prefix_rfl h3.isPrefix
    List.prefix_rfl Hφ.wire_wg Hφ.wire_mem rfl rfl rfl rfl rfl rfl Hφ.rclk.symm Hφ.rinc.symm rfl rfl rfl

end Internal

/-- **Main theorem (step part).** -/
theorem refines_φ (hkw : kq + su < P_w) (hkr : kq + su < P_r) (hstlw : stl < P_w) (hstlr : stl < P_r)
    (hkrd : kq + rdly < P_r) (hrd : kq + rdly ≤ P_r + lat + 1) (hrdR : rdly ≤ R_r) :
    asyncFifoF α n lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r ⊑_{φ lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r} fifoSpec α P_w P_r S_w S_r R_w R_r pw_w pw_r := by
  intro i s Hφ
  obtain ⟨u_r, ⟨rclk_r, rinc_r, wgray_r, orcr, mem_r, rgq, req, rdq⟩,
    ⟨wclk_w, winc_w, wdata_w, rgray_w, orcw, wgq, wfq, wmq⟩, u_w⟩ := i
  dsimp only [φ] at Hφ
  constructor
  · -- Input rules: the specification accepts the same input.
    intro ident mid_i v Hrule
    obtain ⟨u_r', ⟨rclk_r', rinc_r', wgray_r', orcr', mem_r', rgq', req', rdq'⟩,
      ⟨wclk_w', winc_w', wdata_w', rgray_w', orcw', wgq', wfq', wmq'⟩, u_w'⟩ := mid_i
    case_transition Hcontains : Module.inputs (asyncFifoF α n lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r), ident,
      (PortMap.getIO_not_contained_false' Hrule)
    simp [asyncFifoF] at Hcontains
    rcases Hcontains with h | h | h | h | h
    all_goals subst h
    all_goals rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule
    all_goals dsimp only at Hrule
    all_goals simp only [Prod.mk.injEq, RStateF.mk.injEq, WStateF.mk.injEq, and_assoc] at Hrule
    all_goals repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
    · exact case_in_rclk Hφ _ ‹_ ⊏ _›
    · exact case_in_rinc Hφ _ ‹_ ⊏ _›
    · exact case_in_wclk Hφ _ ‹_ ⊏ _›
    · exact case_in_winc Hφ _ ‹_ ⊏ _›
    · exact case_in_wdata Hφ _ ‹_ ⊏ _›
  · -- Output rules: the specification can emit the same stream, thanks to `fifo_correctF`.
    intro ident mid_i v Hrule
    obtain ⟨u_r', ⟨rclk_r', rinc_r', wgray_r', orcr', mem_r', rgq', req', rdq'⟩,
      ⟨wclk_w', winc_w', wdata_w', rgray_w', orcw', wgq', wfq', wmq'⟩, u_w'⟩ := mid_i
    case_transition Hcontains : Module.outputs (asyncFifoF α n lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r), ident,
      (PortMap.getIO_not_contained_false' Hrule)
    simp [asyncFifoF] at Hcontains
    rcases Hcontains with h | h | h
    all_goals subst h
    all_goals rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule
    all_goals dsimp only at Hrule
    all_goals simp only [Prod.mk.injEq, RStateF.mk.injEq, WStateF.mk.injEq, and_assoc] at Hrule
    all_goals repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
    · exact case_out_empty Hφ hkw hkr hstlw hstlr hkrd hrd hrdR _ ‹_› ‹_›
    · exact case_out_rdata Hφ hkw hkr hstlw hstlr hkrd hrd hrdR _ ‹_› ‹_›
    · exact case_out_full Hφ hkw hkr hstlw hstlr hkrd hrd hrdR _ ‹_› ‹_›
  · -- Internal rules: the three wires and the two oracle feeds.  The specification does nothing.
    intro rule mid_i Hin Hrule
    obtain ⟨u_r', ⟨rclk_r', rinc_r', wgray_r', orcr', mem_r', rgq', req', rdq'⟩,
      ⟨wclk_w', winc_w', wdata_w', rgray_w', orcw', wgq', wfq', wmq'⟩, u_w'⟩ := mid_i
    simp only [asyncFifoF, List.mem_cons, List.not_mem_nil, or_false] at Hin
    rcases Hin with h | h | h | h | h
    all_goals subst h
    all_goals simp only [forall_const, and_true, not_true_eq_false, false_implies] at Hrule
    all_goals obtain ⟨⟨cu, ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩, ⟨c9, c10, c11, c12, c13, c14, c15, c16⟩, cu'⟩, out, Hrule⟩ := Hrule
    all_goals simp only [Prod.mk.injEq, RStateF.mk.injEq, WStateF.mk.injEq, and_assoc] at Hrule
    all_goals repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
    · exact ⟨s, existSR_reflexive, int_wgray Hφ _ ‹_› ‹_› ‹_›⟩
    · exact ⟨s, existSR_reflexive, int_rgray Hφ _ ‹_› ‹_› ‹_›⟩
    · exact ⟨s, existSR_reflexive, int_mem Hφ _ ‹_› ‹_› ‹_›⟩
    · exact ⟨s, existSR_reflexive, int_orcw Hφ _ ‹_›⟩
    · exact ⟨s, existSR_reflexive, int_orcr Hφ _ ‹_›⟩

/-- **Main theorem (initial part).** -/
theorem refines_initial :
    Module.refines_initial (asyncFifoF α n lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r) (fifoSpec α P_w P_r S_w S_r R_w R_r pw_w pw_r)
      (φ lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r) := by
  intro i hi
  obtain ⟨u_r, ⟨rclk_r, rinc_r, wgray_r, orcr, mem_r, rgq, req, rdq⟩,
    ⟨wclk_w, winc_w, wdata_w, rgray_w, orcw, wgq, wfq, wmq⟩, u_w⟩ := i
  simp only [asyncFifoF, RStateF.mk.injEq, WStateF.mk.injEq, true_and, and_true] at hi
  obtain ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩ := hi
  exact ⟨FifoIO.empty_io, rfl, Phi.init⟩

/-- **The asynchronous FIFO over filtered domains refines the FIFO specification**, for any
data type, depth, wire latency, and any settling time `stl`, clk-to-q window `kq` and setup
window `su` such that `stl < P` and `kq + su < P` for both clock periods assumed by the
specification. -/
theorem refinesF (hkw : kq + su < P_w) (hkr : kq + su < P_r) (hstlw : stl < P_w) (hstlr : stl < P_r)
    (hkrd : kq + rdly < P_r) (hrd : kq + rdly ≤ P_r + lat + 1) (hrdR : rdly ≤ R_r) :
    asyncFifoF α n lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r ⊑ fifoSpec α P_w P_r S_w S_r R_w R_r pw_w pw_r :=
  ⟨inferInstance, φ lat stl su kq rdly P_w P_r S_w S_r R_w R_r pw_w pw_r, refines_φ hkw hkr hstlw hstlr hkrd hrd hrdR, refines_initial⟩

end Graphiti.AsyncFifo
