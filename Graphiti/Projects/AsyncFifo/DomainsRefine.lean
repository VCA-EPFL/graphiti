/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.TimedRefinement

/-!
# The exact domains refine the filtered domains

`writeDomain_refines` and `readDomain_refines`: the register-level domains of `Modules.lean`,
whose outputs are the exact streams of `Domains.lean`, refine their filtered versions for any
clk-to-q window `kq` and any filter parameters — the exact outputs satisfy the relaxed
relations everywhere (`WGrayF.of_exact`, …).  With `Lifting.lean` this recovers the
register-level FIFO theorem from the one over filtered domains.
-/

set_option linter.unusedSectionVars false

namespace Graphiti.AsyncFifo

variable {α : Type} [Inhabited α] {n lat stl su kq rdly P S R pw : Nat}

/-! ### Write domain -/

instance : MatchInterface (writeDomain α n lat stl su) (writeDomainF α n lat stl su kq P S R pw) := by
  dsimp [writeDomain, writeDomainF]
  solve_match_interface

/-- Same inputs; the filtered module's histories are prefixes of the exact outputs. -/
structure PhiW (lat stl su : Nat) (clk inc : List Bool) (data : List α) (rgray : List (BitVec (n+1))) (orc : List (Orc n))
    (s : WStateF α n) : Prop where
  clk_eq : clk = s.clk
  inc_eq : inc = s.inc
  data_eq : data = s.data
  rgray_eq : rgray = s.rgray
  orc_eq : orc = s.orc
  gray : s.gray_q <+: wGray lat stl su clk inc data rgray orc
  full : s.full_q <+: wFull lat stl su clk inc data rgray orc
  mem : s.mem_q <+: wMem lat stl su clk inc data rgray orc

def φW (lat stl su : Nat) (e : WState α n) (s : WStateF α n) : Prop :=
  PhiW lat stl su e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2 s

namespace PhiW

variable {clk inc : List Bool} {data : List α} {rgray : List (BitVec (n+1))} {orc : List (Orc n)} {s : WStateF α n}
  (h : PhiW lat stl su clk inc data rgray orc s)
include h

theorem grow {clk' inc' : List Bool} {data' : List α} {rgray' : List (BitVec (n+1))} {orc' : List (Orc n)}
    (h1 : clk <+: clk') (h2 : inc <+: inc') (h3 : data <+: data') (h4 : rgray <+: rgray') (h5 : orc <+: orc')
    {s' : WStateF α n} (e1 : s'.clk = clk') (e2 : s'.inc = inc') (e3 : s'.data = data') (e4 : s'.rgray = rgray')
    (e5 : s'.orc = orc') (o1 : s'.gray_q = s.gray_q) (o2 : s'.full_q = s.full_q) (o3 : s'.mem_q = s.mem_q) :
    PhiW lat stl su clk' inc' data' rgray' orc' s' where
  clk_eq := e1.symm
  inc_eq := e2.symm
  data_eq := e3.symm
  rgray_eq := e4.symm
  orc_eq := e5.symm
  gray := by rw [o1]; exact h.gray.trans (wGray_mono _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5)
  full := by rw [o2]; exact h.full.trans (wFull_mono _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5)
  mem := by rw [o3]; exact h.mem.trans (wMem_mono _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5)

theorem out_gray : PhiW lat stl su clk inc data rgray orc { s with gray_q := wGray lat stl su clk inc data rgray orc } :=
  ⟨h.clk_eq, h.inc_eq, h.data_eq, h.rgray_eq, h.orc_eq, List.prefix_rfl, h.full, h.mem⟩
theorem out_full : PhiW lat stl su clk inc data rgray orc { s with full_q := wFull lat stl su clk inc data rgray orc } :=
  ⟨h.clk_eq, h.inc_eq, h.data_eq, h.rgray_eq, h.orc_eq, h.gray, List.prefix_rfl, h.mem⟩
theorem out_mem : PhiW lat stl su clk inc data rgray orc { s with mem_q := wMem lat stl su clk inc data rgray orc } :=
  ⟨h.clk_eq, h.inc_eq, h.data_eq, h.rgray_eq, h.orc_eq, h.gray, h.full, List.prefix_rfl⟩

theorem grayF : WGrayF lat stl su kq P S R pw s.clk s.inc s.data s.rgray s.orc (wGray lat stl su clk inc data rgray orc) := by
  rw [← h.clk_eq, ← h.inc_eq, ← h.data_eq, ← h.rgray_eq, ← h.orc_eq]; exact WGrayF.of_exact List.prefix_rfl
theorem fullF : WFullF lat stl su kq P S R pw s.clk s.inc s.data s.rgray s.orc (wFull lat stl su clk inc data rgray orc) := by
  rw [← h.clk_eq, ← h.inc_eq, ← h.data_eq, ← h.rgray_eq, ← h.orc_eq]; exact WFullF.of_exact List.prefix_rfl
theorem memF : WMemF lat stl su kq P S R pw s.clk s.inc s.data s.rgray s.orc (wMem lat stl su clk inc data rgray orc) := by
  rw [← h.clk_eq, ← h.inc_eq, ← h.data_eq, ← h.rgray_eq, ← h.orc_eq]; exact WMemF.of_exact List.prefix_rfl

end PhiW

theorem writeDomain_refines_φ : writeDomain α n lat stl su ⊑_{φW lat stl su} writeDomainF α n lat stl su kq P S R pw := by
  intro i s Hφ
  obtain ⟨clk, inc, data, rgray, orc⟩ := i
  dsimp only [φW] at Hφ
  constructor
  · intro ident mid_i v Hrule
    obtain ⟨clk', inc', data', rgray', orc'⟩ := mid_i
    case_transition Hcontains : Module.inputs (writeDomain α n lat stl su), ident,
      (PortMap.getIO_not_contained_false' Hrule)
    simp [writeDomain] at Hcontains
    rcases Hcontains with h | h | h | h | h
    all_goals subst h
    all_goals rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule
    all_goals dsimp only at Hrule
    all_goals simp only [Prod.mk.injEq, and_assoc] at Hrule
    all_goals repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
    · exact ⟨_, _, Timed.spec_in_clk s _ (by rw [← Hφ.clk_eq]; assumption), existSR_reflexive,
        Hφ.grow (‹_ ⊏ _› : _ ⊏ _).isPrefix List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl
          rfl Hφ.inc_eq.symm Hφ.data_eq.symm Hφ.rgray_eq.symm Hφ.orc_eq.symm rfl rfl rfl⟩
    · exact ⟨_, _, Timed.spec_in_inc s _ (by rw [← Hφ.inc_eq]; assumption), existSR_reflexive,
        Hφ.grow List.prefix_rfl (‹_ ⊏ _› : _ ⊏ _).isPrefix List.prefix_rfl List.prefix_rfl List.prefix_rfl
          Hφ.clk_eq.symm rfl Hφ.data_eq.symm Hφ.rgray_eq.symm Hφ.orc_eq.symm rfl rfl rfl⟩
    · exact ⟨_, _, Timed.spec_in_data s _ (by rw [← Hφ.data_eq]; assumption), existSR_reflexive,
        Hφ.grow List.prefix_rfl List.prefix_rfl (‹_ ⊏ _› : _ ⊏ _).isPrefix List.prefix_rfl List.prefix_rfl
          Hφ.clk_eq.symm Hφ.inc_eq.symm rfl Hφ.rgray_eq.symm Hφ.orc_eq.symm rfl rfl rfl⟩
    · exact ⟨_, _, Timed.spec_in_rgray s _ (by rw [← Hφ.rgray_eq]; assumption), existSR_reflexive,
        Hφ.grow List.prefix_rfl List.prefix_rfl List.prefix_rfl (‹_ ⊏ _› : _ ⊏ _).isPrefix List.prefix_rfl
          Hφ.clk_eq.symm Hφ.inc_eq.symm Hφ.data_eq.symm rfl Hφ.orc_eq.symm rfl rfl rfl⟩
    · exact ⟨_, _, Timed.spec_in_orc s _ (by rw [← Hφ.orc_eq]; assumption), existSR_reflexive,
        Hφ.grow List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl (‹_ ⊏ _› : _ ⊏ _).isPrefix
          Hφ.clk_eq.symm Hφ.inc_eq.symm Hφ.data_eq.symm Hφ.rgray_eq.symm rfl rfl rfl rfl⟩
  · intro ident mid_i v Hrule
    obtain ⟨clk', inc', data', rgray', orc'⟩ := mid_i
    case_transition Hcontains : Module.outputs (writeDomain α n lat stl su), ident,
      (PortMap.getIO_not_contained_false' Hrule)
    simp [writeDomain] at Hcontains
    rcases Hcontains with h | h | h
    all_goals subst h
    all_goals rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule
    all_goals dsimp only at Hrule
    all_goals simp only [Prod.mk.injEq, and_assoc] at Hrule
    all_goals repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
    · exact ⟨s, _, existSR_reflexive, Timed.spec_out_gray s _ Hφ.gray Hφ.grayF, Hφ.out_gray⟩
    · exact ⟨s, _, existSR_reflexive, Timed.spec_out_full s _ Hφ.full Hφ.fullF, Hφ.out_full⟩
    · exact ⟨s, _, existSR_reflexive, Timed.spec_out_mem s _ Hφ.mem Hφ.memF, Hφ.out_mem⟩
  · intro rule mid_i Hin Hrule
    simp [writeDomain] at Hin

theorem writeDomain_refines_initial :
    Module.refines_initial (writeDomain α n lat stl su) (writeDomainF α n lat stl su kq P S R pw) (φW lat stl su) := by
  intro i hi
  obtain ⟨clk, inc, data, rgray, orc⟩ := i
  simp only [writeDomain, Prod.mk.injEq] at hi
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hi
  exact ⟨⟨[], [], [], [], [], [], [], []⟩, rfl,
    ⟨rfl, rfl, rfl, rfl, rfl, List.nil_prefix, List.nil_prefix, List.nil_prefix⟩⟩

/-- The exact write domain refines the filtered one, for any windows and filters. -/
theorem writeDomain_refines : writeDomain α n lat stl su ⊑ writeDomainF α n lat stl su kq P S R pw :=
  ⟨inferInstance, φW lat stl su, writeDomain_refines_φ, writeDomain_refines_initial⟩

/-! ### Read domain -/

instance : MatchInterface (readDomain α n lat stl su) (readDomainF α n lat stl su kq rdly P S R pw) := by
  dsimp [readDomain, readDomainF]
  solve_match_interface

structure PhiR (lat stl su : Nat) (clk inc : List Bool) (wgray : List (BitVec (n+1))) (orc : List (Orc n))
    (mem : List (BitVec n → α)) (s : RStateF α n) : Prop where
  clk_eq : clk = s.clk
  inc_eq : inc = s.inc
  wgray_eq : wgray = s.wgray
  orc_eq : orc = s.orc
  mem_eq : mem = s.mem
  gray : s.gray_q <+: rGray lat stl su clk inc wgray orc
  empty : s.empty_q <+: rEmpty lat stl su clk inc wgray orc
  rdata : s.rdata_q <+: rData lat stl su clk inc wgray orc mem

def φR (lat stl su : Nat) (e : RState α n) (s : RStateF α n) : Prop :=
  PhiR lat stl su e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2 s

namespace PhiR

variable {clk inc : List Bool} {wgray : List (BitVec (n+1))} {orc : List (Orc n)} {mem : List (BitVec n → α)}
  {s : RStateF α n} (h : PhiR lat stl su clk inc wgray orc mem s)
include h

theorem grow {clk' inc' : List Bool} {wgray' : List (BitVec (n+1))} {orc' : List (Orc n)} {mem' : List (BitVec n → α)}
    (h1 : clk <+: clk') (h2 : inc <+: inc') (h3 : wgray <+: wgray') (h4 : orc <+: orc') (h5 : mem <+: mem')
    {s' : RStateF α n} (e1 : s'.clk = clk') (e2 : s'.inc = inc') (e3 : s'.wgray = wgray') (e4 : s'.orc = orc')
    (e5 : s'.mem = mem') (o1 : s'.gray_q = s.gray_q) (o2 : s'.empty_q = s.empty_q) (o3 : s'.rdata_q = s.rdata_q) :
    PhiR lat stl su clk' inc' wgray' orc' mem' s' where
  clk_eq := e1.symm
  inc_eq := e2.symm
  wgray_eq := e3.symm
  orc_eq := e4.symm
  mem_eq := e5.symm
  gray := by rw [o1]; exact h.gray.trans (rGray_mono _ _ _ _ _ _ _ h1 h2 h3 h4)
  empty := by rw [o2]; exact h.empty.trans (rEmpty_mono _ _ _ _ _ _ _ h1 h2 h3 h4)
  rdata := by rw [o3]; exact h.rdata.trans (rData_mono _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5)

theorem out_gray : PhiR lat stl su clk inc wgray orc mem { s with gray_q := rGray lat stl su clk inc wgray orc } :=
  ⟨h.clk_eq, h.inc_eq, h.wgray_eq, h.orc_eq, h.mem_eq, List.prefix_rfl, h.empty, h.rdata⟩
theorem out_empty : PhiR lat stl su clk inc wgray orc mem { s with empty_q := rEmpty lat stl su clk inc wgray orc } :=
  ⟨h.clk_eq, h.inc_eq, h.wgray_eq, h.orc_eq, h.mem_eq, h.gray, List.prefix_rfl, h.rdata⟩
theorem out_rdata : PhiR lat stl su clk inc wgray orc mem { s with rdata_q := rData lat stl su clk inc wgray orc mem } :=
  ⟨h.clk_eq, h.inc_eq, h.wgray_eq, h.orc_eq, h.mem_eq, h.gray, h.empty, List.prefix_rfl⟩

theorem grayF : RGrayF lat stl su kq P S R pw s.clk s.inc s.wgray s.orc (rGray lat stl su clk inc wgray orc) := by
  rw [← h.clk_eq, ← h.inc_eq, ← h.wgray_eq, ← h.orc_eq]; exact RGrayF.of_exact List.prefix_rfl
theorem emptyF : REmptyF lat stl su kq P S R pw s.clk s.inc s.wgray s.orc (rEmpty lat stl su clk inc wgray orc) := by
  rw [← h.clk_eq, ← h.inc_eq, ← h.wgray_eq, ← h.orc_eq]; exact REmptyF.of_exact List.prefix_rfl
theorem rdataF : RDataF lat stl su kq rdly P S R pw s.clk s.inc s.wgray s.orc s.mem (rData lat stl su clk inc wgray orc mem) := by
  rw [← h.clk_eq, ← h.inc_eq, ← h.wgray_eq, ← h.orc_eq, ← h.mem_eq]; exact RDataF.of_exact List.prefix_rfl

end PhiR

section RSpecRules
variable (s : RStateF α n)

theorem rspec_in_clk (v : List Bool) (h : s.clk ⊏ v) :
    ((readDomainF α n lat stl su kq rdly P S R pw).inputs.getIO ↑"clk").2 s v { s with clk := v } := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩
theorem rspec_in_inc (v : List Bool) (h : s.inc ⊏ v) :
    ((readDomainF α n lat stl su kq rdly P S R pw).inputs.getIO ↑"inc").2 s v { s with inc := v } := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩
theorem rspec_in_wgray (v : List (BitVec (n+1))) (h : s.wgray ⊏ v) :
    ((readDomainF α n lat stl su kq rdly P S R pw).inputs.getIO ↑"wgray").2 s v { s with wgray := v } := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩
theorem rspec_in_orc (v : List (Orc n)) (h : s.orc ⊏ v) :
    ((readDomainF α n lat stl su kq rdly P S R pw).inputs.getIO ↑"orc").2 s v { s with orc := v } := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩
theorem rspec_in_mem (v : List (BitVec n → α)) (h : s.mem ⊏ v) :
    ((readDomainF α n lat stl su kq rdly P S R pw).inputs.getIO ↑"mem").2 s v { s with mem := v } := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem rspec_out_gray (v : List (BitVec (n+1))) (h1 : s.gray_q <+: v)
    (h2 : RGrayF lat stl su kq P S R pw s.clk s.inc s.wgray s.orc v) :
    ((readDomainF α n lat stl su kq rdly P S R pw).outputs.getIO ↑"gray").2 s v { s with gray_q := v } := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h1, h2, rfl⟩
theorem rspec_out_empty (v : List Bool) (h1 : s.empty_q <+: v)
    (h2 : REmptyF lat stl su kq P S R pw s.clk s.inc s.wgray s.orc v) :
    ((readDomainF α n lat stl su kq rdly P S R pw).outputs.getIO ↑"empty").2 s v { s with empty_q := v } := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h1, h2, rfl⟩
theorem rspec_out_rdata (v : List α) (h1 : s.rdata_q <+: v)
    (h2 : RDataF lat stl su kq rdly P S R pw s.clk s.inc s.wgray s.orc s.mem v) :
    ((readDomainF α n lat stl su kq rdly P S R pw).outputs.getIO ↑"rdata").2 s v { s with rdata_q := v } := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h1, h2, rfl⟩

end RSpecRules

theorem readDomain_refines_φ : readDomain α n lat stl su ⊑_{φR lat stl su} readDomainF α n lat stl su kq rdly P S R pw := by
  intro i s Hφ
  obtain ⟨clk, inc, wgray, orc, mem⟩ := i
  dsimp only [φR] at Hφ
  constructor
  · intro ident mid_i v Hrule
    obtain ⟨clk', inc', wgray', orc', mem'⟩ := mid_i
    case_transition Hcontains : Module.inputs (readDomain α n lat stl su), ident,
      (PortMap.getIO_not_contained_false' Hrule)
    simp [readDomain] at Hcontains
    rcases Hcontains with h | h | h | h | h
    all_goals subst h
    all_goals rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule
    all_goals dsimp only at Hrule
    all_goals simp only [Prod.mk.injEq, and_assoc] at Hrule
    all_goals repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
    · exact ⟨_, _, rspec_in_clk s _ (by rw [← Hφ.clk_eq]; assumption), existSR_reflexive,
        Hφ.grow (‹_ ⊏ _› : _ ⊏ _).isPrefix List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl
          rfl Hφ.inc_eq.symm Hφ.wgray_eq.symm Hφ.orc_eq.symm Hφ.mem_eq.symm rfl rfl rfl⟩
    · exact ⟨_, _, rspec_in_inc s _ (by rw [← Hφ.inc_eq]; assumption), existSR_reflexive,
        Hφ.grow List.prefix_rfl (‹_ ⊏ _› : _ ⊏ _).isPrefix List.prefix_rfl List.prefix_rfl List.prefix_rfl
          Hφ.clk_eq.symm rfl Hφ.wgray_eq.symm Hφ.orc_eq.symm Hφ.mem_eq.symm rfl rfl rfl⟩
    · exact ⟨_, _, rspec_in_wgray s _ (by rw [← Hφ.wgray_eq]; assumption), existSR_reflexive,
        Hφ.grow List.prefix_rfl List.prefix_rfl (‹_ ⊏ _› : _ ⊏ _).isPrefix List.prefix_rfl List.prefix_rfl
          Hφ.clk_eq.symm Hφ.inc_eq.symm rfl Hφ.orc_eq.symm Hφ.mem_eq.symm rfl rfl rfl⟩
    · exact ⟨_, _, rspec_in_orc s _ (by rw [← Hφ.orc_eq]; assumption), existSR_reflexive,
        Hφ.grow List.prefix_rfl List.prefix_rfl List.prefix_rfl (‹_ ⊏ _› : _ ⊏ _).isPrefix List.prefix_rfl
          Hφ.clk_eq.symm Hφ.inc_eq.symm Hφ.wgray_eq.symm rfl Hφ.mem_eq.symm rfl rfl rfl⟩
    · exact ⟨_, _, rspec_in_mem s _ (by rw [← Hφ.mem_eq]; assumption), existSR_reflexive,
        Hφ.grow List.prefix_rfl List.prefix_rfl List.prefix_rfl List.prefix_rfl (‹_ ⊏ _› : _ ⊏ _).isPrefix
          Hφ.clk_eq.symm Hφ.inc_eq.symm Hφ.wgray_eq.symm Hφ.orc_eq.symm rfl rfl rfl rfl⟩
  · intro ident mid_i v Hrule
    obtain ⟨clk', inc', wgray', orc', mem'⟩ := mid_i
    case_transition Hcontains : Module.outputs (readDomain α n lat stl su), ident,
      (PortMap.getIO_not_contained_false' Hrule)
    simp [readDomain] at Hcontains
    rcases Hcontains with h | h | h
    all_goals subst h
    all_goals rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule
    all_goals dsimp only at Hrule
    all_goals simp only [Prod.mk.injEq, and_assoc] at Hrule
    all_goals repeat' (obtain ⟨h, Hrule⟩ := Hrule; try subst h)
    · exact ⟨s, _, existSR_reflexive, rspec_out_gray s _ Hφ.gray Hφ.grayF, Hφ.out_gray⟩
    · exact ⟨s, _, existSR_reflexive, rspec_out_empty s _ Hφ.empty Hφ.emptyF, Hφ.out_empty⟩
    · exact ⟨s, _, existSR_reflexive, rspec_out_rdata s _ Hφ.rdata Hφ.rdataF, Hφ.out_rdata⟩
  · intro rule mid_i Hin Hrule
    simp [readDomain] at Hin

theorem readDomain_refines_initial :
    Module.refines_initial (readDomain α n lat stl su) (readDomainF α n lat stl su kq rdly P S R pw) (φR lat stl su) := by
  intro i hi
  obtain ⟨clk, inc, wgray, orc, mem⟩ := i
  simp only [readDomain, Prod.mk.injEq] at hi
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hi
  exact ⟨⟨[], [], [], [], [], [], [], []⟩, rfl,
    ⟨rfl, rfl, rfl, rfl, rfl, List.nil_prefix, List.nil_prefix, List.nil_prefix⟩⟩

/-- The exact read domain refines the filtered one, for any windows and filters. -/
theorem readDomain_refines : readDomain α n lat stl su ⊑ readDomainF α n lat stl su kq rdly P S R pw :=
  ⟨inferInstance, φR lat stl su, readDomain_refines_φ, readDomain_refines_initial⟩

end Graphiti.AsyncFifo
