/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.ProofWriteOnly.EnRegTiming
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.RegFileLemmas

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Graphiti.AsyncFifo.RegFile

open Graphiti.AsyncFifo Graphiti.AsyncFifo.Gates Graphiti.AsyncFifo.Contracts Graphiti.AsyncFifo.Timed
  Graphiti.AsyncFifo.Dff Graphiti.AsyncFifo.EnReg
variable {clk we : List Bool} {addr : List (BitVec 2)} {data crn : List Bool} {R : Nat}

/-! ### The netlist, as an index type

Each wire holds a prefix of what drives it.  Over an index rather than a record with one field
per wire, the per-rule lemmas collapse into `Netlist.Wf_step_of`, `Netlist.Wf_drv` and
`Netlist.Wf_congr`, so what is written here is the circuit and nothing else. -/

open Graphiti.AsyncFifo.Netlist

/-- The 42 driven wires.  The block's own clock, write enable, address, data and clear are not
among them: they are inputs, closed over by `drv`. -/
inductive W
  | en2_a
  | en2_b
  | en3_a
  | en3_b
  | pk_q0
  | pk_q1
  | pk_q2
  | pk_q3
  | dec3_a
  | dec3_b
  | c2_clk
  | c2_en
  | c2_data
  | c2_clrn
  | c3_clk
  | c3_en
  | c3_data
  | c3_clrn
  | a0F_in
  | na0F_in
  | a1F_in
  | na1_a
  | en0_a
  | en0_b
  | c0_clk
  | c0_en
  | c0_data
  | c0_clrn
  | en1_a
  | en1_b
  | na0_a
  | dec0_a
  | dec0_b
  | dec2_a
  | dec2_b
  | dec1_a
  | dec1_b
  | na1F_in
  | c1_clk
  | c1_en
  | c1_data
  | c1_clrn
  deriving DecidableEq

/-- What drives each wire: one line per wire, and the only place the shape of this netlist is
written down.  The address decoder is the four `dec`/`en` pairs; each cell is an `enReg`. -/
def drv (clk we : List Bool) (addr : List (BitVec 2)) (dat crn : List Bool) : Drv W
  | _, .en2_a => we
  | w, .en2_b => gateOut and2 (w .dec2_a) (w .dec2_b)
  | _, .en3_a => we
  | w, .en3_b => gateOut and2 (w .dec3_a) (w .dec3_b)
  | w, .pk_q0 => enOut (w .c0_clk) (w .c0_en) (w .c0_data) (w .c0_clrn)
  | w, .pk_q1 => enOut (w .c1_clk) (w .c1_en) (w .c1_data) (w .c1_clrn)
  | w, .pk_q2 => enOut (w .c2_clk) (w .c2_en) (w .c2_data) (w .c2_clrn)
  | w, .pk_q3 => enOut (w .c3_clk) (w .c3_en) (w .c3_data) (w .c3_clrn)
  | w, .dec3_a => (w .a0F_in)
  | w, .dec3_b => (w .a1F_in)
  | _, .c2_clk => clk
  | w, .c2_en => gateOut and2 (w .en2_a) (w .en2_b)
  | _, .c2_data => dat
  | _, .c2_clrn => crn
  | _, .c3_clk => clk
  | w, .c3_en => gateOut and2 (w .en3_a) (w .en3_b)
  | _, .c3_data => dat
  | _, .c3_clrn => crn
  | _, .a0F_in => bitsA 0 addr
  | w, .na0F_in => gate1Out not (w .na0_a)
  | _, .a1F_in => bitsA 1 addr
  | w, .na1_a => (w .a1F_in)
  | _, .en0_a => we
  | w, .en0_b => gateOut and2 (w .dec0_a) (w .dec0_b)
  | _, .c0_clk => clk
  | w, .c0_en => gateOut and2 (w .en0_a) (w .en0_b)
  | _, .c0_data => dat
  | _, .c0_clrn => crn
  | _, .en1_a => we
  | w, .en1_b => gateOut and2 (w .dec1_a) (w .dec1_b)
  | w, .na0_a => (w .a0F_in)
  | w, .dec0_a => (w .na0F_in)
  | w, .dec0_b => (w .na1F_in)
  | w, .dec2_a => (w .na0F_in)
  | w, .dec2_b => (w .a1F_in)
  | w, .dec1_a => (w .a0F_in)
  | w, .dec1_b => (w .na1F_in)
  | w, .na1F_in => gate1Out not (w .na1_a)
  | _, .c1_clk => clk
  | w, .c1_en => gateOut and2 (w .en1_a) (w .en1_b)
  | _, .c1_data => dat
  | _, .c1_clrn => crn

theorem drv_mono {clk we addr dat crn} : Mono (drv clk we addr dat crn) := by
  intro a b h k
  cases k <;> simp only [drv] <;>
    apply_rules [List.prefix_rfl, h, gateOut_mono, gate1Out_mono, enOut_mono]
theorem drv_env {clk clk' we we' dat dat' crn crn' : List Bool} {addr addr' : List (BitVec 2)}
    (hclk : clk <+: clk') (hwe : we <+: we') (haddr : addr <+: addr') (hdat : dat <+: dat')
    (hcrn : crn <+: crn') (w : Wires W) (k : W) :
    drv clk we addr dat crn w k <+: drv clk' we' addr' dat' crn' w k := by
  cases k <;> simp only [drv] <;>
    apply_rules [List.prefix_rfl, hclk, hwe, hdat, hcrn, bitsA_mono, haddr,
                 gateOut_mono, gate1Out_mono, enOut_mono]
def wires (i : memT) : Wires W
  | .en2_a => i.1.1
  | .en2_b => i.1.2
  | .en3_a => i.2.1.1
  | .en3_b => i.2.1.2
  | .pk_q0 => i.2.2.1.1
  | .pk_q1 => i.2.2.1.2.1
  | .pk_q2 => i.2.2.1.2.2.1
  | .pk_q3 => i.2.2.1.2.2.2
  | .dec3_a => i.2.2.2.1.1
  | .dec3_b => i.2.2.2.1.2
  | .c2_clk => i.2.2.2.2.1.1
  | .c2_en => i.2.2.2.2.1.2.1
  | .c2_data => i.2.2.2.2.1.2.2.1
  | .c2_clrn => i.2.2.2.2.1.2.2.2
  | .c3_clk => i.2.2.2.2.2.1.1
  | .c3_en => i.2.2.2.2.2.1.2.1
  | .c3_data => i.2.2.2.2.2.1.2.2.1
  | .c3_clrn => i.2.2.2.2.2.1.2.2.2
  | .a0F_in => i.2.2.2.2.2.2.1
  | .na0F_in => i.2.2.2.2.2.2.2.2.1
  | .a1F_in => i.2.2.2.2.2.2.2.2.2.1
  | .na1_a => i.2.2.2.2.2.2.2.2.2.2.2.2.1
  | .en0_a => i.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
  | .en0_b => i.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2
  | .c0_clk => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
  | .c0_en => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.1
  | .c0_data => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1
  | .c0_clrn => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2
  | .en1_a => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
  | .en1_b => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2
  | .na0_a => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | .dec0_a => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
  | .dec0_b => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2
  | .dec2_a => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
  | .dec2_b => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2
  | .dec1_a => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
  | .dec1_b => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2
  | .na1F_in => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | .c1_clk => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | .c1_en => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | .c1_data => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | .c1_clrn => i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- The invariant: the wires are well formed, the five inputs the netlist holds are the
specification's, and the packer has reported no more than the four cells hold. -/
def ψ (i : memT) (s : List Bool × List Bool × List (BitVec 2) × List Bool × List Bool ×
    List (BitVec 2 → Bool)) : Prop :=
  Wf (drv s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2.1) (wires i)
    ∧ i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 = s.1
    ∧ i.2.2.2.2.2.2.2.2.2.2.2.1 = s.2.1
    ∧ i.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 = s.2.2.1
    ∧ i.2.2.2.2.2.2.2.2.2.2.1 = s.2.2.2.1
    ∧ i.2.2.2.2.2.2.2.1 = s.2.2.2.2.1
    ∧ s.2.2.2.2.2 <+: packMemOut (wires i .pk_q0) (wires i .pk_q1) (wires i .pk_q2)
        (wires i .pk_q3)

/-! ### What the four cells hold

The decoder is read forwards -- address bit, its complement, the four `and`s, the four write
enables -- and each cell is an `enReg` over its own enable. -/

theorem out_mem {clk we dat crn : List Bool} {addr : List (BitVec 2)} {{w : Wires W}}
    (hw : Wf (drv clk we addr dat crn) w) :
    packMemOut (w .pk_q0) (w .pk_q1) (w .pk_q2) (w .pk_q3) <+: memOut clk we addr dat crn := by
  have ha0 : w .a0F_in <+: bitsA 0 addr := hw .a0F_in
  have ha1 : w .a1F_in <+: bitsA 1 addr := hw .a1F_in
  have hn0 : w .na0F_in <+: gate1Out not (bitsA 0 addr) :=
    (hw .na0F_in).trans (gate1Out_mono _ ((hw .na0_a).trans ha0))
  have hn1 : w .na1F_in <+: gate1Out not (bitsA 1 addr) :=
    (hw .na1F_in).trans (gate1Out_mono _ ((hw .na1_a).trans ha1))
  have hd0 : gateOut and2 (w .dec0_a) (w .dec0_b) <+: W_dec 0 addr :=
    gateOut_mono _ ((hw .dec0_a).trans hn0) ((hw .dec0_b).trans hn1)
  have he0 : gateOut and2 (w .en0_a) (w .en0_b) <+: W_en 0 we addr :=
    gateOut_mono _ (hw .en0_a) ((hw .en0_b).trans hd0)
  have hd1 : gateOut and2 (w .dec1_a) (w .dec1_b) <+: W_dec 1 addr :=
    gateOut_mono _ ((hw .dec1_a).trans ha0) ((hw .dec1_b).trans hn1)
  have he1 : gateOut and2 (w .en1_a) (w .en1_b) <+: W_en 1 we addr :=
    gateOut_mono _ (hw .en1_a) ((hw .en1_b).trans hd1)
  have hd2 : gateOut and2 (w .dec2_a) (w .dec2_b) <+: W_dec 2 addr :=
    gateOut_mono _ ((hw .dec2_a).trans hn0) ((hw .dec2_b).trans ha1)
  have he2 : gateOut and2 (w .en2_a) (w .en2_b) <+: W_en 2 we addr :=
    gateOut_mono _ (hw .en2_a) ((hw .en2_b).trans hd2)
  have hd3 : gateOut and2 (w .dec3_a) (w .dec3_b) <+: W_dec 3 addr :=
    gateOut_mono _ ((hw .dec3_a).trans ha0) ((hw .dec3_b).trans ha1)
  have he3 : gateOut and2 (w .en3_a) (w .en3_b) <+: W_en 3 we addr :=
    gateOut_mono _ (hw .en3_a) ((hw .en3_b).trans hd3)
  refine packMemOut_prefix ?_ ?_ ?_ ?_
  · exact (hw .pk_q0).trans (enOut_mono (hw .c0_clk) ((hw .c0_en).trans he0)
      (hw .c0_data) (hw .c0_clrn))
  · exact (hw .pk_q1).trans (enOut_mono (hw .c1_clk) ((hw .c1_en).trans he1)
      (hw .c1_data) (hw .c1_clrn))
  · exact (hw .pk_q2).trans (enOut_mono (hw .c2_clk) ((hw .c2_en).trans he2)
      (hw .c2_data) (hw .c2_clrn))
  · exact (hw .pk_q3).trans (enOut_mono (hw .c3_clk) ((hw .c3_en).trans he3)
      (hw .c3_data) (hw .c3_clrn))

/-! ### One tactic for every connection -/

/-- Each of the packer's four inputs either stands or advances; one `⊏` is in scope. -/
syntax "mem_pre" : tactic
/-- Every wire of `mid` is the wire of `i`: what an input rule changes is an input. -/
syntax "mem_same" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| mem_pre) => `(tactic| first | exact List.prefix_rfl | exact (‹_ ⊏ _›).isPrefix)
  | `(tactic| mem_same) =>
      `(tactic| (intro j; cases j <;> dsimp only [wires] <;> exact List.prefix_rfl))

syntax "mem_case" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| mem_case) => `(tactic| (
      obtain ⟨⟨en2_a, en2_b⟩, ⟨en3_a, en3_b⟩, ⟨pk_q0, pk_q1, pk_q2, pk_q3⟩, ⟨dec3_a, dec3_b⟩, ⟨c2_clk, c2_en, c2_data, c2_clrn⟩, ⟨c3_clk, c3_en, c3_data, c3_clrn⟩, a0F_in, crF_in, na0F_in, a1F_in, dataF_in, weF_in, na1_a, ⟨en0_a, en0_b⟩, ⟨c0_clk, c0_en, c0_data, c0_clrn⟩, unpA_a, ⟨en1_a, en1_b⟩, na0_a, ⟨dec0_a, dec0_b⟩, clkF_in, ⟨dec2_a, dec2_b⟩, ⟨dec1_a, dec1_b⟩, na1F_in, ⟨c1_clk, c1_en, c1_data, c1_clrn⟩⟩ := i
      obtain ⟨⟨_, _⟩, ⟨_, _⟩, ⟨_, _, _, _⟩, ⟨_, _⟩, ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, _, _, _, _, _, _, _, ⟨_, _⟩, ⟨_, _, _, _⟩, _, ⟨_, _⟩, _, ⟨_, _⟩, _, ⟨_, _⟩, ⟨_, _⟩, _, ⟨_, _, _, _⟩⟩ := mid
      have Hr := Hrule.1 rfl; clear Hrule
      obtain ⟨⟨⟨_, _⟩, ⟨_, _⟩, ⟨_, _, _, _⟩, ⟨_, _⟩, ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, _, _, _, _, _, _, _, ⟨_, _⟩, ⟨_, _, _, _⟩, _, ⟨_, _⟩, _, ⟨_, _⟩, _, ⟨_, _⟩, ⟨_, _⟩, _, ⟨_, _, _, _⟩⟩, out, Hr⟩ := Hr
      simp only [Prod.mk.injEq, and_assoc] at Hr
      repeat' (obtain ⟨hh, Hr⟩ := Hr; try subst hh)
      obtain ⟨hw, e0, e1, e2, e3, e4, h5⟩ := H
      refine ⟨s, existSR_reflexive, Wf_step_of hw drv_mono ?_ ?_, e0, e1, e2, e3, e4, ?_⟩
      · intro j
        cases j <;> dsimp only [wires] <;> mem_pre
      · intro j
        have hj := hw j
        cases j <;> (try dsimp only [wires, drv] at hj) <;> dsimp only [wires, drv] <;>
          first
            | exact hj
            | exact List.prefix_rfl
            | exact e0 ▸ List.prefix_rfl
            | exact e1 ▸ List.prefix_rfl
            | exact e2 ▸ List.prefix_rfl
            | exact e3 ▸ List.prefix_rfl
            | exact e4 ▸ List.prefix_rfl
            | assumption
      · dsimp only [wires] at h5 ⊢
        exact h5.trans (packMemOut_mono (by mem_pre) (by mem_pre) (by mem_pre) (by mem_pre))))

theorem memNetlist_internals_eq : memNetlist.internals =
    [memNetlist.internals.getD 0 (fun _ _ => False), memNetlist.internals.getD 1 (fun _ _ => False), memNetlist.internals.getD 2 (fun _ _ => False),
     memNetlist.internals.getD 3 (fun _ _ => False), memNetlist.internals.getD 4 (fun _ _ => False), memNetlist.internals.getD 5 (fun _ _ => False),
     memNetlist.internals.getD 6 (fun _ _ => False), memNetlist.internals.getD 7 (fun _ _ => False), memNetlist.internals.getD 8 (fun _ _ => False),
     memNetlist.internals.getD 9 (fun _ _ => False), memNetlist.internals.getD 10 (fun _ _ => False), memNetlist.internals.getD 11 (fun _ _ => False),
     memNetlist.internals.getD 12 (fun _ _ => False), memNetlist.internals.getD 13 (fun _ _ => False), memNetlist.internals.getD 14 (fun _ _ => False),
     memNetlist.internals.getD 15 (fun _ _ => False), memNetlist.internals.getD 16 (fun _ _ => False), memNetlist.internals.getD 17 (fun _ _ => False),
     memNetlist.internals.getD 18 (fun _ _ => False), memNetlist.internals.getD 19 (fun _ _ => False), memNetlist.internals.getD 20 (fun _ _ => False),
     memNetlist.internals.getD 21 (fun _ _ => False), memNetlist.internals.getD 22 (fun _ _ => False), memNetlist.internals.getD 23 (fun _ _ => False),
     memNetlist.internals.getD 24 (fun _ _ => False), memNetlist.internals.getD 25 (fun _ _ => False), memNetlist.internals.getD 26 (fun _ _ => False),
     memNetlist.internals.getD 27 (fun _ _ => False), memNetlist.internals.getD 28 (fun _ _ => False), memNetlist.internals.getD 29 (fun _ _ => False),
     memNetlist.internals.getD 30 (fun _ _ => False), memNetlist.internals.getD 31 (fun _ _ => False), memNetlist.internals.getD 32 (fun _ _ => False),
     memNetlist.internals.getD 33 (fun _ _ => False), memNetlist.internals.getD 34 (fun _ _ => False), memNetlist.internals.getD 35 (fun _ _ => False),
     memNetlist.internals.getD 36 (fun _ _ => False), memNetlist.internals.getD 37 (fun _ _ => False), memNetlist.internals.getD 38 (fun _ _ => False),
     memNetlist.internals.getD 39 (fun _ _ => False), memNetlist.internals.getD 40 (fun _ _ => False), memNetlist.internals.getD 41 (fun _ _ => False)] := rfl

/-! ### The specification's own rules -/

section SpecRules
variable (sp : List Bool × List Bool × List (BitVec 2) × List Bool × List Bool × List (BitVec 2 → Bool))

theorem spec_in_clk (v : List Bool) (h : sp.1 ⊏ v) :
    (memSpec.inputs.getIO ↑"clk").2 sp v (v, sp.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem spec_in_we (v : List Bool) (h : sp.2.1 ⊏ v) :
    (memSpec.inputs.getIO ↑"we").2 sp v (sp.1, v, sp.2.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem spec_in_addr (v : List (BitVec 2)) (h : sp.2.2.1 ⊏ v) :
    (memSpec.inputs.getIO ↑"addr").2 sp v (sp.1, sp.2.1, v, sp.2.2.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem spec_in_data (v : List Bool) (h : sp.2.2.2.1 ⊏ v) :
    (memSpec.inputs.getIO ↑"data").2 sp v (sp.1, sp.2.1, sp.2.2.1, v, sp.2.2.2.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem spec_in_clrn (v : List Bool) (h : sp.2.2.2.2.1 ⊏ v) :
    (memSpec.inputs.getIO ↑"clrn").2 sp v (sp.1, sp.2.1, sp.2.2.1, sp.2.2.2.1, v, sp.2.2.2.2.2) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h, rfl⟩

theorem spec_out_mem (v : List (BitVec 2 → Bool)) (h1 : sp.2.2.2.2.2 <+: v)
    (h2 : v <+: memOut sp.1 sp.2.1 sp.2.2.1 sp.2.2.2.1 sp.2.2.2.2.1) :
    (memSpec.outputs.getIO ↑"mem").2 sp v
      (sp.1, sp.2.1, sp.2.2.1, sp.2.2.2.1, sp.2.2.2.2.1, v) := by
  rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])]; exact ⟨h1, h2, rfl⟩
end SpecRules

/-! ### The refinement -/

set_option maxHeartbeats 1000000 in
theorem refines_ψ : memNetlist ⊑_{ψ} memSpec := by
  intro i s H
  constructor
  · intro ident mid_i v Hrule
    obtain ⟨⟨en2_a, en2_b⟩, ⟨en3_a, en3_b⟩, ⟨pk_q0, pk_q1, pk_q2, pk_q3⟩, ⟨dec3_a, dec3_b⟩, ⟨c2_clk, c2_en, c2_data, c2_clrn⟩, ⟨c3_clk, c3_en, c3_data, c3_clrn⟩, a0F_in, crF_in, na0F_in, a1F_in, dataF_in, weF_in, na1_a, ⟨en0_a, en0_b⟩, ⟨c0_clk, c0_en, c0_data, c0_clrn⟩, unpA_a, ⟨en1_a, en1_b⟩, na0_a, ⟨dec0_a, dec0_b⟩, clkF_in, ⟨dec2_a, dec2_b⟩, ⟨dec1_a, dec1_b⟩, na1F_in, ⟨c1_clk, c1_en, c1_data, c1_clrn⟩⟩ := i
    obtain ⟨⟨_, _⟩, ⟨_, _⟩, ⟨_, _, _, _⟩, ⟨_, _⟩, ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, _, _, _, _, _, _, _, ⟨_, _⟩, ⟨_, _, _, _⟩, _, ⟨_, _⟩, _, ⟨_, _⟩, _, ⟨_, _⟩, ⟨_, _⟩, _, ⟨_, _, _, _⟩⟩ := mid_i
    obtain ⟨hw, e0, e1, e2, e3, e4, h5⟩ := H
    case_transition Hcontains : Module.inputs memNetlist, ident,
      (PortMap.getIO_not_contained_false' Hrule)
    dsimp only [memNetlist] at Hcontains
    simp at Hcontains
    rcases Hcontains with h | h | h | h | h <;> subst h <;>
      rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule <;>
      dsimp only at Hrule <;>
      simp only [Prod.mk.injEq, and_assoc] at Hrule <;>
      obtain ⟨hpre, Hrule⟩ := Hrule <;>
      repeat' (obtain ⟨hh, Hrule⟩ := Hrule; try subst hh)
    all_goals simp only [eq_mp_eq_cast] at hpre
    all_goals dsimp only [wires] at h5
    -- The port's identity is decided by `hpre`'s type; the five proofs are one shape.
    -- Two of the three pieces are carried across *pointwise*, and both have to be.  `Wf_congr`
    -- compares the two assignments wire by wire rather than as whole functions, and the
    -- `packMemOut_mono` transports the packer's clause argument by argument rather than as a
    -- whole application.  Handing either one over bare -- `Wf_drv hw …` for the first, `h5` for
    -- the second -- leaves the kernel to unfold `wires` over two forty-seven-component tuples,
    -- or `packMemOut` and the nested `min`s in its length, and it never comes back.
    all_goals first
      | exact ⟨_, _, spec_in_clk s _ (by rw [← e0]; exact hpre), existSR_reflexive,
          Wf_congr drv_mono (Wf_drv hw (drv_env (e0 ▸ hpre.isPrefix) List.prefix_rfl List.prefix_rfl
            List.prefix_rfl List.prefix_rfl _)) (by mem_same) (by mem_same), rfl, e1, e2, e3, e4,
          h5.trans (packMemOut_mono List.prefix_rfl List.prefix_rfl List.prefix_rfl
            List.prefix_rfl)⟩
      | exact ⟨_, _, spec_in_we s _ (by rw [← e1]; exact hpre), existSR_reflexive,
          Wf_congr drv_mono (Wf_drv hw (drv_env List.prefix_rfl (e1 ▸ hpre.isPrefix) List.prefix_rfl
            List.prefix_rfl List.prefix_rfl _)) (by mem_same) (by mem_same), e0, rfl, e2, e3, e4,
          h5.trans (packMemOut_mono List.prefix_rfl List.prefix_rfl List.prefix_rfl
            List.prefix_rfl)⟩
      | exact ⟨_, _, spec_in_addr s _ (by rw [← e2]; exact hpre), existSR_reflexive,
          Wf_congr drv_mono (Wf_drv hw (drv_env List.prefix_rfl List.prefix_rfl (e2 ▸ hpre.isPrefix)
            List.prefix_rfl List.prefix_rfl _)) (by mem_same) (by mem_same), e0, e1, rfl, e3, e4,
          h5.trans (packMemOut_mono List.prefix_rfl List.prefix_rfl List.prefix_rfl
            List.prefix_rfl)⟩
      | exact ⟨_, _, spec_in_data s _ (by rw [← e3]; exact hpre), existSR_reflexive,
          Wf_congr drv_mono (Wf_drv hw (drv_env List.prefix_rfl List.prefix_rfl List.prefix_rfl
            (e3 ▸ hpre.isPrefix) List.prefix_rfl _)) (by mem_same) (by mem_same), e0, e1, e2, rfl, e4,
          h5.trans (packMemOut_mono List.prefix_rfl List.prefix_rfl List.prefix_rfl
            List.prefix_rfl)⟩
      | exact ⟨_, _, spec_in_clrn s _ (by rw [← e4]; exact hpre), existSR_reflexive,
          Wf_congr drv_mono (Wf_drv hw (drv_env List.prefix_rfl List.prefix_rfl List.prefix_rfl
            List.prefix_rfl (e4 ▸ hpre.isPrefix) _)) (by mem_same) (by mem_same), e0, e1, e2, e3, rfl,
          h5.trans (packMemOut_mono List.prefix_rfl List.prefix_rfl List.prefix_rfl
            List.prefix_rfl)⟩
  · intro ident mid_i v Hrule
    obtain ⟨⟨en2_a, en2_b⟩, ⟨en3_a, en3_b⟩, ⟨pk_q0, pk_q1, pk_q2, pk_q3⟩, ⟨dec3_a, dec3_b⟩, ⟨c2_clk, c2_en, c2_data, c2_clrn⟩, ⟨c3_clk, c3_en, c3_data, c3_clrn⟩, a0F_in, crF_in, na0F_in, a1F_in, dataF_in, weF_in, na1_a, ⟨en0_a, en0_b⟩, ⟨c0_clk, c0_en, c0_data, c0_clrn⟩, unpA_a, ⟨en1_a, en1_b⟩, na0_a, ⟨dec0_a, dec0_b⟩, clkF_in, ⟨dec2_a, dec2_b⟩, ⟨dec1_a, dec1_b⟩, na1F_in, ⟨c1_clk, c1_en, c1_data, c1_clrn⟩⟩ := i
    obtain ⟨⟨_, _⟩, ⟨_, _⟩, ⟨_, _, _, _⟩, ⟨_, _⟩, ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, _, _, _, _, _, _, _, ⟨_, _⟩, ⟨_, _, _, _⟩, _, ⟨_, _⟩, _, ⟨_, _⟩, _, ⟨_, _⟩, ⟨_, _⟩, _, ⟨_, _, _, _⟩⟩ := mid_i
    obtain ⟨hw, e0, e1, e2, e3, e4, h5⟩ := H
    have ho := out_mem hw
    dsimp only [wires] at ho h5
    case_transition Hcontains : Module.outputs memNetlist, ident,
      (PortMap.getIO_not_contained_false' Hrule)
    dsimp only [memNetlist] at Hcontains
    simp at Hcontains
    subst Hcontains
    rw [PortMap.rw_rule_execution (by dsimp [reducePortMapgetIO])] at Hrule
    dsimp only at Hrule
    simp only [Prod.mk.injEq, and_assoc] at Hrule
    repeat' (obtain ⟨hh, Hrule⟩ := Hrule; try subst hh)
    exact ⟨s, _, existSR_reflexive, spec_out_mem s _ h5 ho,
      hw, e0, e1, e2, e3, e4, List.prefix_rfl⟩
  · intro rule mid Hin Hrule
    rw [memNetlist_internals_eq] at Hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at Hin
    rcases Hin with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    all_goals (subst h; mem_case)

theorem refines_initial : Module.refines_initial memNetlist memSpec ψ := by
  intro i hi
  obtain ⟨⟨en2_a, en2_b⟩, ⟨en3_a, en3_b⟩, ⟨pk_q0, pk_q1, pk_q2, pk_q3⟩, ⟨dec3_a, dec3_b⟩, ⟨c2_clk, c2_en, c2_data, c2_clrn⟩, ⟨c3_clk, c3_en, c3_data, c3_clrn⟩, a0F_in, crF_in, na0F_in, a1F_in, dataF_in, weF_in, na1_a, ⟨en0_a, en0_b⟩, ⟨c0_clk, c0_en, c0_data, c0_clrn⟩, unpA_a, ⟨en1_a, en1_b⟩, na0_a, ⟨dec0_a, dec0_b⟩, clkF_in, ⟨dec2_a, dec2_b⟩, ⟨dec1_a, dec1_b⟩, na1F_in, ⟨c1_clk, c1_en, c1_data, c1_clrn⟩⟩ := i
  dsimp only [memNetlist] at hi
  simp only [Prod.mk.injEq, and_assoc] at hi
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hi
  refine ⟨([], [], [], [], [], []), rfl, ?_, rfl, rfl, rfl, rfl, rfl, List.nil_prefix⟩
  intro k; cases k <;> exact List.nil_prefix

/-- **The four cells and the decoder refine the register file.** -/
theorem mem_refines : memNetlist ⊑ memSpec :=
  ⟨inferInstance, ψ, refines_ψ, refines_initial⟩

end Graphiti.AsyncFifo.RegFile
