/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: bthom
-/

import Graphiti.Core.Graph.Module
import Graphiti.Core.Graph.ExprHighElaborator
import Graphiti.Core.Graph.ModuleReduction
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open Batteries (AssocList)

namespace Graphiti.AnalogCircuit

noncomputable section

open Real

/-!

We explore using the Module framework to model analog (continuous-time) circuits.
The key idea: the "token" flowing on wires is a pair of time-domain signals
(voltage, current), and each component's `init_state` encodes its constitutive
relation (Ohm's law, capacitor equation, etc.).

The state of each component is the *complete* time-domain solution at its
terminals.  Transitions are identity (the state doesn't change during I/O).
-/

/-- A time-varying real signal (voltage or current as a function of time). -/
abbrev Signal := ℝ → ℝ

/-- Token carried on a wire: (voltage, current) at a terminal.-/
abbrev WireToken := Signal × Signal

/-- State of a generic 2-terminal component.
    `v₁`, `v₂` are the potentials at terminal 1 and 2;
    `i` is the current flowing from terminal 1 to terminal 2 through the component. -/
structure TwoTermState where
  v₁ : Signal
  v₂ : Signal
  i  : Signal

/-- State of a probe (observation point).
    Records the voltage and current at a single node. -/
structure ProbeState where
  v : Signal
  i : Signal

-- ============================================================================
-- § Component Definitions
-- ============================================================================

/-! ### Port convention

For every 2-terminal component:
- **Output port 0** current *leaves* through this port.
- **Input port 0** current *arrives* through this port.

When `connect'` fuses an output to an input, it forces the voltage and current
carried by the token to match, that's Kirchoff: KVL (voltage equality at a node) and
KCL (current conservation in series) for free. -/

/-- **Voltage source** with constant EMF `E`.
    Constitutive relation: `v₁(t) - v₂(t) = E` for all `t`.
    Terminal 1 = positive terminal, terminal 2 = negative terminal. -/
def vsource (E : ℝ) : NatModule TwoTermState where
  inputs  := [(0, ⟨WireToken, fun s tok s' =>
                  s' = s ∧ tok.1 = s.v₂ ∧ tok.2 = s.i⟩)].toAssocList
  outputs := [(0, ⟨WireToken, fun s tok s' =>
                  s' = s ∧ tok.1 = s.v₁ ∧ tok.2 = s.i⟩)].toAssocList
  init_state := fun s => ∀ t, s.v₁ t - s.v₂ t = E

/-- **Resistor** with resistance `R`.
    Constitutive relation (Ohm's law): `v₁(t) - v₂(t) = R · i(t)`. -/
def resistor (R : ℝ) : NatModule TwoTermState where
  inputs  := [(0, ⟨WireToken, fun s tok s' =>
                  s' = s ∧ tok.1 = s.v₁ ∧ tok.2 = s.i⟩)].toAssocList
  outputs := [(0, ⟨WireToken, fun s tok s' =>
                  s' = s ∧ tok.1 = s.v₂ ∧ tok.2 = s.i⟩)].toAssocList
  init_state := fun s => ∀ t, s.v₁ t - s.v₂ t = R * s.i t

/-- **Capacitor** with capacitance `C`.
    Constitutive relation: `i(t) = C · d(v₁ - v₂)/dt`. -/
def capacitor (C : ℝ) : NatModule TwoTermState where
  inputs  := [(0, ⟨WireToken, fun s tok s' =>
                  s' = s ∧ tok.1 = s.v₁ ∧ tok.2 = s.i⟩)].toAssocList
  outputs := [(0, ⟨WireToken, fun s tok s' =>
                  s' = s ∧ tok.1 = s.v₂ ∧ tok.2 = s.i⟩)].toAssocList
  init_state := fun s =>
    Differentiable ℝ (fun t => s.v₁ t - s.v₂ t)
    ∧ ∀ t, s.i t = C * deriv (fun t => s.v₁ t - s.v₂ t) t

/-- **Probe** — an ideal observation point.
    One input, two outputs (morally a fork).
    Output 0 continues the circuit; output 1 is the observation tap.
    No constitutive relation (transparent to the circuit). -/
def probe : NatModule ProbeState where
  inputs  := [(0, ⟨WireToken, fun s tok s' =>
                  s' = s ∧ tok.1 = s.v ∧ tok.2 = s.i⟩)].toAssocList
  outputs := [(0, ⟨WireToken, fun s tok s' =>
                  s' = s ∧ tok.1 = s.v ∧ tok.2 = s.i⟩),
              (1, ⟨WireToken, fun s tok s' =>
                  s' = s ∧ tok.1 = s.v ∧ tok.2 = s.i⟩)].toAssocList
  init_state := fun _ => True

/-- **Ground** — fixes voltage to zero.  One input port, no output.
    Absorbs current and sets voltage to 0. -/
def ground : NatModule (Signal) where
  inputs  := [(0, ⟨WireToken, fun s tok s' =>
                  s' = s ∧ tok.1 = s ∧ tok.2 = tok.2⟩)].toAssocList
  outputs := ∅
  init_state := fun s => s = fun _ => 0


/-- State of an ideal NMOS transistor.
    `vG`, `vD`, `vS` are the gate, drain, and source potentials;
    `iDS` is the drain-to-source current. Gate current is zero (ideal). -/
structure NMOSState where
  vG  : Signal
  vD  : Signal
  vS  : Signal
  iDS : Signal

/-- **NMOS transistor** (ideal switch model) with threshold voltage `Vth`.
    - Gate high (`vG - vS > Vth`): drain–source is a short (`vD = vS`).
    - Gate low  (`vG - vS ≤ Vth`): drain–source is open (`iDS = 0`).
    Three ports: gate (input 0), drain (input 1), source (output 0). -/
def nmos (Vth : ℝ) : NatModule NMOSState where
  inputs  := [(0, ⟨WireToken, fun s tok s' =>   -- gate: receives (vG, 0)
                  s' = s ∧ tok.1 = s.vG ∧ tok.2 = (fun _ => 0)⟩),
              (1, ⟨WireToken, fun s tok s' =>   -- drain: receives (vD, iDS)
                  s' = s ∧ tok.1 = s.vD ∧ tok.2 = s.iDS⟩)].toAssocList
  outputs := [(0, ⟨WireToken, fun s tok s' =>   -- source: produces (vS, iDS)
                  s' = s ∧ tok.1 = s.vS ∧ tok.2 = s.iDS⟩)].toAssocList
  init_state := fun s =>
    (∀ t, s.vG t - s.vS t > Vth → s.vD t = s.vS t) ∧   -- ON: short
    (∀ t, s.vG t - s.vS t ≤ Vth → s.iDS t = 0)          -- OFF: open

-- ============================================================================
-- § 3. Stringified Components (for graphEnv DSL)
-- ============================================================================

def vsource_sm (E : ℝ) := (vsource E).stringify
def resistor_sm (R : ℝ) := (resistor R).stringify
def capacitor_sm (C : ℝ) := (capacitor C).stringify
def probe_sm := probe.stringify
def nmos_sm (Vth : ℝ) := (nmos Vth).stringify
def ground_sm := ground.stringify

-- ============================================================================
-- § Examples using these components
-- ============================================================================

/-! ### V-R series circuit
-/

/-- The V-R series circuit, described using the graphEnv DOT syntax. -/
def vr_circuit (E R : ℝ) := [graphEnv|
    vs  [type="vsource",  typeImp=$(⟨_, vsource_sm E⟩)];
    res [type="resistor", typeImp=$(⟨_, resistor_sm R⟩)];

    vs  -> res [from="out1", to="in1"];   -- V+ → R+
    res -> vs  [from="out1", to="in1"];   -- R- → V-
  ]

/-! ### V-R-C series circuit with probe
-/

/-- The V-R-C circuit with a probe between R and C, described using graphEnv. -/
def vrc_circuit (E R C : ℝ) := [graphEnv|
    obs [type="io"];   -- observation output (voltage across C)

    vs  [type="vsource",   typeImp=$(⟨_, vsource_sm E⟩)];
    res [type="resistor",  typeImp=$(⟨_, resistor_sm R⟩)];
    prb [type="probe",     typeImp=$(⟨_, probe_sm⟩)];
    cap [type="capacitor", typeImp=$(⟨_, capacitor_sm C⟩)];

    vs  -> res [from="out1", to="in1"];   -- V+ → R+
    res -> prb [from="out1", to="in1"];   -- R- → probe
    prb -> cap [from="out1", to="in1"];   -- probe → C+
    cap -> vs  [from="out1", to="in1"];   -- C- → V-
    prb -> obs [from="out2"];             -- observation tap
  ]

/-! ### NAND gate from NMOS transistors (RTL)

An RTL NAND gate: pull-up resistor to VDD, two NMOS in series to ground.
```
       VDD
        │
       [R]  pull-up
        │
output ─┤
        │
      drain
  A ─ gate  NMOS1
      source
        │
      drain
  B ─ gate  NMOS2
      source
        │
       GND
```
The NMOS is a 3-port component (gate, drain, source).
Input A and B are external IO ports driving the gates.
-/

/-- RTL NAND gate: VDD + pull-up resistor + 2 NMOS transistors in series. -/
def nand_circuit (Vdd R Vth : ℝ) := [graphEnv|
    input_a [type="io"];   -- external input A
    input_b [type="io"];   -- external input B
    obs     [type="io"];   -- observation output

    vdd  [type="vsource",  typeImp=$(⟨_, vsource_sm Vdd⟩)];
    rpull [type="resistor", typeImp=$(⟨_, resistor_sm R⟩)];
    prb  [type="probe",     typeImp=$(⟨_, probe_sm⟩)];
    n1   [type="nmos1",     typeImp=$(⟨_, nmos_sm Vth⟩)];
    n2   [type="nmos2",     typeImp=$(⟨_, nmos_sm Vth⟩)];

    vdd   -> rpull [from="out1", to="in1"];    -- VDD+ → R
    rpull -> prb   [from="out1", to="in1"];    -- R → probe (output node)
    prb   -> n1    [from="out1", to="in2"];    -- probe → NMOS1 drain
    input_a -> n1  [to="in1"];                 -- A → NMOS1 gate
    n1    -> n2    [from="out1", to="in2"];    -- NMOS1 source → NMOS2 drain
    input_b -> n2  [to="in1"];                 -- B → NMOS2 gate
    n2    -> vdd   [from="out1", to="in1"];    -- NMOS2 source → GND (VDD−)
    prb   -> obs   [from="out2"];              -- observation tap
  ]


/-- Lowered ExprLow for the V-R circuit (topology only, independent of E, R). -/
@[drunfold_defs]
def vr_lowered := (vr_circuit 0 0).1.lower_TR |>.get rfl

/-- Component environment for the V-R circuit (depends on E, R). -/
def env_vr (E R : ℝ) := (vr_circuit E R).2

@[drenv] theorem env_vr_vsource (E R : ℝ) :
    Batteries.AssocList.find? "vsource" (env_vr E R) = .some ⟨_, vsource_sm E⟩ := rfl
@[drenv] theorem env_vr_resistor (E R : ℝ) :
    Batteries.AssocList.find? "resistor" (env_vr E R) = .some ⟨_, resistor_sm R⟩ := rfl

-- Type extraction: TODO do a tactic for that
seal env_vr in
def_module vr_module_t (E R: ℝ): Type :=
  [T| vr_lowered, (env_vr 0 0).find? ]
reduction_by
  dsimp [vr_lowered]
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type,
         ExprLow.build_module, ExprLow.build_module', toString]
  simp only [drenv]
  dsimp

seal env_vr in
noncomputable def_module vr_module (E R : ℝ) : StringModule (vr_module_t E R) :=
  [e| vr_lowered, (env_vr E R).find? ]

/-- Lowered ExprLow for the V-R-C circuit. -/
@[drunfold_defs]
def vrc_lowered := (vrc_circuit 0 0 0).1.lower_TR |>.get rfl

/-- Component environment for the V-R-C circuit. -/
def env_vrc (E R C : ℝ) := (vrc_circuit E R C).2

@[drenv] theorem env_vrc_vsource (E R C : ℝ) :
    Batteries.AssocList.find? "vsource" (env_vrc E R C) = .some ⟨_, vsource_sm E⟩ := rfl
@[drenv] theorem env_vrc_resistor (E R C : ℝ) :
    Batteries.AssocList.find? "resistor" (env_vrc E R C) = .some ⟨_, resistor_sm R⟩ := rfl
@[drenv] theorem env_vrc_probe (E R C : ℝ) :
    Batteries.AssocList.find? "probe" (env_vrc E R C) = .some ⟨_, probe_sm⟩ := rfl
@[drenv] theorem env_vrc_capacitor (E R C : ℝ) :
    Batteries.AssocList.find? "capacitor" (env_vrc E R C) = .some ⟨_, capacitor_sm C⟩ := rfl

seal env_vrc in
-- Type extraction: TODO do a tactic for that
def_module vrc_module_t : Type :=
  [T| vrc_lowered, (env_vrc 0 0 0).find? ]
reduction_by
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type,
         ExprLow.build_module, ExprLow.build_module', toString]
  simp only [drenv]
  dsimp


seal env_vrc in
/-- The V-R-C circuit, obtained by lowering the graphEnv definition. -/
noncomputable def_module vrc_module (E R C : ℝ) : StringModule vrc_module_t  :=
  [e| vrc_lowered, (env_vrc E R C).find? ]


/-- Lowered NAND gate topology. -/
def nand_lowered := (nand_circuit 0 0 0).1.lower_TR |>.get rfl

/-- Component environment for the NAND gate. -/
def env_nand (Vdd R Vth : ℝ) := (nand_circuit Vdd R Vth).2



noncomputable def nand_module (Vdd R Vth : ℝ) :=
  [e| nand_lowered, (env_nand Vdd R Vth).find? ]
-- ============================================================================
-- § Equation Derivation
-- ============================================================================

/-- A state of a composed circuit is **physically valid** when `init_state`
    holds (constitutive laws) and every `connect''` internal rule is a fixed
    point (connection constraints are satisfied).

    In the analog model, there are no real transitions — the state IS the
    complete solution.  The Module framework provides *composition*; this
    predicate extracts the *physics*. -/
def analogValid {Ident S : Type _} (m : Module Ident S) (s : S) : Prop :=
  m.init_state s ∧ ∀ rule ∈ m.internals, rule s s

/-! Two examples of equation derivaiton (we can easily solve them in mathlib) -/

theorem vr_from_analogValid (E R : ℝ) (hR : R ≠ 0)
    (s) (h : analogValid (vr_module E R) s) :
    ∀ t, s.2.i t = E / R := by
  obtain ⟨hinit, hint⟩ := h
  -- Unfold constitutive laws and internal rules
  dsimp [vr_module, vsource_sm, resistor_sm, vsource, resistor,
         NatModule.stringify, Module.mapIdent] at *
  obtain ⟨hvs, hres⟩ := hinit
  -- Apply hint to each internal rule; simp resolves the (T = T → …) guard.
  have h1 := hint _ (List.mem_cons_self ..)
  have h2 := hint _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  simp only [forall_const, not_true_eq_false, false_implies, and_true] at h1 h2
  obtain ⟨_, _, h1'⟩ := h1
  obtain ⟨_, _, h2'⟩ := h2
  intro t
  -- Signal equalities from the connection witnesses.
  have hv1_eq : s.1.v₁ t = s.2.v₁ t := by grind
  have hv2_eq : s.2.v₂ t = s.1.v₂ t := by grind
  have hE : R * s.2.i t = E := by
    rw [← hres t, ← hv1_eq, hv2_eq]; linarith [hvs t]
  field_simp [hR]; linarith

theorem vrc_ode_from_analogValid (E R C : ℝ)
    (s) (h : analogValid (vrc_module E R C) s) :
    let V_C := fun t => s.2.2.2.v₁ t - s.2.2.2.v₂ t
    ∀ t, R * C * deriv V_C t + V_C t = E := by
  obtain ⟨hinit, hint⟩ := h
  dsimp [vrc_module, vsource_sm, resistor_sm, capacitor_sm, probe_sm,
         vsource, resistor, capacitor, probe,
         NatModule.stringify, Module.mapIdent] at *
  obtain ⟨hvs, _, hres, _, hcap⟩ := hinit
  -- Four internal rules, one per connection.
  have h1 := hint _ (List.mem_cons_self ..)
  have h2 := hint _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have h3 := hint _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have h4 := hint _ (List.mem_cons_of_mem _
                      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
  simp only [forall_const, not_true_eq_false, false_implies, and_true] at h1 h2 h3 h4
  obtain ⟨_, _, h1'⟩ := h1
  obtain ⟨_, _, h2'⟩ := h2
  obtain ⟨_, _, h3'⟩ := h3
  obtain ⟨_, _, h4'⟩ := h4
  intro t
  set V_C := fun t => s.2.2.2.v₁ t - s.2.2.2.v₂ t with hV_C
  -- Signal equalities at t, derived from the connection witnesses.
  have hv1 : s.1.v₁ t = s.2.2.1.v₁ t := by grind
  have hv2 : s.2.2.1.v₂ t = s.2.1.v t := by grind
  have hv3 : s.2.1.v t = s.2.2.2.v₁ t := by grind
  have hv4 : s.2.2.2.v₂ t = s.1.v₂ t := by grind
  have hi1 : s.2.2.1.i t = s.2.1.i t := by grind
  have hi2 : s.2.1.i t = s.2.2.2.i t := by grind
  have eq_vs := hvs t; have eq_res := hres t; have eq_cap := hcap t
  have hi_series : s.2.2.1.i t = s.2.2.2.i t := by linarith
  have h_sub : R * s.2.2.1.i t = R * (C * deriv V_C t) := by rw [hi_series, eq_cap]
  calc R * C * deriv V_C t + V_C t
      = R * (C * deriv V_C t) + V_C t := by ring
    _ = R * s.2.2.1.i t + V_C t := by rw [h_sub]
    _ = E := by simp only [V_C]; linarith


-- ============================================================================
-- § NAND Gate Correctness
-- ============================================================================

/-! ### NAND gate from the `analogValid` predicate

The NAND correctness theorem: for a physically valid state of the NAND circuit,
- When both inputs are above threshold: the output voltage equals 0 (GND).
- When either input is below threshold: the output voltage equals Vdd.
-/


/-- When both inputs are above threshold at time `t`, the output voltage is 0 (GND).

    Both NMOS transistors are ON → drain=source for each → output is shorted
    to the VDD negative terminal (GND) through the series path. -/
theorem nand_both_high (Vdd R Vth : ℝ) (hR : R ≠ 0)
    (s) (h : analogValid (nand_module Vdd R Vth) s)
    -- Both gates above threshold at time t
    (t : ℝ)
    (hA : s.2.2.1.vG t - s.2.2.1.vS t > Vth)   -- NMOS1 gate high
    (hB : s.1.vG t - s.1.vS t > Vth)             -- NMOS2 gate high
    : s.2.1.v t = s.2.2.2.1.v₂ t                 -- output = GND voltage
    := by
  sorry  -- From analogValid: extract NMOS constitutive laws + KVL.
         -- NMOS1 ON: n1.vD = n1.vS, NMOS2 ON: n2.vD = n2.vS
         -- Connection: output = n1.vD, n1.vS = n2.vD, n2.vS = GND
         -- Chain: output = n1.vD = n1.vS = n2.vD = n2.vS = GND

/-- When input A is below threshold at time `t`, the output voltage equals Vdd.

    NMOS₁ OFF → iDS₁ = 0 → series current = 0 → no voltage drop across R
    → output = VDD. -/
theorem nand_a_low (Vdd R Vth : ℝ)
    (s) (h : analogValid (nand_module Vdd R Vth) s)
    (t : ℝ)
    (hA : s.2.2.1.vG t - s.2.2.1.vS t ≤ Vth)    -- NMOS1 gate low
    : s.2.1.v t = s.2.2.2.1.v₁ t                  -- output = VDD voltage
    := by
  sorry  -- NMOS1 OFF: iDS1 = 0. Series: iDS1 = iDS2 = 0.
         -- No current through R → output = VDD (by Ohm's law: 0 = R·0).

end

end Graphiti.AnalogCircuit
