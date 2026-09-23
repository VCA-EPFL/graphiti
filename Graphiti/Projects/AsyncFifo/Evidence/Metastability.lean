/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.ProofWriteOnly.DffTiming

/-!
# Where the gate level stops: metastability

`DffTiming.lean` proves the flip-flop is an edge-triggered register *when its data is stable
over the setup window* (`RegOut 4 1`, aperture `[e-2, e]`).  This file is about what the same
netlist does when that assumption fails, because that is what a synchroniser is for: the first
stage of a two-flip-flop synchroniser samples a bus from another clock domain, and no
assumption about its edges is available.

The answer is that the netlist **oscillates for ever** (`dff_metastable`).  With a clean clock,
a released clear, and `d` showing a one-instant pulse inside the aperture, the cross-coupled
pair `n5`/`n6` enters its symmetric state and the output alternates at every instant, with no
horizon after which it is the value the edge saw, the value before the aperture, or any other
constant.  This is metastability, exactly as a discrete deterministic model can express it: a
bistable driven into its balance point has no noise to fall off it.

What this is *not* is a claim that the first synchroniser stage is not a netlist.  It is one,
it is the same seven gates as every other flip-flop here, and `PlainSync.lean` builds it and proves
`sync_refines` about it -- an honest, entirely gate-derived description of what the two stages
in series compute.  The claim is narrower and is about the model:

> In a deterministic Boolean model with discrete time, there is no true statement of the form
> "the first stage settles", so `syncNetlist ⊑ SyncStage.syncSpec` is not merely unproved, it is
> false, and `dff_metastable` is the counterexample.

`SyncStage.syncSpec` promises that `stl` instants after an edge the output is a per-bit mixture of
the new and the old bus value.  The netlist's output after an aperture violation is `0101…`
for ever, so there is no `stl` at which it is a mixture of anything, and no oracle stream
reproduces it.

The model, not the circuit, is what is wrong here, and it is wrong in the conservative
direction.  Three things it drops are exactly the three that make a real flip-flop resolve:
the metastable state is a point in a continuum rather than one of finitely many states, so a
real circuit sits *near* it with a residual that grows like `e^{t/τ}`; there is noise, which
leaves the balance point with probability one; and the delays are not all exactly equal, so
the cancellation that sustains `0101…` is not robust.  A real stage resolves after a random
time `T` with `P(T > t) ≈ e^{-t/τ}` -- unbounded, but exponentially unlikely to be long, which
is what an MTBF budget buys.  None of that is expressible as a Boolean refinement, and it is
not special to this netlist: a device that always decided within a bounded time would be a
bounded-time arbiter, which is the thing classically shown not to exist.

So the assumption has to be written down rather than discharged, and `SyncStage.syncSpec` is where
this development writes it: the oracle names which bits of a metastable sample resolve to the
new value and what is observed while the stage settles, and `stl < P` is the settling budget.
Discharging it would mean a probabilistic or continuous argument, outside the framework.  The
*second* stage needs no such treatment: its data is `SyncStage.syncOut`, which is stable from `stl`
instants after an edge, so as long as `stl + 2 < P` it meets the aperture of an ordinary
flip-flop and is part of the register bank, as gates -- which is precisely the textbook reason
for giving the first stage a whole clock period before anything reads it.

The same reading explains the `su = 1` in `RegOut 4 1`: the four data patterns over the
aperture that are constant (`000`, `111`) settle, and among the six that are not, two happen to
settle and four oscillate -- so stability over `[e-2, e]` is not merely sufficient, it is the
weakest hypothesis of that shape that works.
-/

set_option linter.unusedSectionVars false

namespace Graphiti.AsyncFifo.Dff

open Graphiti.AsyncFifo Graphiti.AsyncFifo.Contracts Graphiti.AsyncFifo.Timed

/-! ### One concrete run -/

/-- A clean clock: low until `8`, one pulse three instants wide, low afterwards.  No edge
before `R + 3 = 5`, and `PulseOK 3` holds. -/
def clkM : List Bool :=
  [false, false, false, false, false, false, false, false, true, true, true, false,
   false, false, false, false, false, false, false, false, false, false, false, false]

/-- The clear asserted over `[0, 2)` and released afterwards: `ClearOK 2`. -/
def crnM : List Bool :=
  [false, false, true, true, true, true, true, true, true, true, true, true,
   true, true, true, true, true, true, true, true, true, true, true, true]

/-- Data with a one-instant pulse at `7`, inside the aperture `[6, 8]` of the edge at `8`. -/
def dM : List Bool :=
  [false, false, false, false, false, false, false, true, false, false, false, false,
   false, false, false, false, false, false, false, false, false, false, false, false]

/-- The same data settled before the aperture. -/
def dS : List Bool :=
  [false, false, false, false, false, false, true, true, true, true, true, true,
   true, true, true, true, true, true, true, true, true, true, true, true]

/-! ### The two runs -/

/-- **Metastability.**  With the data glitching inside the aperture, the output alternates at
every instant from the end of the clock-to-q window onwards: it never settles, and in
particular it is neither the value at the edge (`dM.getD 8 = false`) nor the value before the
aperture (`dM.getD 6 = false`) from any instant on. -/
theorem dff_metastable :
    (List.range 13).map (fun k => (dffOut clkM dM crnM).getD (12 + k) false)
      = [true, false, true, false, true, false, true, false, true, false, true, false, true] := by
  rfl

/-- The oscillation is not a truncation artefact: consecutive outputs differ at every instant
in the window shown. -/
theorem dff_metastable_alternates :
    ((List.range 12).all fun k =>
      (dffOut clkM dM crnM).getD (12 + k) false != (dffOut clkM dM crnM).getD (13 + k) false) = true := by
  rfl

/-- **The contrast.**  With the same clock and clear and the data settled before the aperture,
the output is the captured value from `e + 4` on -- what `dffOut_regOut` proves in general. -/
theorem dff_settles :
    (List.range 13).map (fun k => (dffOut clkM dS crnM).getD (12 + k) false)
      = [true, true, true, true, true, true, true, true, true, true, true, true, true] := by
  rfl

/-- The block's horizon for this run. -/
theorem dffLenM : dffLen clkM dM crnM = 24 := rfl

/-! ### How long it lasts: a whole clock period

The run above has one edge, so it leaves open how long the oscillation lasts.  This one has
two, twenty-four instants apart -- a clean clock of period `P = 24`, well within every filter
-- with the data glitching inside the first aperture and held stable for ever afterwards. -/

/-- Two pulses, at `8` and at `32`: `ClockOK 24`, `PulseOK 3`, `ResetOK 5`. -/
def clk2 : List Bool :=
  List.replicate 8 false ++ [true, true, true] ++ List.replicate 21 false ++
    [true, true, true] ++ List.replicate 5 false

def crn2 : List Bool := [false, false] ++ List.replicate 38 true

/-- A one-instant glitch at `7`, inside the aperture of the edge at `8`; stable low afterwards. -/
def d2 : List Bool := List.replicate 7 false ++ [true] ++ List.replicate 32 false

/-- **The metastability lasts a whole clock period.**  From the end of the first clock-to-q
window the output alternates at every instant, right up to the second edge; only that edge,
whose data is stable, restores it, and then with the ordinary clock-to-q latency of four.  So
the output is a value at no instant of `[12, 36)`, an interval of exactly `P = 24`.

This is what makes `stl < P` -- the settling budget of `SyncStage.syncSpec`, and the hypothesis that
makes the `orc.junk` branch of `wstep`'s second stage unreachable -- unsatisfiable at gate
level: whatever period one assumes, the metastable interval is the whole of it, so the second
stage samples the first while it is still oscillating and nothing downstream is constrained. -/
theorem dff_metastable_whole_period :
    ((List.range 23).all fun k =>
      (dffOut clk2 d2 crn2).getD (12 + k) false != (dffOut clk2 d2 crn2).getD (13 + k) false) = true := by
  rfl

/-- ... and the second edge, whose data is stable, captures it correctly four instants later. -/
theorem dff_recovers_at_next_edge :
    (List.range 4).map (fun k => (dffOut clk2 d2 crn2).getD (36 + k) false)
      = [false, false, false, false] := by
  rfl

/-- The two edges are twenty-four apart, so this run satisfies `ClockOK 24`. -/
theorem clk2_edges : ∀ e, e < 40 → riseAt clk2 e = true → e = 8 ∨ e = 32 := by decide

/-! ### The single-edge run -/

/-- The only rising edge of this clock is at instant `8`. -/
theorem riseM : ∀ e, e < 24 → riseAt clkM e = true → e = 8 := by decide

/-- The filters the general theorem asks for do hold of this clock and clear, so the run above
is not excluded by them: what fails is only the stability of the data over the aperture. -/
theorem clkM_filters :
    ClearOK 2 crnM 24 ∧ ResetOK (2 + 3) clkM 24 ∧ PulseOK 3 clkM 24 := by
  refine ⟨⟨by decide, by decide⟩, fun e he hre => by rw [riseM e he hre]; lia, fun e he hre => ?_⟩
  rw [riseM e he hre]
  refine ⟨by lia, fun u h1 h2 => ?_, fun u h1 h2 _ => ?_⟩
  · rcases (by lia : u = 5 ∨ u = 6 ∨ u = 7) with rfl | rfl | rfl <;> rfl
  · rcases (by lia : u = 8 ∨ u = 9 ∨ u = 10) with rfl | rfl | rfl <;> rfl

end Graphiti.AsyncFifo.Dff
