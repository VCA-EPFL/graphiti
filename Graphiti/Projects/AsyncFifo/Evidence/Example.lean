/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.ProofWriteOnly.DomainsLemmas

/-!
# Executing the asynchronous FIFO

Everything in the model is computable, so we can run the two clock domains on concrete
traces as a sanity check that the specification is not vacuous, and that the timing
hypotheses of the theorem are really needed.  The feedback loop between the two domains is
resolved by iterating the two machines to a fixpoint, exactly as the internal rules of the
Graphiti circuit would.  The FIFO has `2^2 = 4` entries; the data written at instant `t` is
`t` itself, so the values read out tell us at which write edges they were enqueued.
-/

namespace Graphiti.AsyncFifo.Example

/-- Iterate the two domains to a fixpoint of the wire values, and return the `full`, `empty`
and `rdata` streams. -/
def runFifo (n lat stl su : Nat) (wclk winc : List Bool) (wdata : List Nat) (rclk rinc : List Bool)
    (orcw orcr : List (Orc n)) (fuel : Nat) : List Bool × List Bool × List Nat :=
  let rec go (rgray_w wgray_r : List (BitVec (n+1))) (mem_r : List (BitVec n → Nat)) : Nat →
      List Bool × List Bool × List Nat
    | 0 => (wFull lat stl su wclk winc wdata rgray_w orcw, rEmpty lat stl su rclk rinc wgray_r orcr,
            rData lat stl su rclk rinc wgray_r orcr mem_r)
    | k+1 =>
      let wgray_r' := wGray lat stl su wclk winc wdata rgray_w orcw
      let mem_r' := wMem lat stl su wclk winc wdata rgray_w orcw
      let rgray_w' := rGray lat stl su rclk rinc wgray_r' orcr
      go rgray_w' wgray_r' mem_r' k
  go [] [] [] fuel

def wdata : List Nat := List.range 60
def always : List Bool := List.replicate 60 true
def clock (period phase : Nat) : List Bool := (List.range 60).map (fun t => t % period == phase)

/-- The "ideal" oracle: every sampled bit resolves to the new value, never any garbage. -/
def ideal : List (Orc 2) := List.replicate 60 ⟨BitVec.allOnes 3, 0#3⟩
/-- An adversarial oracle: bits resolve to old/new in an alternating pattern and the garbage
value seen from an unsettled first stage is the Gray code of the count 5. -/
def adversarial : List (Orc 2) :=
  (List.range 60).map (fun t => ⟨if t % 2 == 0 then 0b101#3 else 0b010#3, Gray.gray (5#3)⟩)

def check (lat stl su : Nat) (wclk winc rclk : List Bool) (orcw orcr : List (Orc 2)) : List Nat × List Nat :=
  let r := runFifo 2 lat stl su wclk winc wdata rclk always orcw orcr 60
  (enqs wclk winc wdata r.1 60, deqs rclk always r.2.1 r.2.2 60)

/-! ### Scenario 1: ideal synchronisers, fast writer (period 2), slow reader (period 6) -/

def s₁ := check 0 0 0 (clock 2 1) ((List.range 60).map (· < 30)) (clock 6 4) ideal ideal
-- What was read is exactly what was written: the writer fills the four entries, is throttled
-- by `full` until the first read has been synchronised back, writes once more and stops.
#guard s₁.2 <+: s₁.1
#guard s₁.1 = [1, 3, 5, 7, 29]
#guard s₁.2 = [1, 3, 5, 7, 29]

/-! ### Scenario 2: ideal synchronisers, slow writer (period 6), fast reader (period 2) -/

def s₂ := check 0 0 0 (clock 6 4) always (clock 2 1) ideal ideal
-- Even with a fast reader the shallow FIFO reports `full` once (edge 28): the writer only
-- learns about reads two of its own clock edges later.
#guard s₂.2 <+: s₂.1
#guard s₂.1 = [4, 10, 16, 22, 34, 40, 46, 52]
#guard s₂.2 = [4, 10, 16, 22, 34, 40, 46, 52]

/-! ### Scenario 3: wire latency 1, settling time 2, adversarial oracle, clocks of periods 3 and 6

The settling time is shorter than both periods, so `fifo_correct` applies and the FIFO is
still correct whatever the oracle does. -/

def s₃ := check 1 2 0 (clock 3 1) always (clock 6 4) adversarial adversarial
#guard s₃.2 <+: s₃.1
#guard s₃.2.length ≥ 5

/-! ### Scenario 4: the same synchronisers, but the read clock has period 2 ≤ settling time

The specification's assumption `ClockOK 3 rclk` is violated from the second read edge on,
so it promises nothing, and indeed the circuit misbehaves: the second synchroniser stage
samples garbage, `empty` deasserts too early and values are read that were never written. -/

def s₄ := check 1 2 0 (clock 3 1) always (clock 2 1) adversarial adversarial
#guard (s₄.2.isPrefixOf s₄.1) = false

end Graphiti.AsyncFifo.Example
