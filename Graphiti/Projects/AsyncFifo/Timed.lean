/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Core.Graph.ModuleLemmas
import Graphiti.Core.Graph.ModuleReduction
import Graphiti.Core.Graph.ExprHighElaborator
import Graphiti.Projects.AsyncFifo.Filtered

/-!
# Timed RTL components (Stage 1 of the gate-level programme)

This file starts the descent from the register-level model of `Domains.lean` towards gates.
Following Kobler's translation pattern, each block is a Graphiti module storing its input
streams; input rules extend a stream strictly; output rules emit a stream related to the stored
inputs (and, see below, extend the stream the block remembers having emitted).  The new
ingredient is *timing*, with contracts chosen so that Kobler's NAND-level flip-flop theorem can
eventually discharge them:

* `CombOut`: a combinational block with propagation delay in `[dmin, dmax]`.  Its output at
  instant `t` is `g` of the inputs at `t - dmax`, but only where the part of the inputs the
  block depends on (`dep`) has been constant over the whole delay window
  `[t - dmax, t - dmin]`.  Elsewhere the output is unconstrained: transients and glitches,
  and nothing at all during the first `dmax` instants, before the logic has seen its inputs
  (the specifications' reset filter `ResetOK R` keeps the clocks away from them).
* `RegOut kq su`: an edge-triggered register with clk-to-q window `kq` and setup `su`.  After
  an edge at `e` whose data was stable over `[e - su - 1, e]`, the output is unconstrained
  for `kq` instants and equals the sampled data from `e + kq` until the next edge.  After a
  violated edge nothing is promised until the next edge.  This is exactly the shape of
  Kobler's filtered perfect flip-flop (delay filter, setup/hold filter), with `kq = 4`,
  `su = 2` for her NAND implementation.
* `BusRegOut kq su`: the same, plus the guarantee needed by a register whose output crosses
  into another clock domain: inside the clk-to-q window every bit is either the new bit or
  the bit the register showed at the edge (no glitches).  Hers does not state this clause
  yet; it is the one strengthening her theorem needs.
* `MemOut kq su`: a register file, one such window per written entry, other entries untouched,
  and nothing promised once a write has violated its setup window.
* `syncOut lat su stl`: the metastable first synchroniser stage, deterministic given the oracle
  stream: a sample is a per-bit mixture of the input at the edge and `su + 1` instants before,
  and the output is the oracle's junk for `stl` instants after the edge.  The resolution
  time `stl` is an assumption, not a theorem: the boolean unit-delay NAND model oscillates
  forever in the metastable case.

Blocks with a nondeterministic output remember the stream they emitted and only ever extend
it: an output is a single physical history, and a later emission may not change the past
even at instants where the contract says nothing.  (The consumer's strict-prefix input rule
would reject such a change anyway; remembering makes the block refine a specification that
remembers too.)  Every contract bounds the emitted stream by the horizon of the block's
inputs, so that the timed domain never claims more than the register-level one.  A netlist of
unit-delay gates computes further ahead than that -- each level of logic knows its output one
instant past its inputs, which is what lets a stream go round a loop -- so a gate-level block
reports only the part of what it computes that its inputs justify (`Gates.cut3`).

Nondeterminism that the specification must be able to follow (the synchroniser) is driven by
the oracle; nondeterminism the specification never observes (transients, contents inside a
window or after a setup violation) is left as a relation.
-/

namespace Graphiti.AsyncFifo.Timed

/-! ### Stability, edges, and the component relations -/

/-- `x` is constant on the instants `a ≤ u ≤ b`, all of which are known. -/
def StableOn {κ : Type} (x : Nat → κ) (len a b : Nat) : Prop :=
  b < len ∧ ∀ u, a ≤ u → u ≤ b → x u = x b

/-- Output relation of a combinational block with delay window `[dmin, dmax]`, computing `g`
of the dependency cone `dep` of its inputs (`len` = number of known input instants). -/
def CombOut {κ ο : Type} [Inhabited ο] (dep : Nat → κ) (g : κ → ο) (len dmin dmax : Nat)
    (v : List ο) : Prop :=
  v.length ≤ len ∧
  ∀ t, dmax ≤ t → t < v.length → StableOn dep len (t - dmax) (t - dmin) →
    v.getD t default = g (dep (t - dmax))

/-- What an edge-triggered register promises at *one* instant: low until the first edge, and
the data the last settled edge saw once the clk-to-q window has passed. -/
def RegAt {β : Type} [Inhabited β] (kq su : Nat) (init : β) (clk : List Bool) (d : Nat → β) (dlen : Nat)
    (q : List β) (t : Nat) : Prop :=
  (NoEdge clk t → q.getD t default = init) ∧
  (∀ e, LastEdge clk e t → StableOn d dlen (e - su - 1) e → e + kq ≤ t → q.getD t default = d e)

/-- Output relation of an edge-triggered register with clk-to-q window `kq`, setup `su` and
initial value `init`. -/
def RegOut {β : Type} [Inhabited β] (kq su : Nat) (init : β) (clk : List Bool) (d : Nat → β) (dlen : Nat)
    (q : List β) : Prop :=
  q.length ≤ min clk.length dlen + 1 ∧ ∀ t, t < q.length → RegAt kq su init clk d dlen q t

/-- Every edge before `t` presented its data stable over the setup window.  This is to a
register what `CleanWrites` is to a register file, and a netlist needs it for the same reason:
an edge whose data moved may leave the circuit unsettled, and it will still be unsettled now.
The register's *value* clause does not need it --- a violated edge is forgotten at the next
clean one --- but the glitch-free clause does, because that one is about the circuit being
settled when the edge arrives. -/
def CleanEdges {β : Type} (clk : List Bool) (d : Nat → β) (dlen su t : Nat) : Prop :=
  ∀ e, e < t → riseAt clk e = true → StableOn d dlen (e - su - 1) e

/-- The glitch-free clause at one instant: inside the clk-to-q window every bit is the new bit
or the bit shown at the edge. -/
def BusWinAt {w : Nat} (kq su : Nat) (clk : List Bool) (d : Nat → BitVec w) (dlen : Nat)
    (q : List (BitVec w)) (t : Nat) : Prop :=
  CleanEdges clk d dlen su t → ∀ e, LastEdge clk e t → t < e + kq →
    ∀ i, (q.getD t 0#w).getLsbD i = (d e).getLsbD i ∨ (q.getD t 0#w).getLsbD i = (q.getD e 0#w).getLsbD i

/-- A register whose output crosses into another clock domain: additionally, inside the
clk-to-q window every bit is the new bit or the bit shown at the edge. -/
def BusRegOut {w : Nat} (kq su : Nat) (clk : List Bool) (d : Nat → BitVec w) (dlen : Nat)
    (q : List (BitVec w)) : Prop :=
  RegOut kq su 0#w clk d dlen q ∧ ∀ t, t < q.length → BusWinAt kq su clk d dlen q t

/-- Output relation of an asynchronous memory **read port** with delay window `[dmin, dmax]`.

A read port is combinational, but not over a bus: it does not depend on the whole array.  What
it needs held over its window is the address, and the *word that address selects* --- a write to
any other entry is invisible to it, which is the point of having a memory rather than a
register.  `CombOut` over the array would demand the whole memory stand still. -/
def ReadOut {α : Type} [Inhabited α] {ι : Type} (dmin dmax : Nat) (addr : Nat → ι)
    (mem : Nat → ι → α) (len : Nat) (v : List α) : Prop :=
  v.length ≤ len ∧
  ∀ t, dmax ≤ t → t < v.length → StableOn addr len (t - dmax) (t - dmin) →
    (∀ u, t - dmax ≤ u → u ≤ t - dmin → mem u (addr (t - dmin)) = mem (t - dmin) (addr (t - dmin))) →
    v.getD t default = mem (t - dmin) (addr (t - dmin))

/-- Write event to entry `a` at edge `e`: an edge with write enable and this address, both
stable over the setup window. -/
def WriteEdge {ι α : Type} (a : ι) (clk : List Bool) (we : Nat → Bool) (addr : Nat → ι) (data : Nat → α)
    (dlen su e : Nat) : Prop :=
  riseAt clk e = true ∧ StableOn we dlen (e - su - 1) e ∧ StableOn addr dlen (e - su - 1) e ∧
  StableOn data dlen (e - su - 1) e ∧ we e = true ∧ addr e = a

/-- Every edge before `t` was clean for the register file: the write enable was stable over its
setup window, and so were the address and data when it was writing. -/
def CleanWrites {ι α : Type} (clk : List Bool) (we : Nat → Bool) (addr : Nat → ι) (data : Nat → α)
    (dlen su t : Nat) : Prop :=
  ∀ e, e < t → riseAt clk e = true → StableOn we dlen (e - su - 1) e ∧
    (we e = true → StableOn addr dlen (e - su - 1) e ∧ StableOn data dlen (e - su - 1) e)

/-- Output relation of a register file with clk-to-q window `kq`.  As long as every edge so far
was clean (`CleanWrites`), each entry shows its last written data from `kq` instants after the
writing edge, is unconstrained inside that window, and is untouched by writes to other
entries.  After a violated write nothing is promised: a glitching write enable or address may
corrupt any entry. -/
def MemAt {ι α : Type} [DecidableEq ι] [Inhabited α] (kq su : Nat) (clk : List Bool) (we : Nat → Bool)
    (addr : Nat → ι) (data : Nat → α) (dlen : Nat) (mem : List (ι → α)) (t : Nat) : Prop :=
  CleanWrites clk we addr data dlen su t → ∀ a : ι,
    ((∀ e, e < t → ¬ WriteEdge a clk we addr data dlen su e) → (mem.getD t (fun _ => default)) a = default) ∧
    (∀ e, e < t → WriteEdge a clk we addr data dlen su e →
      (∀ e', e < e' → e' < t → ¬ WriteEdge a clk we addr data dlen su e') → e + kq ≤ t →
      (mem.getD t (fun _ => default)) a = data e)

def MemOut {ι α : Type} [DecidableEq ι] [Inhabited α] (kq su : Nat) (clk : List Bool) (we : Nat → Bool)
    (addr : Nat → ι) (data : Nat → α) (dlen : Nat) (mem : List (ι → α)) : Prop :=
  mem.length ≤ min clk.length dlen + 1 ∧
  ∀ t, t < mem.length → MemAt kq su clk we addr data dlen mem t

/-! ### Monotonicity of the contracts in the block's inputs

A contract established when the block held shorter input streams still holds for longer
ones: every clause only looks at instants before the one it constrains. -/

theorem StableOn.mono {κ : Type} {x x' : Nat → κ} {len len' a b : Nat} (hl : len ≤ len')
    (hx : ∀ u, u < len → x u = x' u) (h : StableOn x len a b) : StableOn x' len' a b := by
  obtain ⟨hb, h⟩ := h
  refine ⟨by lia, fun u hu1 hu2 => ?_⟩
  rw [← hx u (by lia), ← hx b hb]; exact h u hu1 hu2

theorem StableOn.of_mono {κ : Type} {x x' : Nat → κ} {len len' a b : Nat} (hb : b < len)
    (hx : ∀ u, u < len → x u = x' u) (h : StableOn x' len' a b) : StableOn x len a b := by
  obtain ⟨_, h⟩ := h
  refine ⟨hb, fun u hu1 hu2 => ?_⟩
  rw [hx u (by lia), hx b hb]; exact h u hu1 hu2

theorem ReadOut.mono {α : Type} [Inhabited α] {ι : Type} {dmin dmax : Nat} {addr addr' : Nat → ι}
    {mem mem' : Nat → ι → α} {len len' : Nat} {v : List α} (hl : len ≤ len')
    (ha : ∀ u, u < len → addr u = addr' u) (hm : ∀ u, u < len → mem u = mem' u)
    (h : ReadOut dmin dmax addr mem len v) : ReadOut dmin dmax addr' mem' len' v := by
  obtain ⟨hlen, h⟩ := h
  refine ⟨by omega, fun t hdt ht hs hw => ?_⟩
  have hb : t - dmin < len := by omega
  have hs' : StableOn addr len (t - dmax) (t - dmin) := StableOn.of_mono hb ha hs
  rw [h t hdt ht hs' (fun u hu1 hu2 => by
      rw [hm u (by omega), hm (t - dmin) hb, ha (t - dmin) hb]; exact hw u hu1 hu2),
    hm (t - dmin) hb, ha (t - dmin) hb]

theorem CombOut.mono {κ ο : Type} [Inhabited ο] {dep dep' : Nat → κ} {g : κ → ο} {len len' dmin dmax : Nat}
    {v : List ο} (hl : len ≤ len') (hdep : ∀ u, u < len → dep u = dep' u)
    (h : CombOut dep g len dmin dmax v) : CombOut dep' g len' dmin dmax v := by
  obtain ⟨hlen, h⟩ := h
  refine ⟨by lia, fun t hdt ht hs => ?_⟩
  rw [h t hdt ht (hs.of_mono (by lia) hdep), hdep (t - dmax) (by lia)]

theorem RegOut.mono {β : Type} [Inhabited β] {kq su : Nat} {init : β} {clk clk' : List Bool} {d d' : Nat → β}
    {dlen dlen' : Nat} {q : List β} (hc : clk <+: clk') (hd : ∀ u, u < dlen → d u = d' u) (hl : dlen ≤ dlen')
    (h : RegOut kq su init clk d dlen q) : RegOut kq su init clk' d' dlen' q := by
  obtain ⟨hlen, h⟩ := h
  have hcl := hc.length_le
  refine ⟨by omega, fun t ht => ?_⟩
  obtain ⟨h1, h2⟩ := h t ht
  have htc : t ≤ clk.length := by omega
  have htd : t ≤ dlen := by omega
  refine ⟨fun hn => h1 ((NoEdge_congr hc htc).mpr hn), fun e he hs hk => ?_⟩
  have he' := (LastEdge_congr hc htc).mpr he
  have he1 := he.1
  rw [h2 e he' (hs.of_mono (by lia) hd) hk, hd e (by lia)]

theorem BusRegOut.mono {w : Nat} {kq su : Nat} {clk clk' : List Bool} {d d' : Nat → BitVec w}
    {dlen dlen' : Nat} {q : List (BitVec w)} (hc : clk <+: clk') (hd : ∀ u, u < dlen → d u = d' u) (hl : dlen ≤ dlen')
    (h : BusRegOut kq su clk d dlen q) : BusRegOut kq su clk' d' dlen' q := by
  obtain ⟨hreg, hwin⟩ := h
  have hlen := hreg.1
  have hcl := hc.length_le
  refine ⟨hreg.mono hc hd hl, fun t ht hclean e he hk i => ?_⟩
  have htc : t ≤ clk.length := by omega
  have he' := (LastEdge_congr hc htc).mpr he
  have he1 := he.1
  rw [← hd e (by omega)]
  refine hwin t ht (fun e' he2 hr' => ?_) e he' hk i
  exact (hclean e' he2 (by rw [← riseAt_prefix hc (by omega)]; exact hr')).of_mono (by omega) hd

theorem WriteEdge.congr {ι α : Type} {a : ι} {clk clk' : List Bool} {we we' : Nat → Bool} {addr addr' : Nat → ι}
    {data data' : Nat → α} {dlen dlen' su e : Nat} (hc : clk <+: clk') (hl : dlen ≤ dlen')
    (hwe : ∀ u, u < dlen → we u = we' u) (haddr : ∀ u, u < dlen → addr u = addr' u)
    (hdata : ∀ u, u < dlen → data u = data' u) (he : e < dlen) (hec : e < clk.length) :
    WriteEdge a clk we addr data dlen su e ↔ WriteEdge a clk' we' addr' data' dlen' su e := by
  unfold WriteEdge
  rw [riseAt_prefix hc hec, hwe e he, haddr e he]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨h1, h2.mono hl hwe, h3.mono hl haddr, h4.mono hl hdata, h5, h6⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨h1, h2.of_mono he hwe, h3.of_mono he haddr, h4.of_mono he hdata, h5, h6⟩

theorem CleanWrites.of_mono {ι α : Type} {clk clk' : List Bool} {we we' : Nat → Bool} {addr addr' : Nat → ι}
    {data data' : Nat → α} {dlen dlen' su t : Nat} (hc : clk <+: clk') (hwe : ∀ u, u < dlen → we u = we' u)
    (haddr : ∀ u, u < dlen → addr u = addr' u) (hdata : ∀ u, u < dlen → data u = data' u)
    (ht : t ≤ dlen) (htc : t ≤ clk.length) (h : CleanWrites clk' we' addr' data' dlen' su t) :
    CleanWrites clk we addr data dlen su t := by
  intro e he hre
  have hre' : riseAt clk' e = true := by rw [← riseAt_prefix hc (by lia)]; exact hre
  obtain ⟨h1, h2⟩ := h e he hre'
  refine ⟨h1.of_mono (by lia) hwe, fun hw => ?_⟩
  obtain ⟨h3, h4⟩ := h2 (by rw [← hwe e (by lia)]; exact hw)
  exact ⟨h3.of_mono (by lia) haddr, h4.of_mono (by lia) hdata⟩

/-! ### What a netlist of gates can promise

A register built from gates meets its contract only where the clock and the clear behave: the
pulses are wide enough for its internal loops to resolve, the clear has put it in a known state,
and no edge comes before that.  These are filters like the domain's own, and they are applied
the same way -- at each instant, to the history *before* that instant -- so a block is still
right at every instant before a violation, not silently excused from the whole run by one.  The
guarded contracts below are the unguarded ones with the per-instant clause (`RegAt`, `BusWinAt`,
`MemAt`) conditioned on a guard `G`. -/

/-- The filters a netlist of gates needs of its clock and its clear, up to instant `t`. -/
structure GateOK (P pw Rr Rc : Nat) (clk crn : List Bool) (t : Nat) : Prop where
  period : ClockOK P clk t
  pulse : PulseOK pw clk t
  reset : ResetOK Rr clk t
  clear : ClearOK Rc crn t

theorem GateOK.mono {P pw Rr Rc : Nat} {clk crn : List Bool} {t t' : Nat}
    (h : GateOK P pw Rr Rc clk crn t') (ht : t ≤ t') : GateOK P pw Rr Rc clk crn t :=
  ⟨h.period.mono ht, h.pulse.mono ht, h.reset.mono ht, h.clear.mono ht⟩

/-- A guard read off longer streams still holds of the prefixes the block stores. -/
theorem GateOK.congr {P pw Rr Rc : Nat} {clk clk' crn crn' : List Bool} {t : Nat}
    (hc : clk <+: clk') (hr : crn <+: crn') (ht : t ≤ clk.length) (ht' : t ≤ crn.length)
    (h : GateOK P pw Rr Rc clk' crn' t) : GateOK P pw Rr Rc clk crn t :=
  ⟨ClockOK.congr hc ht h.period, PulseOK.congr hc ht h.pulse, ResetOK.congr hc ht h.reset,
   ClearOK.congr hr ht' h.clear⟩

/-- `RegOut`, binding only at the instants where the guard holds, and with the horizon `len`
given explicitly (a netlist reports no further than its clear is known either). -/
def RegOutG {β : Type} [Inhabited β] (kq su : Nat) (init : β) (G : Nat → Prop) (clk : List Bool)
    (d : Nat → β) (dlen len : Nat) (q : List β) : Prop :=
  q.length ≤ len + 1 ∧ ∀ t, t < q.length → G t → RegAt kq su init clk d dlen q t

/-- `BusRegOut`, likewise. -/
def BusRegOutG {w : Nat} (kq su : Nat) (G : Nat → Prop) (clk : List Bool) (d : Nat → BitVec w)
    (dlen len : Nat) (q : List (BitVec w)) : Prop :=
  RegOutG kq su 0#w G clk d dlen len q ∧ ∀ t, t < q.length → G t → BusWinAt kq su clk d dlen q t

/-- `MemOut`, likewise. -/
def MemOutG {ι α : Type} [DecidableEq ι] [Inhabited α] (kq su : Nat) (G : Nat → Prop)
    (clk : List Bool) (we : Nat → Bool) (addr : Nat → ι) (data : Nat → α) (dlen len : Nat)
    (mem : List (ι → α)) : Prop :=
  mem.length ≤ len + 1 ∧ ∀ t, t < mem.length → G t → MemAt kq su clk we addr data dlen mem t

theorem MemOut.mono {ι α : Type} [DecidableEq ι] [Inhabited α] {kq su : Nat} {clk clk' : List Bool}
    {we we' : Nat → Bool} {addr addr' : Nat → ι} {data data' : Nat → α} {dlen dlen' : Nat} {mem : List (ι → α)}
    (hc : clk <+: clk') (hl : dlen ≤ dlen')
    (hwe : ∀ u, u < dlen → we u = we' u) (haddr : ∀ u, u < dlen → addr u = addr' u)
    (hdata : ∀ u, u < dlen → data u = data' u)
    (h : MemOut kq su clk we addr data dlen mem) : MemOut kq su clk' we' addr' data' dlen' mem := by
  obtain ⟨hlen, h⟩ := h
  have hcl := hc.length_le
  refine ⟨by omega, fun t ht hcw a => ?_⟩
  obtain ⟨h1, h2⟩ := h t ht (hcw.of_mono hc hwe haddr hdata (by omega) (by omega)) a
  have hW : ∀ e, e < t → (WriteEdge a clk we addr data dlen su e ↔ WriteEdge a clk' we' addr' data' dlen' su e) :=
    fun e he => WriteEdge.congr hc hl hwe haddr hdata (by omega) (by omega)
  refine ⟨fun hn => h1 (fun e he hw => hn e he ((hW e he).mp hw)), fun e he hw hlast hk => ?_⟩
  rw [h2 e he ((hW e he).mpr hw) (fun e' h1 h2 hw' => hlast e' h1 h2 ((hW e' h2).mp hw')) hk, hdata e (by omega)]

/-! ### Monotonicity of the per-instant clauses and of the guarded contracts -/

theorem RegAt.mono {β : Type} [Inhabited β] {kq su : Nat} {init : β} {clk clk' : List Bool} {d d' : Nat → β}
    {dlen dlen' t : Nat} {q : List β} (hc : clk <+: clk') (hd : ∀ u, u < dlen → d u = d' u)
    (hl : dlen ≤ dlen') (htc : t ≤ clk.length) (htd : t ≤ dlen)
    (h : RegAt kq su init clk d dlen q t) : RegAt kq su init clk' d' dlen' q t := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun hn => h1 ((NoEdge_congr hc htc).mpr hn), fun e he hs hk => ?_⟩
  have he' := (LastEdge_congr hc htc).mpr he
  have he1 := he.1
  rw [h2 e he' (hs.of_mono (by lia) hd) hk, hd e (by lia)]

theorem CleanEdges.of_mono {β : Type} {clk clk' : List Bool} {d d' : Nat → β} {dlen dlen' su t : Nat}
    (hc : clk <+: clk') (hd : ∀ u, u < dlen → d u = d' u) (htc : t ≤ clk.length) (htd : t ≤ dlen)
    (h : CleanEdges clk' d' dlen' su t) : CleanEdges clk d dlen su t := by
  intro e he hr
  exact (h e he (by rw [← riseAt_prefix hc (by omega)]; exact hr)).of_mono (by omega) hd

theorem BusWinAt.mono {w : Nat} {kq su : Nat} {clk clk' : List Bool} {d d' : Nat → BitVec w}
    {dlen dlen' t : Nat} {q : List (BitVec w)} (hc : clk <+: clk') (hd : ∀ u, u < dlen → d u = d' u)
    (hl : dlen ≤ dlen') (htc : t ≤ clk.length) (htd : t ≤ dlen)
    (h : BusWinAt kq su clk d dlen q t) : BusWinAt kq su clk' d' dlen' q t := by
  intro hclean e he hk i
  have he' := (LastEdge_congr hc htc).mpr he
  have he1 := he.1
  rw [← hd e (by lia)]
  exact h (hclean.of_mono hc hd htc htd) e he' hk i

theorem MemAt.mono {ι α : Type} [DecidableEq ι] [Inhabited α] {kq su : Nat} {clk clk' : List Bool}
    {we we' : Nat → Bool} {addr addr' : Nat → ι} {data data' : Nat → α} {dlen dlen' t : Nat}
    {mem : List (ι → α)} (hc : clk <+: clk') (hl : dlen ≤ dlen')
    (hwe : ∀ u, u < dlen → we u = we' u) (haddr : ∀ u, u < dlen → addr u = addr' u)
    (hdata : ∀ u, u < dlen → data u = data' u) (htc : t ≤ clk.length) (htd : t ≤ dlen)
    (h : MemAt kq su clk we addr data dlen mem t) : MemAt kq su clk' we' addr' data' dlen' mem t := by
  intro hcw a
  obtain ⟨h1, h2⟩ := h (hcw.of_mono hc hwe haddr hdata (by omega) (by omega)) a
  have hW : ∀ e, e < t → (WriteEdge a clk we addr data dlen su e ↔ WriteEdge a clk' we' addr' data' dlen' su e) :=
    fun e he => WriteEdge.congr hc hl hwe haddr hdata (by omega) (by omega)
  refine ⟨fun hn => h1 (fun e he hw => hn e he ((hW e he).mp hw)), fun e he hw hlast hk => ?_⟩
  rw [h2 e he ((hW e he).mpr hw) (fun e' k1 k2 hw' => hlast e' k1 k2 ((hW e' k2).mp hw')) hk, hdata e (by omega)]

/-! A per-instant clause looks at the block's report only at the instants it constrains, so two
reports that agree there satisfy it together.  This is what lets a contract proved of the
stream a block computes be read off any prefix of it. -/

theorem RegAt.congr_out {β : Type} [Inhabited β] {kq su : Nat} {init : β} {clk : List Bool}
    {dd : Nat → β} {dlen t : Nat} {q q' : List β} (h : q.getD t default = q'.getD t default)
    (hq : RegAt kq su init clk dd dlen q t) : RegAt kq su init clk dd dlen q' t :=
  ⟨fun hn => by rw [← h]; exact hq.1 hn, fun e he hs hk => by rw [← h]; exact hq.2 e he hs hk⟩

theorem BusWinAt.congr_out {w : Nat} {kq su : Nat} {clk : List Bool} {dd : Nat → BitVec w}
    {dlen t : Nat} {q q' : List (BitVec w)} (h : ∀ u, u ≤ t → q.getD u 0#w = q'.getD u 0#w)
    (hq : BusWinAt kq su clk dd dlen q t) : BusWinAt kq su clk dd dlen q' t := by
  intro hclean e he hk i
  have he1 := he.1
  rw [← h t (Nat.le_refl t), ← h e (by omega)]
  exact hq hclean e he hk i

theorem MemAt.congr_out {ι α : Type} [DecidableEq ι] [Inhabited α] {kq su : Nat} {clk : List Bool}
    {we : Nat → Bool} {addr : Nat → ι} {data : Nat → α} {dlen t : Nat} {mem mem' : List (ι → α)}
    (h : mem.getD t (fun _ => default) = mem'.getD t (fun _ => default))
    (hq : MemAt kq su clk we addr data dlen mem t) :
    MemAt kq su clk we addr data dlen mem' t := by
  intro hcw a
  obtain ⟨h1, h2⟩ := hq hcw a
  rw [← h]
  exact ⟨h1, h2⟩

/-! A longer setup window is a stronger hypothesis on the data, so a contract proved with a
short one implies the same contract with a long one.  That is how blocks with different setup
windows --- the registers' one instant, the register file's eight --- meet in one bank. -/

theorem RegAt.weaken_su {β : Type} [Inhabited β] {kq su su' : Nat} {init : β} {clk : List Bool}
    {dd : Nat → β} {dlen t : Nat} {q : List β} (h : su ≤ su')
    (hq : RegAt kq su init clk dd dlen q t) : RegAt kq su' init clk dd dlen q t :=
  ⟨hq.1, fun e he hs hk => hq.2 e he ⟨hs.1, fun u hu1 hu2 => hs.2 u (by omega) hu2⟩ hk⟩

theorem BusWinAt.weaken_su {w : Nat} {kq su su' : Nat} {clk : List Bool} {dd : Nat → BitVec w}
    {dlen t : Nat} {q : List (BitVec w)} (h : su ≤ su')
    (hq : BusWinAt kq su clk dd dlen q t) : BusWinAt kq su' clk dd dlen q t :=
  fun hclean e he hk i =>
    hq (fun e' he' hr' => (fun hs => ⟨hs.1, fun u hu1 hu2 => hs.2 u (by omega) hu2⟩)
      (hclean e' he' hr')) e he hk i

theorem RegOutG.weaken_su {β : Type} [Inhabited β] {kq su su' : Nat} {init : β} {G : Nat → Prop}
    {clk : List Bool} {dd : Nat → β} {dlen len : Nat} {q : List β} (h : su ≤ su')
    (hq : RegOutG kq su init G clk dd dlen len q) : RegOutG kq su' init G clk dd dlen len q :=
  ⟨hq.1, fun t ht hg => (hq.2 t ht hg).weaken_su h⟩

theorem BusRegOutG.weaken_su {w : Nat} {kq su su' : Nat} {G : Nat → Prop} {clk : List Bool}
    {dd : Nat → BitVec w} {dlen len : Nat} {q : List (BitVec w)} (h : su ≤ su')
    (hq : BusRegOutG kq su G clk dd dlen len q) : BusRegOutG kq su' G clk dd dlen len q :=
  ⟨hq.1.weaken_su h, fun t ht hg => (hq.2 t ht hg).weaken_su h⟩

theorem RegOutG.mono {β : Type} [Inhabited β] {kq su : Nat} {init : β} {G G' : Nat → Prop}
    {clk clk' : List Bool} {d d' : Nat → β} {dlen dlen' len len' : Nat} {q : List β}
    (hc : clk <+: clk') (hd : ∀ u, u < dlen → d u = d' u) (hl : dlen ≤ dlen')
    (hlc : len ≤ clk.length) (hld : len ≤ dlen) (hlen : len ≤ len')
    (hG : ∀ t, t < q.length → G' t → G t)
    (h : RegOutG kq su init G clk d dlen len q) : RegOutG kq su init G' clk' d' dlen' len' q := by
  obtain ⟨hq, h⟩ := h
  exact ⟨by omega, fun t ht hg =>
    (h t ht (hG t ht hg)).mono hc hd hl (by omega) (by omega)⟩

theorem BusRegOutG.mono {w : Nat} {kq su : Nat} {G G' : Nat → Prop} {clk clk' : List Bool}
    {d d' : Nat → BitVec w} {dlen dlen' len len' : Nat} {q : List (BitVec w)}
    (hc : clk <+: clk') (hd : ∀ u, u < dlen → d u = d' u) (hl : dlen ≤ dlen')
    (hlc : len ≤ clk.length) (hld : len ≤ dlen) (hlen : len ≤ len')
    (hG : ∀ t, t < q.length → G' t → G t)
    (h : BusRegOutG kq su G clk d dlen len q) : BusRegOutG kq su G' clk' d' dlen' len' q := by
  obtain ⟨hreg, hwin⟩ := h
  have hq := hreg.1
  exact ⟨hreg.mono hc hd hl hlc hld hlen hG, fun t ht hg =>
    (hwin t ht (hG t ht hg)).mono hc hd hl (by omega) (by omega)⟩

theorem MemOutG.mono {ι α : Type} [DecidableEq ι] [Inhabited α] {kq su : Nat} {G G' : Nat → Prop}
    {clk clk' : List Bool} {we we' : Nat → Bool} {addr addr' : Nat → ι} {data data' : Nat → α}
    {dlen dlen' len len' : Nat} {mem : List (ι → α)}
    (hc : clk <+: clk') (hl : dlen ≤ dlen')
    (hwe : ∀ u, u < dlen → we u = we' u) (haddr : ∀ u, u < dlen → addr u = addr' u)
    (hdata : ∀ u, u < dlen → data u = data' u)
    (hlc : len ≤ clk.length) (hld : len ≤ dlen) (hlen : len ≤ len')
    (hG : ∀ t, t < mem.length → G' t → G t)
    (h : MemOutG kq su G clk we addr data dlen len mem) :
    MemOutG kq su G' clk' we' addr' data' dlen' len' mem := by
  obtain ⟨hq, h⟩ := h
  exact ⟨by omega, fun t ht hg =>
    (h t ht (hG t ht hg)).mono hc hl hwe haddr hdata (by omega) (by omega)⟩

/-! ### The settling contract: the one assumption -/

/-- **What a flip-flop does when its data does *not* meet the setup window.**  This is the one
thing in the development that is assumed rather than derived, and it is deliberately one clause
about one bit.

The first half is `RegOut` --- exactly what a netlist of gates gives, and `Dff.dffOut_regOut`
proves it.  The second half is the assumption: from `stl` instants after an edge until the next
one the output is *a value* --- it does not move, and it is one of the two the data showed at
the ends of the aperture.  Nothing at all is said about the `stl` instants themselves, so a
stage still inside its metastable window may report anything.

`Dff.dffOut_settleOut` proves the netlist satisfies this whenever its data *is* stable over the
aperture, with `stl = kq = 4`.  So what is assumed is exactly the failure of that hypothesis,
for the flip-flops of the first synchroniser stage and nowhere else: everywhere else the setup
window is discharged from the clock period (`TimedProof.edge_value`) and this contract is a
theorem.  `Metastability.lean` says why it cannot be a theorem here. -/
def SettleOut (kq su stl : Nat) (clk : List Bool) (d : Nat → Bool) (dlen : Nat) (q : List Bool) : Prop :=
  RegOut kq su false clk d dlen q ∧
  ∀ t, t < q.length → ∀ e, LastEdge clk e t → e + stl ≤ t →
    q.getD t false = q.getD (e + stl) false ∧
      (q.getD (e + stl) false = d e ∨ q.getD (e + stl) false = d (e - su - 1))

theorem SettleOut.mono {kq su stl : Nat} {clk clk' : List Bool} {d d' : Nat → Bool}
    {dlen dlen' : Nat} {q : List Bool} (hc : clk <+: clk') (hd : ∀ u, u < dlen → d u = d' u)
    (hl : dlen ≤ dlen') (h : SettleOut kq su stl clk d dlen q) :
    SettleOut kq su stl clk' d' dlen' q := by
  obtain ⟨hreg, hset⟩ := h
  have hlen := hreg.1
  have hcl := hc.length_le
  refine ⟨hreg.mono hc hd hl, fun t ht e hle hk => ?_⟩
  have he1 := hle.1
  obtain ⟨h1, h2⟩ := hset t ht e ((LastEdge_congr hc (by omega)).mpr hle) hk
  refine ⟨h1, ?_⟩
  rcases h2 with h2 | h2
  · exact Or.inl (by rw [h2, hd e (by omega)])
  · exact Or.inr (by rw [h2, hd (e - su - 1) (by omega)])

/-- The block a settling flip-flop is: the ports of the netlist, and `SettleOut` as its
contract.  It stores what it has reported so that its reports only grow. -/
structure SettleSt where
  clk : List Bool
  d : List Bool
  crn : List Bool
  q : List Bool

@[drcomponents]
def settlingDff (kq su stl : Nat) : StringModule SettleSt :=
  { inputs := [ (↑"clk", ⟨List Bool, fun s v s' => s.clk ⊏ v ∧ s' = { s with clk := v }⟩)
              , (↑"d", ⟨List Bool, fun s v s' => s.d ⊏ v ∧ s' = { s with d := v }⟩)
              , (↑"clrn", ⟨List Bool, fun s v s' => s.crn ⊏ v ∧ s' = { s with crn := v }⟩)
              ].toAssocList
    outputs := [ (↑"q", ⟨List Bool, fun s v s' => s.q <+: v ∧
                    SettleOut kq su stl s.clk (fun u => s.d.getD u false) s.d.length v ∧
                    s' = { s with q := v }⟩) ].toAssocList
    internals := []
    init_state := fun s => s = ⟨[], [], [], []⟩ }

variable {n : Nat}

/-- State of the metastable synchroniser stage: the value it will settle to, and the number of
instants since its last edge. -/
structure SyncReg (n : Nat) where
  val : BitVec (n+1)
  since : Nat

structure SyncIn (n : Nat) where
  rise : Bool
  dNew : BitVec (n+1)
  dOld : BitVec (n+1)
  orc : Orc n

def syncStep (s : SyncReg n) (i : SyncIn n) : SyncReg n :=
  if i.rise then ⟨mix i.orc.sel i.dNew i.dOld, 0⟩ else ⟨s.val, s.since + 1⟩

/-- Inputs of the stage at instant `t`: the bus is read through a wire of latency `lat`, at
the edge and `su + 1` instants earlier. -/
def syncInp (lat su : Nat) (clk : List Bool) (d : List (BitVec (n+1))) (orc : List (Orc n)) (t : Nat) : SyncIn n :=
  ⟨riseAt clk t, delayed lat d t, delayed lat d (t - su - 1), orc.getD t default⟩

def syncLen (lat : Nat) (clk : List Bool) (d : List (BitVec (n+1))) (orc : List (Orc n)) : Nat :=
  min (min clk.length (d.length + lat)) orc.length

def syncRun (lat su stl : Nat) (clk : List Bool) (d : List (BitVec (n+1))) (orc : List (Orc n)) (t : Nat) : SyncReg n :=
  run syncStep ⟨0#(n+1), stl⟩ (syncInp lat su clk d orc) t

/-- Output of the synchroniser stage: junk while settling, the settled value otherwise.  The
junk at instant `t` is the oracle's, so the output is only known while the oracle is. -/
def syncOut (lat su stl : Nat) (clk : List Bool) (d : List (BitVec (n+1))) (orc : List (Orc n)) : List (BitVec (n+1)) :=
  timeline (fun t => if (syncRun lat su stl clk d orc t).since < stl then (orc.getD t default).junk
                     else (syncRun lat su stl clk d orc t).val)
    (syncLen lat clk d orc)

theorem syncInp_congr {lat su : Nat} {clk clk' : List Bool} {d d' : List (BitVec (n+1))} {orc orc' : List (Orc n)}
    (h₁ : clk <+: clk') (h₂ : d <+: d') (h₃ : orc <+: orc') {t : Nat} (ht : t < syncLen lat clk d orc) :
    syncInp lat su clk d orc t = syncInp lat su clk' d' orc' t := by
  unfold syncLen at ht
  unfold syncInp
  rw [riseAt_prefix h₁ (by omega), delayed_congr h₂ (by omega), delayed_congr h₂ (by omega), h₃.getD_eq_left (by omega)]

theorem syncLen_mono {lat : Nat} {clk clk' : List Bool} {d d' : List (BitVec (n+1))} {orc orc' : List (Orc n)}
    (h₁ : clk <+: clk') (h₂ : d <+: d') (h₃ : orc <+: orc') : syncLen lat clk d orc ≤ syncLen lat clk' d' orc' := by
  have := h₁.length_le; have := h₂.length_le; have := h₃.length_le
  unfold syncLen; omega

theorem syncOut_mono {lat su stl : Nat} {clk clk' : List Bool} {d d' : List (BitVec (n+1))} {orc orc' : List (Orc n)}
    (h₁ : clk <+: clk') (h₂ : d <+: d') (h₃ : orc <+: orc') :
    syncOut lat su stl clk d orc <+: syncOut lat su stl clk' d' orc' := by
  apply timeline_mono (syncLen_mono h₁ h₂ h₃)
  intro t ht
  have hrun : syncRun lat su stl clk d orc t = syncRun lat su stl clk' d' orc' t :=
    run_congr _ _ (fun u hu => syncInp_congr h₁ h₂ h₃ hu) t (Nat.le_of_lt ht)
  unfold syncLen at ht
  rw [hrun, h₃.getD_eq_left (by omega)]

/-! ### The write domain as timed blocks -/

section WriteBlocks

variable (α : Type) [Inhabited α]

/-- The registers of the write domain other than the memory, the Gray pointer register and the
synchroniser: binary pointer, flag, second synchroniser stage. -/
structure WSt (n : Nat) where
  ptr : BitVec (n+1)
  full : Bool
  q2 : BitVec (n+1)

instance : Inhabited (WSt n) := ⟨⟨0#(n+1), false, 0#(n+1)⟩⟩

/-- The next-state logic of the write domain as a pure function: from the state, the write
request, and the current synchroniser output, it produces the next state, the next Gray
pointer (registered separately, so that the bus that crosses clock domains never glitches),
and the memory write command. -/
structure WNext (α : Type) (n : Nat) where
  st : WSt n
  gnext : BitVec (n+1)
  we : Bool
  addr : BitVec n
  data : α

instance : Inhabited (WNext α n) := ⟨⟨default, 0#(n+1), false, 0#n, default⟩⟩

def wNext (st : WSt n) (inc : Bool) (data : α) (q1 : BitVec (n+1)) : WNext α n :=
  let ok := inc && !st.full
  let ptr' := if ok then st.ptr + 1#(n+1) else st.ptr
  { st := { ptr := ptr', full := ptr' == Gray.ungray st.q2 + BitVec.ofNat (n+1) (2 ^ n), q2 := q1 }
    gnext := Gray.gray ptr'
    we := ok
    addr := st.ptr.setWidth n
    data := data }

/-- State of the next-state block: its four input streams and the bus it has emitted. -/
structure NextSt (α : Type) (n : Nat) where
  st : List (WSt n)
  inc : List Bool
  data : List α
  q1 : List (BitVec (n+1))
  d : List (WNext α n)

/-- The dependency cone of the next-state block at instant `u`: all four inputs. -/
def nextDep (s : NextSt α n) (u : Nat) : WSt n × Bool × α × BitVec (n+1) :=
  (s.st.getD u default, s.inc.getD u false, s.data.getD u default, s.q1.getD u 0)

def nextLen (s : NextSt α n) : Nat :=
  min (min s.st.length s.inc.length) (min s.data.length s.q1.length)

def nextFun (x : WSt n × Bool × α × BitVec (n+1)) : WNext α n := wNext α x.1 x.2.1 x.2.2.1 x.2.2.2

/-- Combinational next-state block with delay window `[dmin, dmax]`.  Its single output is the
bus carrying the whole `WNext` record (next state, next Gray pointer, memory write command);
at Stage 2 this block becomes a netlist and the bus its individual wires. -/
@[drcomponents]
def nextBlock (dmin dmax : Nat) : StringModule (NextSt α n) :=
  { inputs := [ (↑"st", ⟨List (WSt n), fun s v s' => s.st ⊏ v ∧ s' = { s with st := v }⟩)
              , (↑"inc", ⟨List Bool, fun s v s' => s.inc ⊏ v ∧ s' = { s with inc := v }⟩)
              , (↑"data", ⟨List α, fun s v s' => s.data ⊏ v ∧ s' = { s with data := v }⟩)
              , (↑"q1", ⟨List (BitVec (n+1)), fun s v s' => s.q1 ⊏ v ∧ s' = { s with q1 := v }⟩)
              ].toAssocList
    outputs := [ (↑"d", ⟨List (WNext α n), fun s v s' => s.d <+: v ∧
                    CombOut (nextDep α s) (nextFun α) (nextLen α s) dmin dmax v ∧ s' = { s with d := v }⟩) ].toAssocList
    internals := []
    init_state := fun s => s = ⟨[], [], [], [], []⟩ }

/-- State of the register bank: the clock, the next-state bus, the clear, and the four emitted
outputs. -/
structure RegSt (α : Type) (n : Nat) where
  clk : List Bool
  d : List (WNext α n)
  crn : List Bool
  st_q : List (WSt n)
  full_q : List Bool
  gray_q : List (BitVec (n+1))
  mem_q : List (BitVec n → α)

/-- How far the bank's inputs are known: its clock, its bus and its clear. -/
def RegSt.horizon (s : RegSt α n) : Nat := min (min s.clk.length s.d.length) s.crn.length

/-- The register bank of the write domain, clocked by `clk`, loaded from the next-state bus
`d`, and cleared by `clrn`.  Each output has its own contract: the state (`RegOut`), the `full`
flag (a projection of the state register), the Gray pointer register that crosses into the
other domain (`BusRegOut`, glitch-free window) and the memory (`MemOut`, one window per written
entry).  Each binds only at the instants where the clock and the clear have behaved
(`GateOK P pw Rr Rc`), because that is all a netlist of gates can promise; the register level
gets the unguarded contracts back by taking the guard to be trivially true. -/
@[drcomponents]
def regBank (kq su P pw Rr Rc : Nat) : StringModule (RegSt α n) :=
  { inputs := [ (↑"clk", ⟨List Bool, fun s v s' => s.clk ⊏ v ∧ s' = { s with clk := v }⟩)
              , (↑"d", ⟨List (WNext α n), fun s v s' => s.d ⊏ v ∧ s' = { s with d := v }⟩)
              , (↑"clrn", ⟨List Bool, fun s v s' => s.crn ⊏ v ∧ s' = { s with crn := v }⟩)
              ].toAssocList
    outputs := [ (↑"st", ⟨List (WSt n), fun s v s' => s.st_q <+: v ∧
                    RegOutG kq su default (GateOK P pw Rr Rc s.clk s.crn) s.clk
                      (fun u => (s.d.getD u default).st) s.d.length s.horizon v ∧
                    s' = { s with st_q := v }⟩)
               , (↑"full", ⟨List Bool, fun s v s' => s.full_q <+: v ∧
                    (∃ q, RegOutG kq su default (GateOK P pw Rr Rc s.clk s.crn) s.clk
                            (fun u => (s.d.getD u default).st) s.d.length s.horizon q ∧
                          v = q.map (fun st => st.full)) ∧
                    s' = { s with full_q := v }⟩)
               , (↑"gray", ⟨List (BitVec (n+1)), fun s v s' => s.gray_q <+: v ∧
                    BusRegOutG kq su (GateOK P pw Rr Rc s.clk s.crn) s.clk
                      (fun u => (s.d.getD u default).gnext) s.d.length s.horizon v ∧
                    s' = { s with gray_q := v }⟩)
               , (↑"mem", ⟨List (BitVec n → α), fun s v s' => s.mem_q <+: v ∧
                    MemOutG kq su (GateOK P pw Rr Rc s.clk s.crn) s.clk
                      (fun u => (s.d.getD u default).we) (fun u => (s.d.getD u default).addr)
                      (fun u => (s.d.getD u default).data) s.d.length s.horizon v ∧
                    s' = { s with mem_q := v }⟩)
               ].toAssocList
    internals := []
    init_state := fun s => s = ⟨[], [], [], [], [], [], []⟩ }

/-- The power-on reset: a source that produces a clear satisfying `ClearOK Rc`.  It is internal
to the write domain, so the domain's interface is the one the register level already had --- a
netlist of gates has no defined state until something puts it there, but nothing outside needs
to know that. -/
@[drcomponents]
def clearSrc (Rc : Nat) : StringModule (List Bool) :=
  { inputs := ∅
    outputs := [ (↑"crn", ⟨List Bool, fun s v s' => s ⊏ v ∧ ClearOK Rc v v.length ∧ s' = v⟩) ].toAssocList
    internals := []
    init_state := fun s => s = [] }

/-- The metastable first synchroniser stage, sampling the other domain's Gray pointer through
a wire of latency `lat`.  Its output is determined by the oracle, and like every other block it
records what it has reported, so that its reports only grow --- which is what lets a netlist
stand in for it (`SyncStage.lean`). -/
@[drcomponents]
def syncReg (lat su stl : Nat) :
    StringModule (List Bool × List (BitVec (n+1)) × List (Orc n) × List (BitVec (n+1))) :=
  { inputs := [ (↑"clk", ⟨List Bool, fun s v s' => s.1 ⊏ v ∧ s' = (v, s.2)⟩)
              , (↑"d", ⟨List (BitVec (n+1)), fun s v s' => s.2.1 ⊏ v ∧ s' = (s.1, v, s.2.2)⟩)
              , (↑"orc", ⟨List (Orc n), fun s v s' => s.2.2.1 ⊏ v ∧
                  s' = (s.1, s.2.1, v, s.2.2.2)⟩)
              ].toAssocList
    outputs := [ (↑"q", ⟨List (BitVec (n+1)), fun s v s' => s.2.2.2 <+: v ∧
                    v <+: syncOut lat su stl s.1 s.2.1 s.2.2.1 ∧
                    s' = (s.1, s.2.1, s.2.2.1, v)⟩) ].toAssocList
    internals := []
    init_state := fun s => s = ([], [], [], []) }

/-- A two-way fork (zero delay) for the clock, as in the report. -/
@[drcomponents]
def fork2 (β : Type) : StringModule (List β) :=
  { inputs := [ (↑"in", ⟨List β, fun s v s' => s ⊏ v ∧ s' = v⟩) ].toAssocList
    outputs := [ (↑"out1", ⟨List β, fun s v s' => s' = s ∧ v = s⟩)
               , (↑"out2", ⟨List β, fun s v s' => s' = s ∧ v = s⟩) ].toAssocList
    internals := []
    init_state := fun s => s = [] }

variable (n lat kq su stl dmin dmax P pw Rr Rc : Nat)

/-- The write domain as timed RTL blocks.  Same interface as `writeDomain`: the clear is
produced inside the domain by `clrS`, so nothing outside has to know the bank needs one. -/
def wdomTimedGraph := [graphEnv|
    clk [type="io"];
    inc [type="io"];
    data [type="io"];
    rgray [type="io"];
    orc [type="io"];
    gray [type="io"];
    full [type="io"];
    mem [type="io"];

    clkF [type="clkF", typeImp=$(⟨_, fork2 Bool⟩)];
    regs [type="regBank", typeImp=$(⟨_, regBank α (n := n) kq su P pw Rr Rc⟩)];
    clrS [type="clearSrc", typeImp=$(⟨_, clearSrc Rc⟩)];
    next [type="nextBlock", typeImp=$(⟨_, nextBlock α (n := n) dmin dmax⟩)];
    sync [type="syncReg", typeImp=$(⟨_, syncReg (n := n) lat su stl⟩)];

    clk -> clkF [to="in"];
    clkF -> regs [from="out1", to="clk"];
    clrS -> regs [from="crn", to="clrn"];
    clkF -> sync [from="out2", to="clk"];
    rgray -> sync [to="d"];
    orc -> sync [to="orc"];
    inc -> next [to="inc"];
    data -> next [to="data"];
    sync -> next [from="q", to="q1"];
    regs -> next [from="st", to="st"];
    next -> regs [from="d", to="d"];

    regs -> gray [from="gray"];
    regs -> full [from="full"];
    regs -> mem [from="mem"];
  ]

@[drunfold_defs]
def wdomTimedLowered := (wdomTimedGraph Unit 0 0 0 0 0 0 0 0 0 0 0).1.lower_TR |>.get rfl

def wenv := (wdomTimedGraph α n lat kq su stl dmin dmax P pw Rr Rc).2

@[drenv] theorem wenv_clkF : (wenv α n lat kq su stl dmin dmax P pw Rr Rc).find? "clkF" = .some ⟨_, fork2 Bool⟩ := rfl
@[drenv] theorem wenv_regs : (wenv α n lat kq su stl dmin dmax P pw Rr Rc).find? "regBank" = .some ⟨_, regBank α (n := n) kq su P pw Rr Rc⟩ := rfl
@[drenv] theorem wenv_clrS : (wenv α n lat kq su stl dmin dmax P pw Rr Rc).find? "clearSrc" = .some ⟨_, clearSrc Rc⟩ := rfl
@[drenv] theorem wenv_next : (wenv α n lat kq su stl dmin dmax P pw Rr Rc).find? "nextBlock" = .some ⟨_, nextBlock α (n := n) dmin dmax⟩ := rfl
@[drenv] theorem wenv_sync : (wenv α n lat kq su stl dmin dmax P pw Rr Rc).find? "syncReg" = .some ⟨_, syncReg (n := n) lat su stl⟩ := rfl

seal wenv in
def_module wdomTimedT' : Type :=
  [T| wdomTimedLowered, (wenv α n lat kq su stl dmin dmax P pw Rr Rc).find? ]
reduction_by
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type,
         ExprLow.build_module, ExprLow.build_module', toString]
  simp only [drenv]
  dsimp

/-- The state of the timed write domain, as produced by lowering the graph: the clear source,
the synchroniser (`clk`, `d`, `orc`), the clock fork, the next-state block and the register
bank. -/
abbrev wdomTimedT : Type :=
  List Bool × (List Bool × List (BitVec (n+1)) × List (Orc n) × List (BitVec (n+1))) ×
    List Bool × NextSt α n × RegSt α n

omit [Inhabited α] in
theorem wdomTimedT_eq : wdomTimedT' α n = wdomTimedT α n := rfl

seal wenv in
def_module wdomTimed : StringModule (wdomTimedT α n) :=
  [e| wdomTimedLowered, (wenv α n lat kq su stl dmin dmax P pw Rr Rc).find? ]

end WriteBlocks

/-! ### The read domain as timed blocks

The same four blocks as the write domain --- a clock fork, a register bank, combinational
next-state logic and the synchroniser --- and one more, the read port: the read data is the
memory word at the read address, and it is combinational, so it is a block with a delay window
like the next-state logic rather than a register.

Two things differ from the write side.  The bank has no memory (the write domain owns it), and
the `empty` flag powers up **high**: a FIFO starts empty.  `RSt`'s `default` therefore has
`empty := true`, which a bank of flip-flops cleared to low cannot show directly --- so the
gate-level bank stores the complement and inverts it on the way out, which costs an inverter and
no ports.  (The alternative is a preset on that one flip-flop, i.e. a second asynchronous input
on the cell; Cummings' design does exactly that.) -/

section ReadBlocks

variable (α : Type) [Inhabited α]

/-- The registers of the read domain that the bank holds. -/
structure RSt (n : Nat) where
  ptr : BitVec (n+1)
  empty : Bool
  q2 : BitVec (n+1)

/-- A FIFO starts empty. -/
instance : Inhabited (RSt n) := ⟨⟨0#(n+1), true, 0#(n+1)⟩⟩

/-- The next-state logic of the read domain: the next state and the next Gray pointer
(registered separately, so the bus that crosses clock domains never glitches). -/
structure RNext (n : Nat) where
  st : RSt n
  gnext : BitVec (n+1)

instance : Inhabited (RNext n) := ⟨⟨default, 0#(n+1)⟩⟩

def rNext (st : RSt n) (inc : Bool) (q1 : BitVec (n+1)) : RNext n :=
  let ok := inc && !st.empty
  let ptr' := if ok then st.ptr + 1#(n+1) else st.ptr
  { st := { ptr := ptr', empty := ptr' == Gray.ungray st.q2, q2 := q1 }
    gnext := Gray.gray ptr' }

/-- State of the read domain's next-state block: its three input streams and the bus it has
emitted. -/
structure RNextSt (n : Nat) where
  st : List (RSt n)
  inc : List Bool
  q1 : List (BitVec (n+1))
  d : List (RNext n)

def rnextDep (s : RNextSt n) (u : Nat) : RSt n × Bool × BitVec (n+1) :=
  (s.st.getD u default, s.inc.getD u false, s.q1.getD u 0)

def rnextLen (s : RNextSt n) : Nat := min (min s.st.length s.inc.length) s.q1.length

def rnextFun (x : RSt n × Bool × BitVec (n+1)) : RNext n := rNext x.1 x.2.1 x.2.2

@[drcomponents]
def rnextBlock (dmin dmax : Nat) : StringModule (RNextSt n) :=
  { inputs := [ (↑"st", ⟨List (RSt n), fun s v s' => s.st ⊏ v ∧ s' = { s with st := v }⟩)
              , (↑"inc", ⟨List Bool, fun s v s' => s.inc ⊏ v ∧ s' = { s with inc := v }⟩)
              , (↑"q1", ⟨List (BitVec (n+1)), fun s v s' => s.q1 ⊏ v ∧ s' = { s with q1 := v }⟩)
              ].toAssocList
    outputs := [ (↑"d", ⟨List (RNext n), fun s v s' => s.d <+: v ∧
                    CombOut (rnextDep s) rnextFun (rnextLen s) dmin dmax v ∧
                    s' = { s with d := v }⟩) ].toAssocList
    internals := []
    init_state := fun s => s = ⟨[], [], [], []⟩ }

/-- State of the read domain's register bank. -/
structure RRegSt (n : Nat) where
  clk : List Bool
  d : List (RNext n)
  crn : List Bool
  st_q : List (RSt n)
  empty_q : List Bool
  gray_q : List (BitVec (n+1))

/-- How far the bank's inputs are known. -/
def RRegSt.horizon (s : RRegSt n) : Nat := min (min s.clk.length s.d.length) s.crn.length

/-- The register bank of the read domain: the state, the `empty` flag (a projection of it) and
the Gray pointer that crosses into the other domain.  Guarded like the write domain's
(`GateOK`), and with no memory. -/
@[drcomponents]
def rregBank (kq su P pw Rr Rc : Nat) : StringModule (RRegSt n) :=
  { inputs := [ (↑"clk", ⟨List Bool, fun s v s' => s.clk ⊏ v ∧ s' = { s with clk := v }⟩)
              , (↑"d", ⟨List (RNext n), fun s v s' => s.d ⊏ v ∧ s' = { s with d := v }⟩)
              , (↑"clrn", ⟨List Bool, fun s v s' => s.crn ⊏ v ∧ s' = { s with crn := v }⟩)
              ].toAssocList
    outputs := [ (↑"st", ⟨List (RSt n), fun s v s' => s.st_q <+: v ∧
                    RegOutG kq su default (GateOK P pw Rr Rc s.clk s.crn) s.clk
                      (fun u => (s.d.getD u default).st) s.d.length s.horizon v ∧
                    s' = { s with st_q := v }⟩)
               , (↑"empty", ⟨List Bool, fun s v s' => s.empty_q <+: v ∧
                    (∃ q, RegOutG kq su default (GateOK P pw Rr Rc s.clk s.crn) s.clk
                            (fun u => (s.d.getD u default).st) s.d.length s.horizon q ∧
                          v = q.map (fun st => st.empty)) ∧
                    s' = { s with empty_q := v }⟩)
               , (↑"gray", ⟨List (BitVec (n+1)), fun s v s' => s.gray_q <+: v ∧
                    BusRegOutG kq su (GateOK P pw Rr Rc s.clk s.crn) s.clk
                      (fun u => (s.d.getD u default).gnext) s.d.length s.horizon v ∧
                    s' = { s with gray_q := v }⟩)
               ].toAssocList
    internals := []
    init_state := fun s => s = ⟨[], [], [], [], [], []⟩ }

/-- State of the read port: the state register's output, the memory snapshot, and the data it
has emitted. -/
structure RDataSt (α : Type) (n : Nat) where
  st : List (RSt n)
  mem : List (BitVec n → α)
  q : List α

def rdataLen (s : RDataSt α n) : Nat := min s.st.length s.mem.length

/-- The read port: the memory word at the read address, combinational with a delay window. -/
@[drcomponents]
def rdataBlock (dmin dmax : Nat) : StringModule (RDataSt α n) :=
  { inputs := [ (↑"st", ⟨List (RSt n), fun s v s' => s.st ⊏ v ∧ s' = { s with st := v }⟩)
              , (↑"mem", ⟨List (BitVec n → α), fun s v s' => s.mem ⊏ v ∧ s' = { s with mem := v }⟩)
              ].toAssocList
    outputs := [ (↑"q", ⟨List α, fun s v s' => s.q <+: v ∧
                    ReadOut dmin dmax (fun u => (s.st.getD u default).ptr.setWidth n)
                      (fun u => s.mem.getD u (fun _ => default)) (rdataLen α s) v ∧
                    s' = { s with q := v }⟩) ].toAssocList
    internals := []
    init_state := fun s => s = ⟨[], [], []⟩ }

variable (n lat kq su stl dmin dmax ddmin ddmax P pw Rr Rc : Nat)

/-- The read domain as timed RTL blocks.  Same interface as `readDomain`. -/
def rdomTimedGraph := [graphEnv|
    clk [type="io"];
    inc [type="io"];
    wgray [type="io"];
    orc [type="io"];
    mem [type="io"];
    gray [type="io"];
    empty [type="io"];
    rdata [type="io"];

    clkF [type="clkF", typeImp=$(⟨_, fork2 Bool⟩)];
    regs [type="rregBank", typeImp=$(⟨_, rregBank (n := n) kq su P pw Rr Rc⟩)];
    clrS [type="clearSrc", typeImp=$(⟨_, clearSrc Rc⟩)];
    next [type="rnextBlock", typeImp=$(⟨_, rnextBlock (n := n) dmin dmax⟩)];
    sync [type="syncReg", typeImp=$(⟨_, syncReg (n := n) lat su stl⟩)];
    stF [type="stF", typeImp=$(⟨_, fork2 (RSt n)⟩)];
    rdat [type="rdataBlock", typeImp=$(⟨_, rdataBlock α (n := n) ddmin ddmax⟩)];

    clk -> clkF [to="in"];
    clkF -> regs [from="out1", to="clk"];
    clrS -> regs [from="crn", to="clrn"];
    clkF -> sync [from="out2", to="clk"];
    wgray -> sync [to="d"];
    orc -> sync [to="orc"];
    inc -> next [to="inc"];
    sync -> next [from="q", to="q1"];
    regs -> stF [from="st", to="in"];
    stF -> next [from="out1", to="st"];
    stF -> rdat [from="out2", to="st"];
    mem -> rdat [to="mem"];
    next -> regs [from="d", to="d"];

    regs -> gray [from="gray"];
    regs -> empty [from="empty"];
    rdat -> rdata [from="q"];
  ]

@[drunfold_defs]
def rdomTimedLowered := (rdomTimedGraph Unit 0 0 0 0 0 0 0 0 0 0 0 0 0).1.lower_TR |>.get rfl

def renv := (rdomTimedGraph α n lat kq su stl dmin dmax ddmin ddmax P pw Rr Rc).2

@[drenv] theorem renv_clkF : (renv α n lat kq su stl dmin dmax ddmin ddmax P pw Rr Rc).find? "clkF" =
  .some ⟨_, fork2 Bool⟩ := rfl
@[drenv] theorem renv_regs : (renv α n lat kq su stl dmin dmax ddmin ddmax P pw Rr Rc).find? "rregBank" =
  .some ⟨_, rregBank (n := n) kq su P pw Rr Rc⟩ := rfl
@[drenv] theorem renv_clrS : (renv α n lat kq su stl dmin dmax ddmin ddmax P pw Rr Rc).find? "clearSrc" =
  .some ⟨_, clearSrc Rc⟩ := rfl
@[drenv] theorem renv_next : (renv α n lat kq su stl dmin dmax ddmin ddmax P pw Rr Rc).find? "rnextBlock" =
  .some ⟨_, rnextBlock (n := n) dmin dmax⟩ := rfl
@[drenv] theorem renv_sync : (renv α n lat kq su stl dmin dmax ddmin ddmax P pw Rr Rc).find? "syncReg" =
  .some ⟨_, syncReg (n := n) lat su stl⟩ := rfl
@[drenv] theorem renv_stF : (renv α n lat kq su stl dmin dmax ddmin ddmax P pw Rr Rc).find? "stF" =
  .some ⟨_, fork2 (RSt n)⟩ := rfl
@[drenv] theorem renv_rdat : (renv α n lat kq su stl dmin dmax ddmin ddmax P pw Rr Rc).find? "rdataBlock" =
  .some ⟨_, rdataBlock α (n := n) ddmin ddmax⟩ := rfl

seal renv in
def_module rdomTimedT' : Type :=
  [T| rdomTimedLowered, (renv α n lat kq su stl dmin dmax ddmin ddmax P pw Rr Rc).find? ]
reduction_by
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type,
         ExprLow.build_module, ExprLow.build_module', toString]
  simp only [drenv]
  dsimp

/-- The state of the timed read domain, as produced by lowering the graph: the clear source,
the state fork, the synchroniser, the clock fork, the next-state block, the read port and the
register bank. -/
abbrev rdomTimedT : Type :=
  List Bool × List (RSt n) × (List Bool × List (BitVec (n+1)) × List (Orc n) × List (BitVec (n+1))) ×
    List Bool × RNextSt n × RDataSt α n × RRegSt n

omit [Inhabited α] in
theorem rdomTimedT_eq : rdomTimedT' α n = rdomTimedT α n := rfl

seal renv in
def_module rdomTimed : StringModule (rdomTimedT α n) :=
  [e| rdomTimedLowered, (renv α n lat kq su stl dmin dmax ddmin ddmax P pw Rr Rc).find? ]

end ReadBlocks

end Graphiti.AsyncFifo.Timed
