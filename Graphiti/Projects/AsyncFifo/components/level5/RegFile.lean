/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Core.Graph.ModuleLemmas
import Graphiti.Core.Graph.ModuleReduction
import Graphiti.Core.Graph.ExprHighElaborator
import Graphiti.Projects.AsyncFifo.components.level0.Streams
import Graphiti.Projects.AsyncFifo.components.level1.Gates
import Graphiti.Projects.AsyncFifo.components.level3.Contracts
import Graphiti.Projects.AsyncFifo.components.level3.Dff
import Graphiti.Projects.AsyncFifo.components.level4.EnReg

/-!
# The register file: an address decoder and four cells

The write domain's memory holds four one-bit entries.  The address is decoded into four write
enables -- six gates, two inverters and four ANDs, and one more AND per entry for the write
enable itself -- and each enable drives a cell of `EnReg.lean`, through the cell's specification `enSpec`.

Nothing here has feedback: the loop of a memory lives inside the cell.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Graphiti.AsyncFifo.RegFile

open Graphiti.AsyncFifo Graphiti.AsyncFifo.Gates Graphiti.AsyncFifo.Contracts
  Graphiti.AsyncFifo.Dff Graphiti.AsyncFifo.EnReg

/-! ### The address and its bits -/

def bitsA (i : Nat) (addr : List (BitVec 2)) : List Bool := addr.map (·.getLsbD i)

/-- Split the address bus into its two bits. -/
@[drcomponents]
def unpack2A : StringModule (List (BitVec 2)) :=
  { inputs := [ (↑"a", ⟨List (BitVec 2), fun s v s' => s ⊏ v ∧ s' = v⟩) ].toAssocList
    outputs := [ (↑"b0", ⟨List Bool, fun s v s' => s' = s ∧ v = bitsA 0 s⟩)
               , (↑"b1", ⟨List Bool, fun s v s' => s' = s ∧ v = bitsA 1 s⟩) ].toAssocList
    internals := []
    init_state := fun s => s = [] }

/-- The four entries as one function, reported three instants short of where the cells reach.
That is the file's reporting policy: the decoder in front of the cells is three gates deep, so
the cells run up to three instants ahead of the address, and what a block reports has to stay
inside the horizon its own inputs justify (`MemOut`'s length clause, which is what makes that
contract monotone).  Reporting less than one computes is always sound. -/
def packMemOut (q0 q1 q2 q3 : List Bool) : List (BitVec 2 → Bool) :=
  timeline (fun t a => if a = 0#2 then q0.getD t false else if a = 1#2 then q1.getD t false
    else if a = 2#2 then q2.getD t false else q3.getD t false)
    (min (min q0.length q1.length) (min q2.length q3.length) - 3)

/-- Assemble the four entries into one function. -/
@[drcomponents]
def packMem : StringModule (List Bool × List Bool × List Bool × List Bool) :=
  { inputs := [ (↑"q0", ⟨List Bool, fun s v s' => s.1 ⊏ v ∧ s' = (v, s.2)⟩)
              , (↑"q1", ⟨List Bool, fun s v s' => s.2.1 ⊏ v ∧ s' = (s.1, v, s.2.2)⟩)
              , (↑"q2", ⟨List Bool, fun s v s' => s.2.2.1 ⊏ v ∧ s' = (s.1, s.2.1, v, s.2.2.2)⟩)
              , (↑"q3", ⟨List Bool, fun s v s' => s.2.2.2 ⊏ v ∧ s' = (s.1, s.2.1, s.2.2.1, v)⟩)
              ].toAssocList
    outputs := [ (↑"mem", ⟨List (BitVec 2 → Bool), fun s v s' => s' = s ∧
                    v = packMemOut s.1 s.2.1 s.2.2.1 s.2.2.2⟩) ].toAssocList
    internals := []
    init_state := fun s => s = ([], [], [], []) }

/-! ### The netlist -/

def memGraph := [graphEnv|
    clk [type="io"];
    we [type="io"];
    addr [type="io"];
    data [type="io"];
    clrn [type="io"];
    mem [type="io"];

    unpA [type="unpack2A", typeImp=$(⟨_, unpack2A⟩)];
    clkF [type="fork4", typeImp=$(⟨_, fork4⟩)];
    crF [type="fork4", typeImp=$(⟨_, fork4⟩)];
    weF [type="fork4", typeImp=$(⟨_, fork4⟩)];
    dataF [type="fork4", typeImp=$(⟨_, fork4⟩)];
    a0F [type="fork3", typeImp=$(⟨_, fork3⟩)];
    a1F [type="fork3", typeImp=$(⟨_, fork3⟩)];
    na0 [type="not1", typeImp=$(⟨_, gate1 not⟩)];
    na1 [type="not1", typeImp=$(⟨_, gate1 not⟩)];
    na0F [type="fork2", typeImp=$(⟨_, fork2 Bool⟩)];
    na1F [type="fork2", typeImp=$(⟨_, fork2 Bool⟩)];
    dec0 [type="and2", typeImp=$(⟨_, gate2 and2⟩)];
    dec1 [type="and2", typeImp=$(⟨_, gate2 and2⟩)];
    dec2 [type="and2", typeImp=$(⟨_, gate2 and2⟩)];
    dec3 [type="and2", typeImp=$(⟨_, gate2 and2⟩)];
    en0 [type="and2", typeImp=$(⟨_, gate2 and2⟩)];
    en1 [type="and2", typeImp=$(⟨_, gate2 and2⟩)];
    en2 [type="and2", typeImp=$(⟨_, gate2 and2⟩)];
    en3 [type="and2", typeImp=$(⟨_, gate2 and2⟩)];
    c0 [type="cell", typeImp=$(⟨_, enSpec⟩)];
    c1 [type="cell", typeImp=$(⟨_, enSpec⟩)];
    c2 [type="cell", typeImp=$(⟨_, enSpec⟩)];
    c3 [type="cell", typeImp=$(⟨_, enSpec⟩)];
    pk [type="packMem", typeImp=$(⟨_, packMem⟩)];

    clk -> clkF [to="in"];
    we -> weF [to="in"];
    addr -> unpA [to="a"];
    data -> dataF [to="in"];
    clrn -> crF [to="in"];

    unpA -> a0F [from="b0", to="in"];
    unpA -> a1F [from="b1", to="in"];
    a0F -> na0 [from="out1", to="a"];
    a0F -> dec1 [from="out2", to="a"];
    a0F -> dec3 [from="out3", to="a"];
    a1F -> na1 [from="out1", to="a"];
    a1F -> dec2 [from="out2", to="b"];
    a1F -> dec3 [from="out3", to="b"];
    na0 -> na0F [from="out", to="in"];
    na0F -> dec0 [from="out1", to="a"];
    na0F -> dec2 [from="out2", to="a"];
    na1 -> na1F [from="out", to="in"];
    na1F -> dec0 [from="out1", to="b"];
    na1F -> dec1 [from="out2", to="b"];
    weF -> en0 [from="out1", to="a"];
    weF -> en1 [from="out2", to="a"];
    weF -> en2 [from="out3", to="a"];
    weF -> en3 [from="out4", to="a"];
    dec0 -> en0 [from="out", to="b"];
    dec1 -> en1 [from="out", to="b"];
    dec2 -> en2 [from="out", to="b"];
    dec3 -> en3 [from="out", to="b"];
    clkF -> c0 [from="out1", to="clk"];
    clkF -> c1 [from="out2", to="clk"];
    clkF -> c2 [from="out3", to="clk"];
    clkF -> c3 [from="out4", to="clk"];
    crF -> c0 [from="out1", to="clrn"];
    crF -> c1 [from="out2", to="clrn"];
    crF -> c2 [from="out3", to="clrn"];
    crF -> c3 [from="out4", to="clrn"];
    dataF -> c0 [from="out1", to="data"];
    dataF -> c1 [from="out2", to="data"];
    dataF -> c2 [from="out3", to="data"];
    dataF -> c3 [from="out4", to="data"];
    en0 -> c0 [from="out", to="en"];
    en1 -> c1 [from="out", to="en"];
    en2 -> c2 [from="out", to="en"];
    en3 -> c3 [from="out", to="en"];
    c0 -> pk [from="q", to="q0"];
    c1 -> pk [from="q", to="q1"];
    c2 -> pk [from="q", to="q2"];
    c3 -> pk [from="q", to="q3"];

    pk -> mem [from="mem"];
  ]

@[drunfold_defs]
def memLowered := memGraph.1.lower_TR |>.get rfl

/-- What each node of the graph is: the address decoder's gates and forks, the packer, and for each cell its specification
`EnReg.enSpec`. -/
def menv := memGraph.2

/-- **The register file**: the graph, each child standing for its specification. -/
def memImpl := [e| memLowered, menv.find? ]

/-! ### The decoded write enables, as streams -/

/-- The address bit the decoder of entry `i` reads, inverted or not. -/
def W_bit (i k : Nat) (addr : List (BitVec 2)) : List Bool :=
  if (i >>> k) % 2 = 0 then gate1Out not (bitsA k addr) else bitsA k addr

/-- The address match of entry `i`. -/
def W_dec (i : Nat) (addr : List (BitVec 2)) : List Bool :=
  gateOut and2 (W_bit i 0 addr) (W_bit i 1 addr)

/-- The enable of entry `i`: the write enable, and the address matching `i`.  Three gates deep:
an inverter, the address match, and the write enable itself. -/
def W_en (i : Nat) (we : List Bool) (addr : List (BitVec 2)) : List Bool :=
  gateOut and2 we (W_dec i addr)

/-- What one cell of the file reports. -/
def cellOut (i : Nat) (clk we : List Bool) (addr : List (BitVec 2)) (data crn : List Bool) :
    List Bool :=
  enOut clk (W_en i we addr) data crn

/-- How far the file's inputs are known. -/
def memLen (clk we : List Bool) (addr : List (BitVec 2)) (data crn : List Bool) : Nat :=
  min (min clk.length we.length) (min addr.length (min data.length crn.length))

/-- What the file reports: its four cells, as far as the *file's own* inputs are known plus the
one instant a Moore block may add.

The packer on its own cannot know that bound.  It sees only the four cells, and a cell's enable
comes through the decoder, which is three gates deep, so the cells are known further than the
file's inputs are --- by as much as three instants, and by nothing at all when the address and
the write enable are the short ones.  With only the cells in hand the packer has to assume the
worst and subtract the decoder's depth (`packMemOut`), which costs it three instants whenever
they were not there to lose.  Read against the file's inputs the bound is exact, and that is
what the file reports: `memLen + 1`, never more (`memLen_le_enLen`) and never less. -/
def memOut (clk we : List Bool) (addr : List (BitVec 2)) (data crn : List Bool) :
    List (BitVec 2 → Bool) :=
  timeline (fun t a => if a = 0#2 then (cellOut 0 clk we addr data crn).getD t false
      else if a = 1#2 then (cellOut 1 clk we addr data crn).getD t false
      else if a = 2#2 then (cellOut 2 clk we addr data crn).getD t false
      else (cellOut 3 clk we addr data crn).getD t false)
    (memLen clk we addr data crn + 1)

/-! ### The specification -/

/-- The register file as a single block. -/
@[drcomponents]
def memSpec : StringModule (List Bool × List Bool × List (BitVec 2) × List Bool × List Bool ×
    List (BitVec 2 → Bool)) :=
  { inputs := [ (↑"clk", ⟨List Bool, fun s v s' => s.1 ⊏ v ∧ s' = (v, s.2)⟩)
              , (↑"we", ⟨List Bool, fun s v s' => s.2.1 ⊏ v ∧ s' = (s.1, v, s.2.2)⟩)
              , (↑"addr", ⟨List (BitVec 2), fun s v s' => s.2.2.1 ⊏ v ∧
                  s' = (s.1, s.2.1, v, s.2.2.2)⟩)
              , (↑"data", ⟨List Bool, fun s v s' => s.2.2.2.1 ⊏ v ∧
                  s' = (s.1, s.2.1, s.2.2.1, v, s.2.2.2.2)⟩)
              , (↑"clrn", ⟨List Bool, fun s v s' => s.2.2.2.2.1 ⊏ v ∧
                  s' = (s.1, s.2.1, s.2.2.1, s.2.2.2.1, v, s.2.2.2.2.2)⟩) ].toAssocList
    outputs := [ (↑"mem", ⟨List (BitVec 2 → Bool), fun s v s' => s.2.2.2.2.2 <+: v ∧
                    v <+: memOut s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2.1 ∧
                    s' = (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, v)⟩) ].toAssocList
    internals := []
    init_state := fun s => s = ([], [], [], [], [], []) }

end Graphiti.AsyncFifo.RegFile
