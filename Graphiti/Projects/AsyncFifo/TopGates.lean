/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.components.level6.WriteBank
import Graphiti.Projects.AsyncFifo.components.level6.ReadBank
import Graphiti.Projects.AsyncFifo.components.level4.WriteNext
import Graphiti.Projects.AsyncFifo.components.level4.ReadNext
import Graphiti.Projects.AsyncFifo.components.level4.ReadPort
import Graphiti.Projects.AsyncFifo.components.level5.SyncStage
import Graphiti.Projects.AsyncFifo.components.level3.Oracle
import Graphiti.Projects.AsyncFifo.components.level8.Fifo

/-!
# The FIFO, as gates

Every component's implementation names its children's *specifications*: that is what makes a
component reusable, and what keeps each proof the size of one block.  The circuit the main
theorem is about is obtained from them by substitution, bottom up.  For a component `X`,

* `X.gateEnv` is `X`'s environment with every child's specification replaced by the child's
  gates, and
* `X.gates` is `X`'s graph read in that environment: `X` as gates and wiring only.

At the leaves the implementation already is gates (`Dff.dffImpl`, `WriteNext.nextImpl`,
`ReadNext.nextImpl`, `ReadPort.readImpl`), and the synchroniser's first stage keeps its settling
flip-flops, the one assumed primitive.  Each substitution is licensed by the theorems of the
components substituted (`TopRefinement.lean`, and `ProofWriteOnly/StorageGates.lean` for the
storage blocks).  This file holds only the definitions.
-/

namespace Graphiti.AsyncFifo

open Batteries (AssocList)
open Contracts

/-! ### The storage blocks

Flip-flops (`dff`) replaced by `Dff.dffImpl`, then cells by `EnReg.gates`, then registers and the
register file by their gates in the two banks. -/

/-- The memory cell, its flip-flop replaced by gates. -/
def EnReg.gateEnv : AssocList String (TModule1 String) :=
  AssocList.cons "dff" ⟨_, Dff.dffImpl⟩ EnReg.eenv

def EnReg.gates := [e| EnReg.enLowered, EnReg.gateEnv.find? ]

/-- The three-bit register, its flip-flops replaced by gates. -/
def BusReg.gateEnv : AssocList String (TModule1 String) :=
  AssocList.cons "dff" ⟨_, Dff.dffImpl⟩ BusReg.benv

def BusReg.gates := [e| BusReg.busLowered, BusReg.gateEnv.find? ]

/-- The write domain's state register, its flip-flops replaced by gates. -/
def WriteState.gateEnv : AssocList String (TModule1 String) :=
  AssocList.cons "dff" ⟨_, Dff.dffImpl⟩ WriteState.senv

def WriteState.gates := [e| WriteState.stLowered, WriteState.gateEnv.find? ]

/-- The read domain's state register, its flip-flops replaced by gates. -/
def ReadState.gateEnv : AssocList String (TModule1 String) :=
  AssocList.cons "dff" ⟨_, Dff.dffImpl⟩ ReadState.senv

def ReadState.gates := [e| ReadState.stLowered, ReadState.gateEnv.find? ]

/-- The register file, its cells replaced by gates. -/
def RegFile.gateEnv : AssocList String (TModule1 String) :=
  AssocList.cons "cell" ⟨_, EnReg.gates⟩ RegFile.menv

def RegFile.gates := [e| RegFile.memLowered, RegFile.gateEnv.find? ]

/-- The write domain's register bank, every register replaced by gates. -/
def WriteBank.gateEnv : AssocList String (TModule1 String) :=
  AssocList.cons "streg" ⟨_, WriteState.gates⟩
    (AssocList.cons "busreg" ⟨_, BusReg.gates⟩
      (AssocList.cons "memory" ⟨_, RegFile.gates⟩ WriteBank.kenv))

def WriteBank.gates := [e| WriteBank.bankLowered, WriteBank.gateEnv.find? ]

/-- The read domain's register bank, every register replaced by gates. -/
def ReadBank.gateEnv : AssocList String (TModule1 String) :=
  AssocList.cons "streg" ⟨_, ReadState.gates⟩
    (AssocList.cons "busreg" ⟨_, BusReg.gates⟩ ReadBank.kenv)

def ReadBank.gates := [e| ReadBank.bankLowered, ReadBank.gateEnv.find? ]

/-! ### The write domain -/

/-- The write domain's blocks as gates.  The bank meets the windows `kq = 4` and `su = 8` ---
the flip-flop's clock-to-q, and the register file's setup (the cell's five plus the decoder's
three). -/
def wdomGateEnv (lat stl Rc : Nat) : AssocList String (TModule1 String) :=
  AssocList.cons "WriteBank" ⟨_, WriteBank.gates⟩
    (AssocList.cons "WriteNext" ⟨_, WriteNext.nextImpl⟩
      (AssocList.cons "SyncStage" ⟨_, SyncStage.syncImpl lat 8 stl⟩
        (AssocList.cons "clkF" ⟨_, fork2 Bool⟩
          (AssocList.cons "clearSrc" ⟨_, clearSrc Rc⟩ .nil))))

/-- **The write domain as gates**: its next-state logic and its whole state. -/
def wdomGates (lat stl Rc : Nat) := [e| wdomLowered, (wdomGateEnv lat stl Rc).find? ]

/-! ### The read domain -/

/-- The read domain's blocks as gates.  The graph (`rdomLowered`) is unchanged; only what its
nodes stand for.  The bank fixes the windows it meets, `kq = 4` and `su = 8`. -/
def rdomGateEnv (lat stl Rc : Nat) : AssocList String (TModule1 String) :=
  AssocList.cons "ReadPort" ⟨_, ReadPort.readImpl⟩
    (AssocList.cons "ReadBank" ⟨_, ReadBank.gates⟩
      (AssocList.cons "ReadNext" ⟨_, ReadNext.nextImpl⟩
        (AssocList.cons "SyncStage" ⟨_, SyncStage.syncImpl lat 8 stl⟩
          (AssocList.cons "clkF" ⟨_, fork2 Bool⟩
            (AssocList.cons "clearSrc" ⟨_, clearSrc Rc⟩
              (AssocList.cons "stF" ⟨_, fork2 (RSt 2)⟩ .nil))))))

/-- **The read domain as gates**: its next-state logic, its whole state and its read port. -/
def rdomGates (lat stl Rc : Nat) := [e| rdomLowered, (rdomGateEnv lat stl Rc).find? ]

/-! ### The FIFO -/

/-- The FIFO's nodes with both clock domains as gates.  The graph (`asyncFifoLowered`) is the
implementation's; only what `wdom` and `rdom` stand for changes. -/
def fifoGateEnv (lat stl Rc : Nat) : AssocList String (TModule1 String) :=
  AssocList.cons "wdom" ⟨_, wdomGates lat stl Rc⟩
    (AssocList.cons "rdom" ⟨_, rdomGates lat stl Rc⟩
      (AssocList.cons "oracle_w" ⟨_, oracle 2⟩
        (AssocList.cons "oracle_r" ⟨_, oracle 2⟩ .nil)))

/-- **The asynchronous FIFO with both clock domains as gates** (depth `4`, 1-bit data). -/
def asyncFifoGates (lat stl Rc : Nat) :=
  [e| asyncFifoLowered, (fifoGateEnv lat stl Rc).find? ]

end Graphiti.AsyncFifo
