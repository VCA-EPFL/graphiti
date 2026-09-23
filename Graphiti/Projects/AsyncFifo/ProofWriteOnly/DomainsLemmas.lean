/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.ProofWriteOnly.SpecLemmas
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.Gray
import Graphiti.Projects.AsyncFifo.components.level2.Domains

/-! # `Domains`: the lemmas

Facts about the definitions in `components/level2/Domains.lean`.  The statement of the
main theorem names none of them. -/

namespace Graphiti.AsyncFifo

open Gray

/-! ### Per-bit resolution of a changing bus -/


section Machines

variable {α : Type} [Inhabited α] {n : Nat}

/-! ### Write domain -/


def wGray (lat stl su : Nat) (wclk winc : List Bool) (wdata : List α) (rgray : List (BitVec (n+1)))
    (orc : List (Orc n)) : List (BitVec (n+1)) :=
  moore (wstep stl) (WReg.init α n stl) (winp lat su wclk winc wdata rgray orc) (fun s => gray s.ptr)
    (wLen lat wclk winc wdata rgray orc)

def wFull (lat stl su : Nat) (wclk winc : List Bool) (wdata : List α) (rgray : List (BitVec (n+1)))
    (orc : List (Orc n)) : List Bool :=
  moore (wstep stl) (WReg.init α n stl) (winp lat su wclk winc wdata rgray orc) (fun s => s.full)
    (wLen lat wclk winc wdata rgray orc)

def wMem (lat stl su : Nat) (wclk winc : List Bool) (wdata : List α) (rgray : List (BitVec (n+1)))
    (orc : List (Orc n)) : List (BitVec n → α) :=
  moore (wstep stl) (WReg.init α n stl) (winp lat su wclk winc wdata rgray orc) (fun s => s.mem)
    (wLen lat wclk winc wdata rgray orc)

/-! ### Read domain -/


def rGray (lat stl su : Nat) (rclk rinc : List Bool) (wgray : List (BitVec (n+1))) (orc : List (Orc n)) :
    List (BitVec (n+1)) :=
  moore (rstep stl) (RReg.init n stl) (rinp lat su rclk rinc wgray orc) (fun s => gray s.ptr)
    (rLen lat rclk rinc wgray orc)

def rEmpty (lat stl su : Nat) (rclk rinc : List Bool) (wgray : List (BitVec (n+1))) (orc : List (Orc n)) :
    List Bool :=
  moore (rstep stl) (RReg.init n stl) (rinp lat su rclk rinc wgray orc) (fun s => s.empty)
    (rLen lat rclk rinc wgray orc)


def rData (lat stl su : Nat) (rclk rinc : List Bool) (wgray : List (BitVec (n+1))) (orc : List (Orc n))
    (mem : List (BitVec n → α)) : List α :=
  timeline (rval lat stl su rclk rinc wgray orc mem) (rDataLen lat rclk rinc wgray orc mem)

end Machines

/-! ### Edges, as the contracts of `Contracts.lean` refer to them -/


end Graphiti.AsyncFifo