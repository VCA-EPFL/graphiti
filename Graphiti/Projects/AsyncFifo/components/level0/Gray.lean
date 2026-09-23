/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

/-!
# Gray codes on `BitVec`

The pointers that cross between the two clock domains are Gray-coded, so that a pointer caught
mid-change by the other domain's synchroniser is always one of its two neighbouring values.
`gray` encodes, `ungray` decodes.  Their properties are in `ProofWriteOnly/Gray.lean`.
-/

namespace Graphiti.AsyncFifo.Gray

/-- Binary-reflected Gray code. -/
def gray {w : Nat} (x : BitVec w) : BitVec w := x ^^^ (x >>> 1)

/-- Inverse of `gray` (prefix-xor), using `w` steps of fuel. -/
def ungrayAux {w : Nat} : Nat → BitVec w → BitVec w
  | 0, _ => 0#w
  | k+1, g => g ^^^ ungrayAux k (g >>> 1)

def ungray {w : Nat} (g : BitVec w) : BitVec w := ungrayAux w g

end Graphiti.AsyncFifo.Gray
