/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Lean

import Graphiti.Module
import Graphiti.Simp
import Graphiti.ExprHigh
import Graphiti.AssocList.Basic

namespace Graphiti

def Env Ident := Ident → Option (TModule1 Ident)

namespace Env

def subsetOf {Ident} (ε₁ ε₂ : Env Ident) : Prop :=
  ∀ i v, ε₁ i = .some v → ε₂ i = .some v

end Env

end Graphiti
