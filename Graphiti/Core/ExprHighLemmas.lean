/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

module

public import Graphiti.Core.Module
public import Graphiti.Core.ExprHigh
public import Graphiti.Core.ExprLowLemmas
public import Graphiti.Core.ExprHighElaborator

@[expose] public section

namespace Graphiti

namespace Module

variable {Ident Typ : Type _}

def liftGraph {S} (m : Module Ident S) (p : PortMapping Ident) (inst : Ident) (typ : Typ) : ExprHigh Ident Typ :=
  { modules := [(inst, p, typ)].toAssocList
    connections := []
  }

end Module

namespace ExprHigh

section Semantics

variable {Ident Typ}
variable [DecidableEq Ident]

variable (ε : Env Ident Typ)

@[drunfold] def build_module' (e : ExprHigh Ident Typ) : Option (TModule Ident) :=
  e.lower.bind (·.build_module ε)

@[drunfold] def build_moduleP (e : ExprHigh Ident Typ)
    (h : (build_module' ε e).isSome = true := by rfl)
    : Σ T, Module Ident T :=
  e.build_module' ε |>.get h

@[drunfold] def build_module (e : ExprHigh Ident Typ) : Σ T, Module Ident T :=
  e.build_module' ε |>.getD ⟨ Unit, Module.empty _ ⟩

@[drunfold] abbrev build_module_expr (e : ExprHigh Ident Typ)
    : Module Ident (e.build_module ε).1 := (e.build_module ε).2

@[drunfold] abbrev build_module_type (e : ExprHigh Ident Typ)
    : Type _ := (e.build_module ε).1

notation:max "[Ge| " e ", " ε " ]" => build_module_expr ε e
notation:max "[GT| " e ", " ε " ]" => build_module_type ε e

end Semantics

end ExprHigh

end Graphiti
