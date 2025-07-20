/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Gurvan Debaussart
-/

import Graphiti.Core.Module
import Graphiti.Core.ModuleLemmas
import Graphiti.Core.Component
import Graphiti.Core.ExprLow
import Graphiti.Projects.Noc.Lang

namespace Graphiti.Noc.Router

  variable (netsz : Netsz) (Flit : Type)

  namespace Unbounded

    @[drunfold_defs]
    def queue : Router netsz Flit :=
      {
        State       := List Flit
        init_state  := []
        input_rel   := λ rid s flit s' => s' = s ++ [flit]
        output_rel  := λ rid s flit s' => s = flit :: s'
      }

    def queueM : ExprLow String :=
      .base { } "Hello"


    @[drunfold_defs]
    def bag : Router netsz Flit :=
      {
        State       := List Flit
        init_state  := []
        input_rel   := λ rid s flit s' => s' = s ++ [flit]
        output_rel  := λ rid s flit s' => ∃ i : Fin (s.length), s' = s.remove i
      }

  end Unbounded

  namespace Bounded

    variable (len : Nat)

    @[drunfold_defs]
    def queue : Router netsz Flit :=
      {
        State       := List Flit
        init_state  := []
        input_rel   := λ rid s flit s' => s'.length < len ∧ s' = s ++ [flit]
        output_rel  := λ rid s flit s' => s = flit :: s'
      }

    @[drunfold_defs]
    def bag : Router netsz Flit :=
      {
        State       := List Flit
        init_state  := []
        input_rel   := λ rid s flit s' => s'.length < len ∧ s' = s ++ [flit]
        output_rel  := λ rid s flit s' => ∃ i : Fin (s.length), s' = s.remove i
      }

  end Bounded

end Graphiti.Noc.Router
