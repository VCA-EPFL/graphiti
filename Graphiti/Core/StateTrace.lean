/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

module

public import Graphiti.Core.Graph.ModuleLemmas
public import Graphiti.Core.StateTransition

@[expose] public section

namespace Graphiti

namespace Module

section StateTransition

variable (Ident : Type _)
variable [DecidableEq Ident]
variable (S : Type _)

structure State where
  state : S
  module : Module Ident S

variable {Ident} {S}

inductive step : State Ident S → List S → State Ident S → Prop where
| input {st ident s' v} :
  (st.module.inputs.getIO ident).snd st.state v s' →
  step st [s'] ⟨s', st.module⟩
| output {st ident s' v} :
  (st.module.outputs.getIO ident).snd st.state v s' →
  step st [s'] ⟨s', st.module⟩
| internal {st r s'} :
  r ∈ st.module.internals →
  r st.state s' →
  step st [s'] ⟨s', st.module⟩

def state_transition (m : Module Ident S) : StateTransition (State Ident S) S where
  init := fun s => m.init_state s.state ∧ s.module = m
  step := step

end StateTransition

end Module

end Graphiti
