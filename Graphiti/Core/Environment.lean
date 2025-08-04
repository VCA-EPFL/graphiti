/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Lean

import Graphiti.Core.Module
import Graphiti.Core.Simp
import Graphiti.Core.ExprHigh
import Graphiti.Core.AssocList.Basic
import Graphiti.Core.Component

namespace Graphiti

def Env Ident Typ := Typ → Option (TModule1 Ident)

namespace Env

def subsetOf {Ident Typ} (ε₁ ε₂ : Env Ident Typ) : Prop :=
  ∀ i v, ε₁ i = .some v → ε₂ i = .some v

def well_formed (ε : Env String (String × String)) (s : String) : Prop :=
  match s with
  | "branch" => ∀ a mod, ε (s, a) = some mod → ∃ T, mod = ⟨_, StringModule.branch T⟩
  | "cntrl_merge" => ∀ a mod, ε (s, a) = some mod → ∃ T, mod = ⟨_, StringModule.cntrl_merge T⟩
  | "constant" => ∀ a mod, ε (s, a) = some mod → ∃ T, ∃ (t : T), mod = ⟨_, StringModule.constant t⟩
  | "fork" => ∀ a mod, ε (s, a) = some mod → ∃ T n, mod = ⟨_, StringModule.fork T n⟩
  | "init" => ∀ a mod, ε (s, a) = some mod → ∃ T, ∃ (t : T), mod = ⟨_, StringModule.init T t⟩
  | "join" => ∀ a mod, ε (s, a) = some mod → ∃ T T', mod = ⟨_, StringModule.join T T'⟩
  | "load" => ∀ a mod, ε (s, a) = some mod → ∃ S T, mod = ⟨_, StringModule.load S T⟩
  | "merge" => ∀ a mod, ε (s, a) = some mod → ∃ T n, mod = ⟨_, StringModule.merge T n⟩
  | "mux" => ∀ a mod, ε (s, a) = some mod → ∃ T, mod = ⟨_, StringModule.mux T⟩
  | "operator1" => ∀ a mod, ε (s, a) = some mod → ∃ T1 T2 T2m s, mod = ⟨_, @StringModule.operator1 T1 T2 T2m s⟩
  | "operator2" => ∀ a mod, ε (s, a) = some mod → ∃ T1 T2 T3 T3m s, mod = ⟨_, @StringModule.operator2 T1 T2 T3 T3m s⟩
  | "operator3" => ∀ a mod, ε (s, a) = some mod → ∃ T1 T2 T3 T4 T4m s, mod = ⟨_, @StringModule.operator3 T1 T2 T3 T4 T4m s⟩
  | "pure" => ∀ a mod, ε (s, a) = some mod → ∃ α β, ∃ (f : α → β), mod = ⟨_, StringModule.pure f⟩
  | "queue" => ∀ a mod, ε (s, a) = some mod → ∃ T, mod = ⟨_, StringModule.queue T⟩
  | "sink" => ∀ a mod, ε (s, a) = some mod → ∃ T n, mod = ⟨_, StringModule.sink T n⟩
  | "split" => ∀ a mod, ε (s, a) = some mod → ∃ T T', mod = ⟨_, StringModule.split T T'⟩
  | "tagger_untagger_val" => ∀ a mod, ε (s, a) = some mod → ∃ TagT mm T T', mod = ⟨_, @StringModule.tagger_untagger_val TagT mm T T'⟩
  | _ => True

end Env

end Graphiti
