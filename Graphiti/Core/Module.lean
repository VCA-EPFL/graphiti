/-
Copyright (c) 2024, 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Lean
import Qq

import Graphiti.Core.Basic
import Graphiti.Core.Simp
import Graphiti.Core.List
import Graphiti.Core.AssocList
import Graphiti.Core.HVector
import Graphiti.Core.Tactic
import Graphiti.Core.BasicLemmas

open Batteries (AssocList)

namespace Graphiti

/--
State that there exists zero or more internal rule executions to reach a final
state from an initial state.
-/
inductive existSR {S : Type _} (rules : List (S → S → Prop)) : S → S → Prop where
| done : ∀ init, existSR rules init init
| step : ∀ init mid final rule,
    rule ∈ rules →
    rule init mid →
    existSR rules mid final →
    existSR rules init final

/-- Input/Output relation --/
@[simp] abbrev RelIO (S : Type _) := Σ T : Type, S → T → S → Prop

/-- Internal relation --/
@[simp] abbrev RelInt (S : Type _) := S → S → Prop

/--
`Module` definition, which is our definition of circuit semantics.  It can have inputs and outputs, which are maps from
`Ident` to transition rules accept or return a value.

One might think to merge inputs and outputs into a single field, because they essentially have the same form.  In most
cases, they are symmetric too, so this would make proofs much simpler.  However, they are actually asymmetric in the
definition of refinement, where inputs can be followed by internal steps, but outputs cannot.  This makes it possible to
connect an output to an input, because it is guaranteed that there won't be any intermediate internal steps that have to
be executed in between the output rule and input rule execution.
-/
@[ext]
structure Module (Ident S : Type _) where
  inputs : PortMap Ident (RelIO S)
  outputs : PortMap Ident (RelIO S)
  internals : List (RelInt S) := []
  init_state : S → Prop
deriving Inhabited

-- mklenses Module
-- open Module.l

namespace Module

/--
The empty module, which should also be the `default` module.
-/
@[drunfold] def empty {Ident : Type _} S : Module Ident S :=
  {
    inputs := ∅,
    outputs := ∅,
    internals:= ∅,
    init_state := λ _ => True,
  }

theorem empty_is_default {Ident S} : @empty Ident S = default := Eq.refl _

section

universe i

variable {Ident : Type i}
variable [DecidableEq Ident]

@[drunfold] def liftL {S S' : Type _} (x : RelIO S) : RelIO (S × S') :=
  ⟨ x.1, λ (a,b) ret (a',b') => x.2 a ret a' ∧ b = b' ⟩

@[drunfold] def liftR {S S'} (x : RelIO S') : RelIO (S × S') :=
  ⟨ x.1, λ (a,b) ret (a',b') => x.2 b ret b' ∧ a = a' ⟩

@[drunfold] def liftL' {S S'} (x : RelInt S) : RelInt (S × S') :=
  λ (a,b) (a',b') => x a a' ∧ b = b'

@[drunfold] def liftR' {S S'} (x : RelInt S') : RelInt (S × S'):=
  λ (a,b) (a',b') => x b b' ∧ a = a'

@[drunfold] def liftLD {α : Type _} {l₁ l₂ : List α} {f} (x : RelIO (HVector f l₁))
    : RelIO (HVector f (l₁ ++ l₂)) :=
  ⟨ x.1, λ a ret a' => x.2 a.left ret a'.left ∧ a.right = a'.right ⟩

@[drunfold] def liftRD {α : Type _} {l₁ l₂ : List α} {f} (x : RelIO (HVector f l₂))
    : RelIO (HVector f (l₁ ++ l₂)) :=
  ⟨ x.1, λ a ret a' => x.2 a.right ret a'.right ∧ a.left = a'.left ⟩

@[drunfold] def liftLD' {α : Type _} {l₁ l₂ : List α} {f} (x : RelInt (HVector f l₁))
    : RelInt (HVector f (l₁ ++ l₂)) :=
  λ a a' => x a.left a'.left ∧ a.right = a'.right

@[drunfold] def liftRD' {α : Type _} {l₁ l₂ : List α} {f} (x : RelInt (HVector f l₂))
    : RelInt (HVector f (l₁ ++ l₂)) :=
  λ a a' => x a.right a'.right ∧ a.left = a'.left

@[drunfold] def liftSingle {α} {a : α} {f} (x : RelIO (f a)) : RelIO (HVector f [a]) :=
  ⟨ x.1, λ | .cons a .nil, t, .cons a' .nil => x.2 a t a' ⟩

@[drunfold] def liftSingle' {α} {a : α} {f} (x : RelInt (f a)) : RelInt (HVector f [a]) :=
  λ | .cons a .nil, .cons a' .nil => x a a'

def EqExt {S} (m₁ m₂ : Module Ident S) : Prop :=
  m₁.inputs.EqExt m₂.inputs
  ∧ m₁.outputs.EqExt m₂.outputs
  ∧ m₁.internals.Perm m₂.internals
  ∧ (∀ i, m₁.init_state i ↔ m₂.init_state i)

theorem EqExt.symm {S} (m₁ m₂ : Module Ident S) :
  m₁.EqExt m₂ → m₂.EqExt m₁ := by
  unfold EqExt; intros; simp [*, AssocList.EqExt.symm, List.Perm.symm]

def connect'' {Ti To S} (ruleO : S → To → S → Prop) (ruleI : S → Ti → S → Prop) : RelInt S :=
  (λ st st' =>
     (∀ wf : To = Ti,
       ∃ consumed_output output, ruleO st output consumed_output
         -- ∧ int consumed_output consumed_input
         ∧ ruleI consumed_output (wf.mp output) st')
     ∧ (∀ nwf : To ≠ Ti, False))

/--
`connect'` will produce a new rule that fuses an input with an output, with a
precondition that the input and output type must match.
-/
@[drunfold] def connect' {S : Type _} (mod : Module Ident S) (o i : InternalPort Ident) : Module Ident S :=
  {
    inputs := mod.inputs.eraseAll i,
    outputs :=  mod.outputs.eraseAll o,
    internals := connect'' (mod.outputs.getIO o).2 (mod.inputs.getIO i).2 :: mod.internals,
    init_state := mod.init_state,
  }

theorem connect''_dep_rw {C : Type} {x y x' y' : RelIO C} (h : x' = x := by simp; rfl) (h' : y' = y := by simp; rfl) :
    @Module.connect'' y.1 x.1 C x.2 y.2 = @Module.connect'' y'.1 x'.1 C x'.2 y'.2 := by
  intros; subst_vars; rfl

@[drunfold]
def product {S S'} (mod1 : Module Ident S) (mod2: Module Ident S') : Module Ident (S × S') :=
  {
    inputs := (mod1.inputs.mapVal (λ _ => liftL)).append (mod2.inputs.mapVal (λ _ => liftR)),
    outputs := (mod1.outputs.mapVal (λ _ => liftL)).append (mod2.outputs.mapVal (λ _ => liftR)),
    internals := mod1.internals.map liftL' ++ mod2.internals.map liftR',
    init_state := λ (s, s') => mod1.init_state s ∧ mod2.init_state s',
  }

def NamedProduct (s : String) T₁ T₂ := T₁ × T₂

@[drunfold]
def named_product {S S'} (mod1 : Module Ident S) (mod2: Module Ident S') (str : String := "") : Module Ident (NamedProduct str S S') :=
  {
    inputs := (mod1.inputs.mapVal (λ _ => liftL)).append (mod2.inputs.mapVal (λ _ => liftR)),
    outputs := (mod1.outputs.mapVal (λ _ => liftL)).append (mod2.outputs.mapVal (λ _ => liftR)),
    internals := mod1.internals.map liftL' ++ mod2.internals.map liftR',
    init_state := λ (s, s') => mod1.init_state s ∧ mod2.init_state s',
  }

@[drunfold]
def productD {α} {l₁ l₂ : List α} {f} (mod1 : Module Ident (HVector f l₁)) (mod2: Module Ident (HVector f l₂)) : Module Ident (HVector f (l₁ ++ l₂)) :=
  {
    inputs := (mod1.inputs.mapVal (λ _ => liftLD)).append (mod2.inputs.mapVal (λ _ => liftRD)),
    outputs := (mod1.outputs.mapVal (λ _ => liftLD)).append (mod2.outputs.mapVal (λ _ => liftRD)),
    internals := mod1.internals.map liftLD' ++ mod2.internals.map liftRD'
    init_state := sorry -- TODO
  }

@[drunfold]
def liftD {α} {e : α} {f} (mod : Module Ident (f e)) : Module Ident (HVector f [e]) :=
  {
    inputs := mod.inputs.mapVal λ _ => liftSingle,
    outputs := mod.outputs.mapVal λ _ => liftSingle,
    internals := mod.internals.map liftSingle'
    init_state := sorry -- TODO
  }

@[drunfold]
def mapInputPorts {S} (mod : Module Ident S) (f : InternalPort Ident → InternalPort Ident) : Module Ident S :=
  { mod with inputs := mod.inputs.mapKey f }

@[drunfold]
def mapOutputPorts {S} (mod : Module Ident S) (f : InternalPort Ident → InternalPort Ident) : Module Ident S :=
  { mod with outputs := mod.outputs.mapKey f }

@[drunfold]
def mapPorts {S} (mod : Module Ident S) (f : InternalPort Ident → InternalPort Ident) : Module Ident S :=
  mod.mapInputPorts f |>.mapOutputPorts f

@[drunfold]
def mapPorts2 {S} (mod : Module Ident S) (f g : InternalPort Ident → InternalPort Ident) : Module Ident S :=
  mod.mapInputPorts f |>.mapOutputPorts g

-- #eval (bijectivePortRenaming (Ident := Nat) [(⟨.top, 1⟩, ⟨.top, 2⟩), (⟨.top, 4⟩, ⟨.top, 3⟩)].toAssocList) ⟨.top, 3⟩

def renamePorts {S} (m : Module Ident S) (p : PortMapping Ident) : Module Ident S :=
  m.mapPorts2 p.input.bijectivePortRenaming p.output.bijectivePortRenaming

theorem renamePorts_EqExt {S} (m : Module Ident S) (p p' : PortMapping Ident) :
  p.wf → p'.wf →
  p.EqExt p' →
  m.renamePorts p = m.renamePorts p' := by
  unfold Module.renamePorts
  intro ⟨hwf1, hwf2⟩ ⟨hwf1', hwf2'⟩ ⟨Heq1, Heq2⟩
  simp [*, AssocList.bijectivePortRenaming_EqExt (p' := p'.input), AssocList.bijectivePortRenaming_EqExt (p' := p'.output)]

theorem sigma_cast {α} {f : α → Type _} {x y : Sigma f} (h : x = y) :
  f x.fst = f y.fst := by subst x; rfl

theorem sigma_cast' {α} {f : α → Type _} {x y : Sigma f} (h : x = y) :
  x.fst = y.fst := by subst x; rfl

theorem sigma_rw {α} {f : α → Type _} {x y : Sigma f} (h : x = y) :
  x.snd = (sigma_cast h).mpr y.snd := by subst x; rfl

theorem liftR_connect {S I} {a b : Σ T, S → T → S → Prop}:
  liftR' (S := I) (connect'' a.snd b.snd) = connect'' (liftR a).snd (liftR b).snd := by
  unfold liftR' connect'' liftR
  dsimp; ext s1 s2
  constructor <;> intro h
  · and_intros
    · intro hwf; have h' := h.1.1 hwf
      obtain ⟨consumed_output, output, ha, hb⟩ := h'
      exists (s2.fst, consumed_output), output
      simp [*]
    · grind
  · grind

theorem comm_conn_product_EqExt {I S} {m₁ : Module Ident I} {m₂ : Module Ident S} {o i}:
  ¬ (m₁.outputs.contains o) → ¬ (m₁.inputs.contains i) →
  (m₁.product (m₂.connect' o i)).EqExt ((m₁.product m₂).connect' o i) := by
  intro hcont1 hcont2
  and_intros
  · intro i'; dsimp [Module.connect', Module.product]
    rw [AssocList.eraseAll_map_comm]
    by_cases i = i'
    · subst i'
      rw [AssocList.append_find_right]
      · simp only [AssocList.find?_eraseAll_eq]
      · rw [← AssocList.find?_map_comm,AssocList.contains_none] <;> solve | rfl | assumption
    · rw [AssocList.eraseAll_append]
      rw (occs := [2]) [AssocList.eraseAll_not_contains]
      intro hneg; apply hcont2
      rw [←AssocList.contains_find?_iff]
      rw [←AssocList.contains_find?_iff] at hneg
      obtain ⟨v, hfind⟩ := hneg
      rw [AssocList.find?_mapVal] at hfind; simp only [Option.map_eq_some_iff] at hfind
      obtain ⟨a, hfind, hlift⟩ := hfind
      exists a
  · intro i'; dsimp [Module.connect', Module.product]
    rw [AssocList.eraseAll_map_comm]
    by_cases o = i'
    · subst i'
      rw [AssocList.append_find_right]
      · simp only [AssocList.find?_eraseAll_eq]
      · rw [← AssocList.find?_map_comm,AssocList.contains_none] <;> solve | rfl | assumption
    · rw [AssocList.eraseAll_append]
      rw (occs := [2]) [AssocList.eraseAll_not_contains]
      intro hneg; apply hcont1
      rw [←AssocList.contains_find?_iff]
      rw [←AssocList.contains_find?_iff] at hneg
      obtain ⟨v, hfind⟩ := hneg
      rw [AssocList.find?_mapVal] at hfind; simp only [Option.map_eq_some_iff] at hfind
      obtain ⟨a, hfind, hlift⟩ := hfind
      exists a
  · dsimp [product, connect']
    suffices hfrom :
      liftR' (connect'' (m₂.outputs.getIO o).snd (m₂.inputs.getIO i).snd)
      = connect''
          (PortMap.getIO (AssocList.mapVal (fun x => liftL) m₁.outputs ++ AssocList.mapVal (fun x => liftR) m₂.outputs)
              o).snd
          (PortMap.getIO (AssocList.mapVal (fun x => liftL) m₁.inputs ++ AssocList.mapVal (fun x => liftR) m₂.inputs)
              i).snd by simp [←hfrom]
    unfold PortMap.getIO
    repeat1' rw [AssocList.append_find_right]
    repeat1' rw [AssocList.find?_mapVal]
    have : ⟨PUnit.{1}, fun (x : I × S) x x => False⟩ = liftR ⟨PUnit.{1}, fun (x : S) x _ => False⟩ := by
      congr; simp
    have this' : (Option.map liftR (AssocList.find? o m₂.outputs)).getD ⟨PUnit.{1}, fun (x : I × S) x x => False⟩
                 = liftR ((AssocList.find? o m₂.outputs).getD ⟨PUnit.{1}, fun x x x => False⟩) := by
      rw [this, Option.getD_map]
    have this'' : (Option.map liftR (AssocList.find? i m₂.inputs)).getD ⟨PUnit.{1}, fun (x : I × S) x x => False⟩
                 = liftR ((AssocList.find? i m₂.inputs).getD ⟨PUnit.{1}, fun x x x => False⟩) := by
      rw [this, Option.getD_map]
    rw [this', this'']
    rw [liftR_connect]
    rw [AssocList.contains_none] <;> trivial
    rw [AssocList.contains_none] <;> trivial
  · simpa [connect', product]

theorem comm_conn_conn_EqExt {I} {m : Module Ident I} {o i o' i'}:
  o ≠ o' → i ≠ i' →
  ((m.connect' o' i').connect' o i).EqExt ((m.connect' o i).connect' o' i') := by
  intro hne1 hne2
  unfold EqExt connect'; and_intros
  · dsimp [AssocList.EqExt]; intro i''
    rw [AssocList.eraseAll_comm]
  · dsimp [AssocList.EqExt]; intro i''
    rw [AssocList.eraseAll_comm]
  · dsimp; unfold PortMap.getIO
    symm_saturate
    repeat1' (rw [AssocList.find?_eraseAll_neq] <;> try assumption)
    apply List.Perm.swap
  · simp

end

section

variable {Ident}
variable {S}

def toInterface (m : Module Ident S): Interface Ident :=
  ⟨m.inputs.keysList, m.outputs.keysList⟩

def toPortMapping (m : Module Ident S) (i : Ident) : PortMapping Ident :=
  m.toInterface.toPortMapping i

theorem mapInputPorts_id {m : Module Ident S} :
  m.mapInputPorts id = m := by
  unfold mapInputPorts
  rw [Batteries.AssocList.mapKey_toList]; simp

theorem mapOutputPorts_id {m : Module Ident S} :
  m.mapOutputPorts id = m := by
  unfold mapOutputPorts
  rw [Batteries.AssocList.mapKey_toList]; simp

variable [DecidableEq Ident]

theorem renamePorts_empty {m : Module Ident S} :
  m.renamePorts ∅ = m := by
  unfold renamePorts
  have i : (∅ : PortMapping Ident).input = ∅ := by rfl
  have o : (∅ : PortMapping Ident).output = ∅ := by rfl
  rw [i,o]
  rw [AssocList.bijectivePortRenaming_id]; unfold Module.mapPorts2; rw [mapInputPorts_id,mapOutputPorts_id]

@[drcomponents]
def mapIdent {Ident Ident' T} (inpR outR: Ident → Ident') (m : Module Ident T)
 : Module Ident' T :=
  {
    inputs := m.inputs.mapKey (InternalPort.map inpR),
    outputs := m.outputs.mapKey (InternalPort.map outR),
    internals := m.internals
    init_state := m.init_state
  }

end

end Module

instance {n} : OfNat (InstIdent Nat) n where
  ofNat := .internal n

instance {n} : OfNat (InternalPort Nat) n where
  ofNat := ⟨ .top, n ⟩

attribute [drnat] instOfNatInstIdentNat instOfNatInternalPortNat

abbrev NatModule := Module Nat

abbrev StringModule := Module String

@[drcomponents]
def NatModule.stringify_input (n : Nat) :=
  s!"in{n + 1}"

@[drcomponents]
def NatModule.stringify_output (n : Nat) :=
  s!"out{n + 1}"

@[drunfold, drcomponents]
def NatModule.stringify {T} (m : NatModule T) : StringModule T :=
  m |>.mapIdent stringify_input stringify_output

def IdentMap.toInterface {Ident} (i : IdentMap Ident (Σ T, Module Ident T))
  : IdentMap Ident (Interface Ident) :=
  i.mapVal (λ _ x => x.snd |>.toInterface)

abbrev TModule Ident := Σ T, Module Ident T
abbrev TModule1 Ident := Σ T : Type, Module Ident T

end Graphiti
