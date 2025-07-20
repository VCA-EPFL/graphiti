/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Module
import Graphiti.Simp
import Graphiti.ExprHigh
import Graphiti.AssocList.Basic
import Graphiti.TypeExpr
import Graphiti.Environment

open Batteries (AssocList)

namespace Graphiti.CombModule

@[simp] abbrev Val := Nat
@[simp] abbrev Reg := Nat
@[simp] abbrev Node := Nat

structure Context where
  memory : AssocList Reg Val
  deriving Inhabited

def update_loc (loc: Reg) (val: Val) (c: Context) : Context :=
  ⟨c.memory.cons loc val⟩

inductive Aexp where
| lit : Val → Aexp
| var : Reg → Aexp
| add : Aexp → Aexp → Aexp

inductive Bexp where
| true : Bexp
| false : Bexp
| eq : Aexp → Aexp → Bexp
| lt : Aexp → Aexp → Bexp
| and : Bexp → Bexp → Bexp
| or : Bexp → Bexp → Bexp
| not : Bexp → Bexp

inductive Instr where
| skip : Node → Instr
| assign : Reg → Aexp → Node → Instr
| cond : Bexp → Node → Node → Instr
| ret : Option Reg → Instr

namespace Semantics

inductive Aexp.sem : Context → Aexp → Val → Prop where
  | lit {c n} : Aexp.sem c (Aexp.lit n) n
  | var {c y r} : c.memory.find? r = some y → Aexp.sem c (Aexp.var r) y
  | add {c a v b v'} : Aexp.sem c a v → Aexp.sem c b v' → Aexp.sem c (Aexp.add a b) (v + v')

inductive Bexp.sem : Context → Bexp → Bool → Prop where
  | true {c} : Bexp.sem c Bexp.true Bool.true
  | false {c} : Bexp.sem c Bexp.false Bool.false
  | eq {c a v b v'} : Aexp.sem c a v → Aexp.sem c b v' → Bexp.sem c (Bexp.eq a b) (v = v')
  | lt {c a v b v'} : Aexp.sem c a v → Aexp.sem c b v' → Bexp.sem c (Bexp.lt a b) (v < v')
  | and {c a v b v'} : Bexp.sem c a v → Bexp.sem c b v' → Bexp.sem c (Bexp.and a b) (v && v')
  | or {c a v b v'} : Bexp.sem c a v → Bexp.sem c b v' → Bexp.sem c (Bexp.or a b) (v || v')
  | not {c a v} : Bexp.sem c a v → Bexp.sem c (Bexp.not a) (¬ v)

inductive State where
| state
  (pc : Node)
  (env : AssocList Node Instr)
  (context : Context) : State
| ret
  (v : Option Val) : State

inductive Instr.sem : State → State → Prop where
  | skip {c n pc env} :
    env.find? pc = .some (Instr.skip n) →
    Instr.sem (.state pc env c) (.state n env c)
  | assign {c e v r n pc env} :
    env.find? pc = .some (Instr.assign r e n) →
    Aexp.sem c e v →
    Instr.sem (.state pc env c) (.state n env (update_loc r v c))
  | cond_true {c b t f env pc} :
    env.find? pc = .some (Instr.cond b t f) →
    Bexp.sem c b true →
    Instr.sem (.state pc env c) (.state t env c)
  | cond_false {c b t f env pc} :
    env.find? pc = .some (Instr.cond b t f) →
    Bexp.sem c b false →
    Instr.sem (.state pc env c) (.state f env c)
  | ret {pc env c v} :
    env.find? pc = .some (Instr.ret v) →
    Instr.sem (.state pc env c) (.ret v)

end Semantics

namespace Denotation

def moduleGen (f : Context → Option Context) : StringModule (Option Context) :=
  NatModule.stringify {
    inputs := [(0, ⟨ Context, fun
      | .none, s, .some c' => f s = .some c'
      | _, _, _ => False ⟩)].toAssocList,
    outputs := [(0, ⟨ Context, fun
      | .some c, s, .none => s = c
      | _, _, _ => False ⟩)].toAssocList,
    init_state := λ s => s = default
  }

end Denotation

end Graphiti.CombModule
