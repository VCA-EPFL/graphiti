/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Core.Module
import Graphiti.Core.Simp
import Graphiti.Core.ExprHigh
import Graphiti.Core.AssocList.Basic
import Graphiti.Core.TypeExpr
import Graphiti.Core.Environment
import Graphiti.Core.ExprHighElaborator

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

namespace Example

def gcd : ExprHigh String (String × Nat) := [graph|
    context [type = "inputContext", arg = 0];

    merge [type = "merge", arg = 0];
    l6rd [type = "rd", arg = 0];
    l6const [type = "constant", arg = 0];
    l6neq [type = "mod", arg = 0];
    l6cont [type = "fork2", arg = 0];
    l6 [type = "if", arg = 0];  -- if (x1 !=s 0) goto 5 else goto 2
    l5cont [type = "fork3", arg = 0];
    l5rdx2 [type = "rd", arg = 2];
    l5rdx1 [type = "rd", arg = 1];
    l5mod [type = "mod", arg = 0];
    l5 [type = "upd", arg = 3]; -- x3 = x2 %s x1
    l4cont [type = "fork2", arg = 0];
    l4rd [type = "rd", arg = 1];
    l4 [type = "upd", arg = 2]; -- x2 = x1
    l3cont [type = "fork2", arg = 0];
    l3rd [type = "rd", arg = 3];
    l3 [type = "upd", arg = 1]; -- x1 = x3; goto 6

    l1cont [type = "fork2", arg = 0];
    l1rdx2 [type = "rd", arg=2];
    l1 [type = "outputVal", arg=0]; -- return x2

    -- CFG
    context -> merge [from="O", to="I1"];
    merge -> l6cont [from="O", to="I"];
    l6 -> l5cont [from="true", to="I"];
    l6 -> l1cont [from="false", to="I"];

    l5 -> l4cont [from="O", to="I"];
    l4 -> l3cont [from="O", to="I"];
    l3 -> merge [from="O", to="I2"];

    -- DATA
    l6cont -> l6rd [from="O2", to="I"];
    l6cont -> l6 [from="O1", to="I"];
    l6rd -> l6neq [from="O", to="I1"];
    l6const -> l6neq [from="O", to="I2"];
    l6neq -> l6 [from="O", to="cond"];

    l5cont -> l5rdx2 [from="O3", to="I"];
    l5cont -> l5rdx1 [from="O2", to="I"];
    l5cont -> l5 [from="O1", to="I"];
    l5rdx2 -> l5mod [from="O", to="I1"];
    l5rdx1 -> l5mod [from="O", to="I2"];
    l5mod -> l5 [from="O", to="val"];

    l4cont -> l4rd [from="O2", to="I"];
    l4cont -> l4 [from="O1", to="I"];
    l4rd -> l4 [from="O", to="val"];

    l3cont -> l3rd [from="O2", to="I"];
    l3cont -> l3 [from="O1", to="I"];
    l3rd -> l3 [from="O", to="val"];

    l1cont -> l1 [from="O1", to="I"];
    l1cont -> l1rdx2 [from="O2", to="I"];
    l1rdx2 -> l1 [from="O", to="val"];
  ]

#eval IO.println <| toString gcd

end Example

end Graphiti.CombModule
