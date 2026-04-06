/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Core.Graph.ModuleLemmas
import Graphiti.Core.Graph.ModuleReduction
import Graphiti.Core.Simp
import Graphiti.Core.Graph.ExprHighElaborator
import Graphiti.Core.AssocList.Basic
import Graphiti.Core.Netlist.VerilogExport

open Batteries (AssocList)

namespace Graphiti.CombModule

def Stream α := Option (List α)

namespace Stream

def empty {α} : Stream α := some []

instance {α} : Inhabited (Stream α) := ⟨empty⟩

def map {α β} (f : α → β) (s : Stream α) : Stream β := Option.map (·.map f) s

def map2 {α β γ} (f : α → β → γ) (s1 : Stream α) (s2 : Stream β) : Stream γ :=
  match s1, s2 with
  | some s1, some s2 => some <| (s1.zip s2).map (fun (a, b) => f a b)
  | _, _ => none

def map3 {α β γ σ} (f : α → β → γ → σ) (s1 : Stream α) (s2 : Stream β) (s3 : Stream γ) : Stream σ :=
  match s1, s2, s3 with
  | some s1, some s2, some s3 => some <| (s1.zip (s2.zip s3)).map (fun (a, b, c) => f a b c)
  | _, _, _ => none

variable {α : Type _}

def more_defined (s1 s2 : Stream α) : Prop :=
  ∃ s1' s2', s1 = some s1' ∧ s2 = some s2' ∧ s1'.length > s2'.length ∧ s1'.take (s2'.length) = s2'

def delay (d : α) (s : Stream α) : Stream α :=
  Option.map (d :: ·) s

def delayN (d : List α) (s : Stream α) : Stream α :=
  Option.map (d ++ ·) s

def not (s : Stream Bool) : Stream Bool := s.map (!·)

def and (s1 s2 : Stream Bool) : Stream Bool :=
  map2 (λ a b => a && b) s1 s2

def xor (s1 s2 : Stream Bool) : Stream Bool :=
  map2 (λ a b => Bool.xor a b) s1 s2

def or (s1 s2 : Stream Bool) : Stream Bool :=
  map2 (λ a b => Bool.or a b) s1 s2

def xor3 (s1 s2 s3 : Stream Bool) : Stream Bool :=
  map3 (λ a b c => Bool.xor (Bool.xor a b) c) s1 s2 s3

def and3 (s1 s2 s3 : Stream Bool) : Stream Bool :=
  map3 (λ a b c => a && b && c) s1 s2 s3

def nand (s1 s2 : Stream Bool) : Stream Bool := not <| and s1 s2

def nand3 (s1 s2 s3 : Stream Bool) : Stream Bool := not <| and3 s1 s2 s3

end Stream

-- We thought we needed a top and bot value for streams, essentially operating on 4-valued logic.  However, we do not
-- need a top-value, because we don't have to signal any errors when two streams do not agree.  Instead, we block the
-- execution of the module if the streams do not agree.
-- For the same reason, we also do not need a bot value, because if we cannot define the result at some point, then we
-- can also block.
-- Also, I think we need integers instead of natural numbers for the domain, so that you have all the future and the
-- past values that you will ever get.  If you end up caring only about the past values, then maybe you can use naturals
-- again.

-- We are adding back a bot value (none) because it makes it easier to keep track of the most recent value that was
-- generated.
abbrev D := Stream Bool

open Stream
open VerilogExport

abbrev Named (s : String) (T : Type _) := T

def not_m : NatModule D :=
  { inputs := [(0, ⟨ D, λ s tt s' => more_defined tt s ∧ s' = tt ⟩)].toAssocList,
    outputs := [(0, ⟨ D, λ s tt s' => s = s' ∧ not (delay false s) = tt⟩)].toAssocList
    init_state := λ s => s = default
  }

def not_m_template : VerilogTemplate where
  module := build_local_module "not_m" (simple_interface ["in1"] ["out1"]) "assign #1 out1 = ~ in1;"
  instantiation name inst := format_instantiation "not_m" name inst

def sink_m : NatModule Unit :=
  { inputs := [(0, ⟨ D, λ s tt s' => True ⟩)].toAssocList,
    outputs := ∅
    init_state := λ s => s = default
  }

def sink_m_template : VerilogTemplate where
  module := build_local_module "sink_m" (simple_interface ["in1"] []) ""
  instantiation name inst := format_instantiation "sink_m" name inst

def nand_m (s : String) : NatModule (Named s (D × D)) :=
  { inputs := [(0, ⟨ Named s!"{s}.in1" D, λ s tt s' => more_defined tt s.1 ∧ s'.1 = tt ∧ s'.2 = s.2 ⟩),
               (1, ⟨ Named s!"{s}.in2" D, λ s tt s' => more_defined tt s.2 ∧ s'.2 = tt ∧ s'.1 = s.1 ⟩)].toAssocList,
    outputs := [(0, ⟨ Named s!"{s}.out1" D, λ s tt s' => s = s' ∧ tt = delay false (nand s.1 s.2) ⟩)].toAssocList
    init_state := λ s => s = default
  }

def nand_m_template : VerilogTemplate where
  module := build_local_module "nand_m" (simple_interface ["in1", "in2"] ["out1"]) "assign #1 out1 = ~ (in1 & in2);"
  instantiation name inst := format_instantiation "nand_m" name inst

def nand3_m : NatModule (D × D × D) :=
  { inputs := [(0, ⟨ D, λ s tt s' => more_defined tt s.1 ∧ s'.1 = tt ∧ s'.2 = s.2 ⟩),
               (1, ⟨ D, λ s tt s' => more_defined tt s.2.1 ∧ s'.2.1 = tt ∧ s'.1 = s.1 ∧ s'.2.2 = s.2.2 ⟩),
               (2, ⟨ D, λ s tt s' => more_defined tt s.2.2 ∧ s'.2.2 = tt ∧ s'.1 = s.1 ∧ s'.2.1 = s.2.1 ⟩)].toAssocList,
    outputs := [(0, ⟨ D, λ s tt s' => s = s' ∧ tt = delay false (nand3 s.1 s.2.1 s.2.2) ⟩)].toAssocList
    init_state := λ s => s = default
  }

def nand3_m_template : VerilogTemplate where
  module := build_local_module "nand3_m" (simple_interface ["in1", "in2", "in3"] ["out1"]) "assign #1 out1 = ~ (in1 & in2 & in3);"
  instantiation name inst := format_instantiation "nand3_m" name inst

def and_m : NatModule (D × D) :=
  { inputs := [(0, ⟨ D, λ s tt s' => more_defined tt s.1 ∧ s'.1 = tt ∧ s'.2 = s.2 ⟩),
               (1, ⟨ D, λ s tt s' => more_defined tt s.2 ∧ s'.2 = tt ∧ s'.1 = s.1 ⟩)].toAssocList,
    outputs := [(0, ⟨ D, λ s tt s' => s = s' ∧ tt = delay false (nand s.1 s.2) ⟩)].toAssocList
    init_state := λ s => s = default
  }

def and_m_template : VerilogTemplate where
  module := build_local_module "and_m" (simple_interface ["in1", "in2"] ["out1"]) "assign #1 out1 = in1 & in2;"
  instantiation name inst := format_instantiation "and_m" name inst

def fork_m (s : String) : NatModule (Named s D) :=
  { inputs := [(0, ⟨ Named s!"{s}.in1" D, λ s tt s' => more_defined tt s ∧ s' = tt ⟩)].toAssocList,
    outputs := [(0, ⟨ Named s!"{s}.out1" D, λ s tt s' => s = s' ∧ tt = s ⟩), (1, ⟨ Named s!"{s}.out2" D, λ s tt s' => s = s' ∧ tt = s ⟩)].toAssocList
    init_state := λ s => s = default
  }

def fork_m_template : VerilogTemplate where
  module := build_local_module "fork_m" (simple_interface ["in1"] ["out1", "out2"]) "assign out1 = in1;\nassign out2 = in1;"
  instantiation name inst := format_instantiation "fork_m" name inst

def fork3_m : NatModule D :=
  { inputs := [(0, ⟨ D, λ s tt s' => more_defined tt s ∧ s' = tt ⟩)].toAssocList,
    outputs := [(0, ⟨ D, λ s tt s' => s = s' ∧ tt = s ⟩), (1, ⟨ D, λ s tt s' => s = s' ∧ tt = s ⟩), (2, ⟨ D, λ s tt s' => s = s' ∧ tt = s ⟩)].toAssocList
    init_state := λ s => s = default
  }

def fork3_m_template : VerilogTemplate where
  module := build_local_module "fork3_m" (simple_interface ["in1"] ["out1", "out2", "out3"]) "assign out1 = in1;\nassign out2 = in1;\nassign out3 = in1;"
  instantiation name inst := format_instantiation "fork3_m" name inst

def not_sm := not_m.stringify
def sink_sm := sink_m.stringify
def and_sm := and_m.stringify
def nand_sm (s : String := "") := (nand_m s).stringify
def nand3_sm := nand3_m.stringify
def fork_sm (s : String := "") := (fork_m s).stringify
def fork3_sm := fork3_m.stringify

def env : IdentMap String VerilogTemplate :=
  [("sink_m", sink_m_template), ("and_m", and_m_template), ("nand_m", nand_m_template), ("nand3_m", nand3_m_template), ("fork_m", fork_m_template), ("fork3_m", fork3_m_template), ("not_m", not_m_template)].toAssocList

namespace FlipFlop

def d_latch'_m := [graphEnv|
    d [type="io"];
    clk [type="io"];
    q [type="io"];
    q_bar [type="io"];

    n1 [type="nand_m", typeImp=$(⟨_, nand_sm⟩)];
    n2 [type="nand_m", typeImp=$(⟨_, nand_sm⟩)];
    n3 [type="nand_m", typeImp=$(⟨_, nand_sm⟩)];
    n4 [type="nand_m", typeImp=$(⟨_, nand_sm⟩)];

    d_2 [type="fork_m", typeImp=$(⟨_, fork_sm⟩)];
    clk_2 [type="fork_m", typeImp=$(⟨_, fork_sm⟩)];
    n3_2 [type="fork_m", typeImp=$(⟨_, fork_sm⟩)];
    n4_2 [type="fork_m", typeImp=$(⟨_, fork_sm⟩)];

    not1 [type="not_m", typeImp=$(⟨_, not_sm⟩)];

    d -> d_2 [to="in1"];
    d_2 -> n1 [from="out1",to="in1"];
    d_2 -> not1 [from="out2",to="in1"];

    clk -> clk_2 [to="in1"];
    clk_2 -> n1 [from="out1",to="in2"];
    clk_2 -> n2 [from="out2",to="in2"];

    not1 -> n2 [from="out1",to="in1"];

    n1 -> n3 [from="out1",to="in1"];
    n2 -> n4 [from="out1",to="in2"];

    n3 -> n3_2 [from="out1",to="in1"];

    n4 -> n4_2 [from="out1",to="in1"];

    n3_2 -> n4 [from="out2",to="in1"];
    n3_2 -> q [from="out1"];

    n4_2 -> n3 [from="out1",to="in2"];
    n4_2 -> q_bar [from="out2"];
  ]

def d_latch_m := [graphEnv|
    d [type="io"];
    clk [type="io"];
    q [type="io"];
    q_bar [type="io"];

    n1 [type="nand_m", typeImp=$(⟨_, nand_sm⟩)];
    n2 [type="nand_m", typeImp=$(⟨_, nand_sm⟩)];
    n3 [type="nand_m", typeImp=$(⟨_, nand_sm⟩)];
    n4 [type="nand_m", typeImp=$(⟨_, nand_sm⟩)];

    clk_2 [type="fork_m", typeImp=$(⟨_, fork_sm⟩)];
    n3_2 [type="fork_m", typeImp=$(⟨_, fork_sm⟩)];
    n4_2 [type="fork_m", typeImp=$(⟨_, fork_sm⟩)];
    n1_2 [type="fork_m", typeImp=$(⟨_, fork_sm⟩)];

    d -> n1 [to="in1"];

    n1 -> n1_2 [from="out1", to="in1"];

    clk -> clk_2 [to="in1"];
    clk_2 -> n1 [from="out1",to="in2"];
    clk_2 -> n2 [from="out2",to="in2"];

    n1_2 -> n2 [from="out2",to="in1"];

    n1_2 -> n3 [from="out1",to="in1"];
    n2 -> n4 [from="out1",to="in2"];

    n3 -> n3_2 [from="out1",to="in1"];

    n4 -> n4_2 [from="out1",to="in1"];

    n3_2 -> n4 [from="out2",to="in1"];
    n3_2 -> q [from="out1"];

    n4_2 -> n3 [from="out1",to="in2"];
    n4_2 -> q_bar [from="out2"];
  ]

def d_latch_m_template : VerilogTemplate where
  module := build_local_module "d_latch_m" (simple_interface ["d", "clk"] ["q", "q_bar"]) ((build_verilog_body env d_latch_m.1).get rfl)
  instantiation name inst := format_instantiation "d_latch_m" name inst

def et_flip_flop_m := [graphEnv|
    clk [type="io"];
    d [type="io"];
    q [type="io"];
    q_bar [type="io"];

    n1 [type="nand_m1", typeImp = $(⟨_, nand_sm "nand1"⟩)];
    n2 [type="nand_m2", typeImp = $(⟨_, nand_sm "nand2"⟩)];
    n3 [type="nand3_m", typeImp = $(⟨_, nand3_sm⟩)];
    n4 [type="nand_m3", typeImp = $(⟨_, nand_sm "nand3"⟩)];
    n5 [type="nand_m4", typeImp = $(⟨_, nand_sm "nand4"⟩)];
    n6 [type="nand_m5", typeImp = $(⟨_, nand_sm "nand5"⟩)];

    clkF [type="clkF", typeImp = $(⟨_, fork_sm "clkF"⟩)];
    n2F [type="fork3_m", typeImp = $(⟨_, fork3_sm⟩)];
    n3F [type="n3_f", typeImp = $(⟨_, fork_sm "n3_f"⟩)];
    n4F [type="n4_f", typeImp = $(⟨_, fork_sm "n4_f"⟩)];
    n5F [type="n5_f", typeImp = $(⟨_, fork_sm "n5_f"⟩)];
    n6F [type="n6_f", typeImp = $(⟨_, fork_sm "n6_f"⟩)];

    n2 -> n2F [from="out1", to="in1"];
    n3 -> n3F [from="out1", to="in1"];
    n4 -> n4F [from="out1", to="in1"];

    n5 -> n5F [from="out1", to="in1"];
    n6 -> n6F [from="out1", to="in1"];

    clk -> clkF [to="in1"];

    d -> n4 [to="in2"];
    clkF -> n2 [from="out1", to="in2"];
    clkF -> n3 [from="out2", to="in2"];

    n1 -> n2 [from="out1", to="in1"];

    n2F -> n1 [from="out1", to="in2"];
    n2F -> n5 [from="out2", to="in1"];
    n2F -> n3 [from="out3", to="in1"];

    n3F -> n4 [from="out2", to="in1"];
    n3F -> n6 [from="out1", to="in2"];

    n4F -> n3 [from="out2", to="in3"];
    n4F -> n1 [from="out1", to="in1"];

    n5F -> n6 [from="out2", to="in1"];
    n6F -> n5 [from="out1", to="in2"];

    n5F -> q [from="out1"];
    n6F -> q_bar [from="out2"];
  ]

#check ExprHigh
#eval repr <| et_flip_flop_m.1
#eval repr <| et_flip_flop_m.2.toList.map Prod.fst

def env' := env.cons "d_latch_m" d_latch_m_template

def et_flip_flop_spec : StringModule (D × D) :=
  { inputs := [ (↑"clk", ⟨ D, λ s tt s' => True ⟩)
              , (↑"d", ⟨ D, λ s tt s' => True ⟩)].toAssocList,
    outputs := [ (↑"q", ⟨ D, λ s tt s' => True ⟩)
               , (↑"q_bar", ⟨ D, λ s tt s' => True ⟩)].toAssocList,
    init_state := λ s => s = default
  }

def et_ms_flip_flop_m := [graphEnv|
    clk [type="io"];
    d [type="io"];
    q [type="io"];
    q_bar [type="io"];

    latch1 [type="d_latch_m", typeImp=$(ExprHigh.build_module d_latch_m.2.find? d_latch_m.1)];
    latch2 [type="d_latch_m", typeImp=$(ExprHigh.build_module d_latch_m.2.find? d_latch_m.1)];
    sink [type="sink_m", typeImp=$(⟨_, sink_sm⟩)];

    n1 [type="not_m", typeImp=$(⟨_, not_sm⟩)];
    n1F [type="fork_m", typeImp=$(⟨_, fork_sm⟩)];
    n2 [type="not_m", typeImp=$(⟨_, not_sm⟩)];

    d -> latch1 [to="d"];
    clk -> n1 [to="in1"];

    n1 -> n1F [from="out1", to="in1"];
    n1F -> latch1 [from="out1", to="clk"];
    n1F -> latch2 [from="out2", to="clk"];

    latch1 -> latch2 [from="q", to="d"];
    latch1 -> sink [from="q_bar", to="in1"];

    latch2 -> q [from="q"];
    latch2 -> q_bar [from="q_bar"];
  ]

#eval IO.print <| build_verilog_module "d_latch_m" env d_latch_m.1 (simple_interface ["d", "clk"] ["q", "q_bar"])
#guard_msgs (drop info) in
#eval IO.print <| build_verilog_module "et_flip_flop_m" env et_flip_flop_m.1 (simple_interface ["d", "clk"] ["q", "q_bar"])
#guard_msgs (drop info) in
#eval IO.print <| build_verilog_module "et_ms_flip_flop_m" env' et_ms_flip_flop_m.1 (simple_interface ["d", "clk"] ["q", "q_bar"])

namespace Refinement

def et_flip_flop_m_lowered := et_flip_flop_m.1.lower_TR |>.get rfl

#eval et_flip_flop_m_lowered
#check ExprLow

def env := (et_flip_flop_m).2

@[drenv] theorem find?_nand1_m : (Batteries.AssocList.find? "nand_m1" env) = .some ⟨_, nand_sm "nand1"⟩ := rfl
@[drenv] theorem find?_nand2_m : (Batteries.AssocList.find? "nand_m2" env) = .some ⟨_, nand_sm "nand2"⟩ := rfl
@[drenv] theorem find?_nand3_m : (Batteries.AssocList.find? "nand_m3" env) = .some ⟨_, nand_sm "nand3"⟩ := rfl
@[drenv] theorem find?_nand4_m : (Batteries.AssocList.find? "nand_m4" env) = .some ⟨_, nand_sm "nand4"⟩ := rfl
@[drenv] theorem find?_nand5_m : (Batteries.AssocList.find? "nand_m5" env) = .some ⟨_, nand_sm "nand5"⟩ := rfl
@[drenv] theorem find?_nand_3_m : (Batteries.AssocList.find? "nand3_m" env) = .some ⟨_, nand3_sm⟩ := rfl
@[drenv] theorem find?_clkF_m : (Batteries.AssocList.find? "clkF" env) = .some ⟨_, fork_sm "clkF"⟩ := rfl
@[drenv] theorem find?_n3_f_m : (Batteries.AssocList.find? "n3_f" env) = .some ⟨_, fork_sm "n3_f"⟩ := rfl
@[drenv] theorem find?_n4_f_m : (Batteries.AssocList.find? "n4_f" env) = .some ⟨_, fork_sm "n4_f"⟩ := rfl
@[drenv] theorem find?_n5_f_m : (Batteries.AssocList.find? "n5_f" env) = .some ⟨_, fork_sm "n5_f"⟩ := rfl
@[drenv] theorem find?_n6_f_m : (Batteries.AssocList.find? "n6_f" env) = .some ⟨_, fork_sm "n6_f"⟩ := rfl
-- @[drenv] theorem find?_fork_m : (Batteries.AssocList.find? "fork_m" env) = .some ⟨_, fork_sm⟩ := rfl
@[drenv] theorem find?_fork3_m : (Batteries.AssocList.find? "fork3_m" env) = .some ⟨_, fork3_sm⟩ := rfl

seal env in
def_module lhsModuleType : Type :=
  [T| et_flip_flop_m_lowered, env.find? ]
reduction_by
  dsimp [et_flip_flop_m_lowered]
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
  simp only [drenv]
  dsimp

seal env in
def_module lhsModule : StringModule lhsModuleType :=
  [e| et_flip_flop_m_lowered, env.find? ]
reduction_by
       dsimp [et_flip_flop_m_lowered]
       (dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
        dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
        dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
        rw [rw_opaque (by simp only [drenv]; rfl)]; dsimp
        dsimp [Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts, Module.mapInputPorts, reduceAssocListfind?]
        simp (disch := decide) only [AssocList.bijectivePortRenaming_invert]
        dsimp [Module.product]
        dsimp only [reduceModuleconnect'2]
        dsimp only [reduceEraseAll]
        dsimp; dsimp [reduceAssocListfind?]

        unfold Module.connect''
        dsimp [toString]
        )
        /- dsimp [Module.liftL, Module.liftR, drcomponents]) -/

instance : MatchInterface lhsModule et_flip_flop_spec := by
  dsimp [lhsModule, et_flip_flop_spec]
  solve_match_interface
def φ : lhsModuleType → (D × D) → Prop :=
  λ (_, _, _, _, (_, dataL), _, _, _, _, clkL, _) (clk, data) =>
    -- First, extract the state
    dataL = data /\ clkL = clk
    -- Second, invariants
    -- Non-mathematically, our current ideas are the following two invariants:
    -- 1: the output state is at most the length of the input + delay
    -- 2: the function defined by the input is more defined than the output

theorem refines' :
  lhsModule ⊑_{φ} et_flip_flop_spec := by
    intro lhsModule rhsModule inv
    unfold φ at inv
    let (n2, n4, n5, n4_f, (n3i1, dataL), n3_f, n6_f, n1, n3_1, clkL, n5_f) := lhsModule
    let (clk, data) := rhsModule
    clear lhsModule rhsModule
    simp at inv
    apply Module.comp_refines.mk
    . -- Inputs
      intros inport targetLhs invalue h
      /- unfold lhsModuleType at lhsState -/
      sorry
    . -- Outputs
      sorry
    . -- Internals
      sorry

theorem refines :
  lhsModule ⊑ et_flip_flop_spec := by sorry

end Refinement

end FlipFlop

namespace HalfAdder

/--
Equivalent to just xor.
-/
def half_adder_s := [graphEnv|
    a [type="io"];
    b [type="io"];
    s [type="io"];

    n1 [type="nand_m_1", typeImp=$(⟨_, nand_sm "nand_1"⟩)];
    n2 [type="nand_m_2", typeImp=$(⟨_, nand_sm "nand_2"⟩)];
    n3 [type="nand_m_3", typeImp=$(⟨_, nand_sm "nand_3"⟩)];
    n4 [type="nand_m_4", typeImp=$(⟨_, nand_sm "nand_4"⟩)];

    a_f [type="fork_m_1", typeImp=$(⟨_, fork_sm "a_f"⟩)];
    b_f [type="fork_m_2", typeImp=$(⟨_, fork_sm "b_f"⟩)];
    n1_f [type="fork_m_3", typeImp=$(⟨_, fork_sm "n1_f"⟩)];

    a -> a_f [to="in1"];
    b -> b_f [to="in1"];
    n1 -> n1_f [from="out1",to="in1"];

    a_f -> n1 [from="out2",to="in1"];
    b_f -> n1 [from="out1",to="in2"];
    a_f -> n2 [from="out1",to="in1"];
    b_f -> n3 [from="out2",to="in2"];

    n1_f -> n2 [from="out1",to="in2"];
    n1_f -> n3 [from="out2",to="in1"];

    n2 -> n4 [from="out1",to="in1"];
    n3 -> n4 [from="out1",to="in2"];

    n4 -> s [from="out1"];
  ]

def half_adder_s_lowered := half_adder_s.1.lower_TR |>.get rfl

def xor_with_delay : StringModule (D × D) where
  inputs := [ (↑"a", ⟨ D, λ s tt s' => more_defined tt s.1 ∧ s'.1 = tt ∧ s'.2 = s.2 ⟩)
            , (↑"b", ⟨ D, λ s tt s' => more_defined tt s.2 ∧ s'.2 = tt ∧ s'.1 = s.1 ⟩)
            ].toAssocList
  outputs := [ (↑"s", ⟨ D, λ s tt s' => tt = delayN [false, false, false, false] (s.1.xor s.2) ∧ s = s' ⟩)].toAssocList
  internals := []
  init_state s := s = (.some [], .some [])

def env := half_adder_s.2

@[drenv] theorem find?_nand1_m : (Batteries.AssocList.find? "nand_m_1" env) = .some ⟨_, nand_sm "nand_1"⟩ := rfl
@[drenv] theorem find?_nand2_m : (Batteries.AssocList.find? "nand_m_2" env) = .some ⟨_, nand_sm "nand_2"⟩ := rfl
@[drenv] theorem find?_nand3_m : (Batteries.AssocList.find? "nand_m_3" env) = .some ⟨_, nand_sm "nand_3"⟩ := rfl
@[drenv] theorem find?_nand4_m : (Batteries.AssocList.find? "nand_m_4" env) = .some ⟨_, nand_sm "nand_4"⟩ := rfl
@[drenv] theorem find?_fork1_m : (Batteries.AssocList.find? "fork_m_1" env) = .some ⟨_, fork_sm "a_f"⟩ := rfl
@[drenv] theorem find?_fork2_m : (Batteries.AssocList.find? "fork_m_2" env) = .some ⟨_, fork_sm "b_f"⟩ := rfl
@[drenv] theorem find?_fork3_m : (Batteries.AssocList.find? "fork_m_3" env) = .some ⟨_, fork_sm "n1_f"⟩ := rfl

seal env in
def_module half_adder_m_t : Type :=
  [T| half_adder_s_lowered, env.find? ]
reduction_by
  dsimp [half_adder_s_lowered]
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
  simp only [drenv]
  dsimp

seal env in
def_module half_adder_m : StringModule half_adder_m_t :=
  [e| half_adder_s_lowered, env.find? ]
reduction_by
       dsimp [half_adder_s_lowered]
       (dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
        dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
        dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
        rw [rw_opaque (by simp only [drenv]; rfl)]; dsimp
        dsimp [Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts, Module.mapInputPorts, reduceAssocListfind?]
        simp (disch := decide) only [AssocList.bijectivePortRenaming_invert]
        dsimp [Module.product]
        dsimp only [reduceModuleconnect'2]
        dsimp only [reduceEraseAll]
        dsimp; dsimp [reduceAssocListfind?]

        unfold Module.connect''
        dsimp [toString]
        )

instance : MatchInterface half_adder_m xor_with_delay := by
  dsimp [half_adder_m, xor_with_delay]
  solve_match_interface

axiom φ : half_adder_m_t → (D × D) → Prop

theorem refines' :
  half_adder_m ⊑_{φ} xor_with_delay := by sorry

theorem refines :
  half_adder_m ⊑ xor_with_delay := by sorry

end HalfAdder

namespace FullAdder

def half_adder_m (s : String := "") : StringModule (Named s (D × D)) :=
  { inputs := [(↑"a", ⟨ Named s!"{s}.a" D, λ s tt s' => more_defined tt s.1 ∧ s'.1 = tt ∧ s'.2 = s.2 ⟩),
               (↑"b", ⟨ Named s!"{s}.b" D, λ s tt s' => more_defined tt s.2 ∧ s'.2 = tt ∧ s'.1 = s.1 ⟩)].toAssocList,
    outputs := [ (↑"s", ⟨ Named s!"{s}.s" D, λ s tt s' => s = s' ∧ tt = delay false (xor s.1 s.2) ⟩)
               , (↑"c", ⟨ Named s!"{s}.c" D, λ s tt s' => s = s' ∧ tt = delay false (and s.1 s.2) ⟩)].toAssocList
    init_state := λ s => s = default
  }

def or_m (s : String := "") : StringModule (D × D) :=
  { inputs := [(↑"a", ⟨ D, λ s tt s' => more_defined tt s.1 ∧ s'.1 = tt ∧ s'.2 = s.2 ⟩),
               (↑"b", ⟨ D, λ s tt s' => more_defined tt s.2 ∧ s'.2 = tt ∧ s'.1 = s.1 ⟩)].toAssocList,
    outputs := [(↑"c", ⟨ D, λ s tt s' => s = s' ∧ tt = delay false (and s.1 s.2) ⟩)].toAssocList
    init_state := λ s => s = default
  }

def adcb (a b c : D) : D × D :=
  (map3 (fun x y z => (BitVec.adcb x y z).1) a b c, map3 (fun x y z => (BitVec.adcb x y z).2) a b c)

-- TODO: delay is not completely correct. Most intuitively, s is stable two ticks after *the last change*, not after any change.
-- similarly, cout is stable 3 ticks after the last change. However, implementing this is currently messy.
def full_adder_spec_m (s : String := "") : StringModule (Named s (D × D × D)) :=
  { inputs := [(↑"a", ⟨ Named s!"{s}.a" D, λ s tt s' => more_defined tt s.1 ∧ s'.1 = tt ∧ s'.2 = s.2 ⟩),
               (↑"b", ⟨ Named s!"{s}.b" D, λ s tt s' => more_defined tt s.2.1 ∧ s'.2.1 = tt ∧ s'.1 = s.1 ∧ s'.2.2 = s.2.2 ⟩),
               (↑"cin", ⟨ Named s!"{s}.c" D, λ s tt s' => more_defined tt s.2.2 ∧ s'.2.2 = tt ∧ s'.1 = s.1 ∧ s'.2.1 = s.2.1 ⟩)].toAssocList,
    outputs := [ (↑"s", ⟨ Named s!"{s}.s" D, λ s tt s' => s = s' ∧ tt = delayN [false, false] (adcb s.1 s.2.1 s.2.2).2 ⟩)
               , (↑"cout", ⟨ Named s!"{s}.c" D, λ s tt s' => s = s' ∧ tt = delayN [false, false, false] (adcb s.1 s.2.1 s.2.2).1 ⟩)].toAssocList
    init_state := λ s => s = default
  }

def buffer_spec_m (s : String := "") : StringModule (Named s (D × D)) :=
 {
  inputs := [(↑"in", ⟨ Named s!"{s}.in" D, λ s tt s' => more_defined tt s.1 ∧ s'.1 = tt ∧ s'.2 = s.2 ⟩)].toAssocList,
  outputs := [(↑"out", ⟨ Named s!"{s}.out" D, λ s tt s' => more_defined tt s.2 ∧ s'.2 = tt ∧ s'.1 = s.1⟩)].toAssocList,
  init_state := λ s => s = default
 }

 def buffered_full_adder_m := [graphEnv|
  a [type="io"];
  b [type="io"];
  cin [type="io"];
  s [type="io"];
  cout [type="io"];

  fa [type="fa", typeImp=$(⟨_, full_adder_spec_m "fa"⟩)];
  b_1 [type="b_1", typeImp=$(⟨_, buffer_spec_m "b_1"⟩)];
  b_2 [type="b_2", typeImp=$(⟨_, buffer_spec_m "b_2"⟩)];

  a -> fa [to="a"];
  b -> fa [to="b"];
  cin -> fa [to="cin"];

  fa -> b_1 [from="s", to="in"];
  fa -> b_2 [from="cout", to="in"];
  b_1 -> s [from="out"];
  b_2 -> cout [from="out"];
 ]

def buffered_full_adder_m_lowered := buffered_full_adder_m.1.lower_TR |>.get rfl

def env_bfam := buffered_full_adder_m.2

@[drenv] theorem find?_fa_m : (Batteries.AssocList.find? "fa" env_bfam) = .some ⟨_, full_adder_spec_m "fa"⟩ := rfl
@[drenv] theorem find?_b1_m : (Batteries.AssocList.find? "b_1" env_bfam) = .some ⟨_, buffer_spec_m "b_1"⟩ := rfl
@[drenv] theorem find?_b2_m : (Batteries.AssocList.find? "b_2" env_bfam) = .some ⟨_, buffer_spec_m "b_2"⟩ := rfl

seal env_bfam in
def_module full_adder_spec_t : Type :=
  [T| buffered_full_adder_m_lowered, env_bfam.find? ]
reduction_by
  dsimp [buffered_full_adder_m_lowered]
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
  simp only [drenv]
  dsimp


seal env_bfam in
def_module full_adder_spec : StringModule full_adder_spec_t :=
  [e| buffered_full_adder_m_lowered, env_bfam.find? ]
reduction_by
       dsimp [buffered_full_adder_m_lowered]
       (dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
        dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
        dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
        rw [rw_opaque (by simp only [drenv]; rfl)]; dsimp
        dsimp [Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts, Module.mapInputPorts, reduceAssocListfind?]
        simp (disch := decide) only [AssocList.bijectivePortRenaming_invert]
        dsimp [Module.product]
        dsimp only [reduceModuleconnect'2]
        dsimp only [reduceEraseAll]
        dsimp; dsimp [reduceAssocListfind?]

        unfold Module.connect''
        dsimp [toString]
        )

/--
Equivalent to just xor.
-/
def full_adder_s := [graphEnv|
    a [type="io"];
    b [type="io"];
    cin [type="io"];
    s [type="io"];
    cout [type="io"];

    ha1 [type="ha_1", typeImp=$(⟨_, half_adder_m "ha_1"⟩)];
    ha2 [type="ha_2", typeImp=$(⟨_, half_adder_m "ha_2"⟩)];
    or [type="or", typeImp=$(⟨_, or_m⟩)];

    a -> ha1 [to="a"];
    b -> ha1 [to="b"];
    cin -> ha2 [to="a"];
    ha1 -> ha2 [from="s",to="b"];
    ha2 -> s [from="s"];
    ha2 -> or [from="c",to="a"];
    ha1 -> or [from="c",to="b"];
    or -> cout [from="c"];
  ]

def full_adder_s_lowered := full_adder_s.1.lower_TR |>.get rfl

def env_fas := full_adder_s.2

@[drenv] theorem find?_nand1_m : (Batteries.AssocList.find? "ha_1" env_fas) = .some ⟨_, half_adder_m "ha_1"⟩ := rfl
@[drenv] theorem find?_nand2_m : (Batteries.AssocList.find? "ha_2" env_fas) = .some ⟨_, half_adder_m "ha_2"⟩ := rfl
@[drenv] theorem find?_nand3_m : (Batteries.AssocList.find? "or" env_fas) = .some ⟨_, or_m⟩ := rfl

seal env_fas in
def_module full_adder_imp_t : Type :=
  [T| full_adder_s_lowered, env_fas.find? ]
reduction_by
  dsimp [full_adder_s_lowered]
  dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
  dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
  dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
  simp only [drenv]
  dsimp

seal env_fas in
def_module full_adder_imp : StringModule full_adder_imp_t :=
  [e| full_adder_s_lowered, env_fas.find? ]
reduction_by
       dsimp [full_adder_s_lowered]
       (dsimp -failIfUnchanged [drunfold_defs, toString, reduceAssocListfind?, reduceListPartition]
        dsimp -failIfUnchanged [reduceExprHighLower, reduceExprHighLowerProdTR, reduceExprHighLowerConnTR]
        dsimp [ ExprHigh.uncurry, ExprLow.build_module_expr, ExprLow.build_module_type, ExprLow.build_module, ExprLow.build_module', toString]
        rw [rw_opaque (by simp only [drenv]; rfl)]; dsimp
        dsimp [Module.renamePorts, Module.mapPorts2, Module.mapOutputPorts, Module.mapInputPorts, reduceAssocListfind?]
        simp (disch := decide) only [AssocList.bijectivePortRenaming_invert]
        dsimp [Module.product]
        dsimp only [reduceModuleconnect'2]
        dsimp only [reduceEraseAll]
        dsimp; dsimp [reduceAssocListfind?]

        unfold Module.connect''
        dsimp [toString]
        )

instance : MatchInterface full_adder_imp full_adder_spec := by
  dsimp [full_adder_imp,full_adder_spec]
  solve_match_interface


def φ (lhs: full_adder_imp_t) (rhs : full_adder_spec_t) : Prop :=
  let ((lA, lB), (lCin, ha1s), ha2c, ha1c) := lhs
  let ((bs_in, bs_out), (bc_in, bc_out), (rA, rB, rCin)) := rhs
  more_defined bc_out (delay false (or ha2c ha1c)) ∧
    more_defined bs_out (delay false (xor lCin ha1s))

theorem refines' :
  full_adder_imp ⊑_{φ} full_adder_spec := by
    intro lhsModule rhsModule inv
    unfold φ at inv
    let ((lA, lB), (lCin, ha1s), ha2c, ha1c) := lhsModule
    let ((bs_in, bs_out), (bc_in, bc_out), (rA, rB, rCin)) := rhsModule
    clear lhsModule rhsModule
    -- simp at inv
    apply Module.comp_refines.mk
    . -- Inputs
      intros inport targetLhs invalue h
      sorry
    . -- Outputs
      sorry
    . -- Internals
      sorry

theorem refines :
  full_adder_imp ⊑ full_adder_spec_m := by sorry

end FullAdder

end Graphiti.CombModule
