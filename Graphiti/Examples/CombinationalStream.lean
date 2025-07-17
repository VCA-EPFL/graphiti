/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.ModuleLemmas
import Graphiti.ModuleReduction
import Graphiti.Simp
import Graphiti.ExprHighElaborator
import Graphiti.AssocList.Basic
import Graphiti.TypeExpr
import Graphiti.VerilogExport

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
  ∃ s1' s2', s1 = some s1' ∧ s2 = some s2' ∧ s1'.length >= s2'.length ∧ s1'.take (s2'.length) = s2'

def delay (d : α) (s : Stream α) : Stream α :=
  Option.map (d :: ·) s

def not (s : Stream Bool) : Stream Bool := s.map (!·)

def and (s1 s2 : Stream Bool) : Stream Bool :=
  map2 (λ a b => a && b) s1 s2

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

def not_m : NatModule D :=
  { inputs := [(0, ⟨ D, λ s tt s' => more_defined s tt ∧ s' = not (delay false tt) ⟩)].toAssocList,
    outputs := [(0, ⟨ D, λ s tt s' => s = s' ∧ s = tt⟩)].toAssocList
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

def nand_m : NatModule (D × D) :=
  { inputs := [(0, ⟨ D, λ s tt s' => more_defined s.1 tt ∧ s'.1 = tt ∧ s'.2 = s.2 ⟩),
               (1, ⟨ D, λ s tt s' => more_defined s.2 tt ∧ s'.2 = tt ∧ s'.1 = s.1 ⟩)].toAssocList,
    outputs := [(0, ⟨ D, λ s tt s' => s = s' ∧ tt = delay false (nand s.1 s.2) ⟩)].toAssocList
    init_state := λ s => s = default
  }

def nand_m_template : VerilogTemplate where
  module := build_local_module "nand_m" (simple_interface ["in1", "in2"] ["out1"]) "assign #1 out1 = ~ (in1 & in2);"
  instantiation name inst := format_instantiation "nand_m" name inst

def nand3_m : NatModule (D × D × D) :=
  { inputs := [(0, ⟨ D, λ s tt s' => more_defined s.1 tt ∧ s'.1 = tt ∧ s'.2 = s.2 ⟩),
               (1, ⟨ D, λ s tt s' => more_defined s.2.1 tt ∧ s'.2.1 = tt ∧ s'.1 = s.1 ∧ s'.2.2 = s.2.2 ⟩),
               (2, ⟨ D, λ s tt s' => more_defined s.2.2 tt ∧ s'.2.2 = tt ∧ s'.1 = s.1 ∧ s'.2.1 = s.2.1 ⟩)].toAssocList,
    outputs := [(0, ⟨ D, λ s tt s' => s = s' ∧ tt = delay false (nand3 s.1 s.2.1 s.2.2) ⟩)].toAssocList
    init_state := λ s => s = default
  }

def nand3_m_template : VerilogTemplate where
  module := build_local_module "nand3_m" (simple_interface ["in1", "in2", "in3"] ["out1"]) "assign #1 out1 = ~ (in1 & in2 & in3);"
  instantiation name inst := format_instantiation "nand3_m" name inst

def and_m : NatModule (D × D) :=
  { inputs := [(0, ⟨ D, λ s tt s' => more_defined s.1 tt ∧ s'.1 = tt ∧ s'.2 = s.2 ⟩),
               (1, ⟨ D, λ s tt s' => more_defined s.2 tt ∧ s'.2 = tt ∧ s'.1 = s.1 ⟩)].toAssocList,
    outputs := [(0, ⟨ D, λ s tt s' => s = s' ∧ tt = delay false (nand s.1 s.2) ⟩)].toAssocList
    init_state := λ s => s = default
  }

def and_m_template : VerilogTemplate where
  module := build_local_module "and_m" (simple_interface ["in1", "in2"] ["out1"]) "assign #1 out1 = in1 & in2;"
  instantiation name inst := format_instantiation "and_m" name inst

def fork_m : NatModule D :=
  { inputs := [(0, ⟨ D, λ s tt s' => more_defined s tt ∧ s' = tt ⟩)].toAssocList,
    outputs := [(0, ⟨ D, λ s tt s' => s = s' ∧ tt = s ⟩), (1, ⟨ D, λ s tt s' => s = s' ∧ tt = s ⟩)].toAssocList
    init_state := λ s => s = default
  }

def fork_m_template : VerilogTemplate where
  module := build_local_module "fork_m" (simple_interface ["in1"] ["out1", "out2"]) "assign out1 = in1;\nassign out2 = in1;"
  instantiation name inst := format_instantiation "fork_m" name inst

def fork3_m : NatModule D :=
  { inputs := [(0, ⟨ D, λ s tt s' => more_defined s tt ∧ s' = tt ⟩)].toAssocList,
    outputs := [(0, ⟨ D, λ s tt s' => s = s' ∧ tt = s ⟩), (1, ⟨ D, λ s tt s' => s = s' ∧ tt = s ⟩), (2, ⟨ D, λ s tt s' => s = s' ∧ tt = s ⟩)].toAssocList
    init_state := λ s => s = default
  }

def fork3_m_template : VerilogTemplate where
  module := build_local_module "fork3_m" (simple_interface ["in1"] ["out1", "out2", "out3"]) "assign out1 = in1;\nassign out2 = in1;\nassign out3 = in1;"
  instantiation name inst := format_instantiation "fork3_m" name inst

def not_sm := not_m.stringify
def sink_sm := sink_m.stringify
def and_sm := and_m.stringify
def nand_sm := nand_m.stringify
def nand3_sm := nand3_m.stringify
def fork_sm := fork_m.stringify
def fork3_sm := fork3_m.stringify

def env : IdentMap String VerilogTemplate :=
  [("sink_m", sink_m_template), ("and_m", and_m_template), ("nand_m", nand_m_template), ("nand3_m", nand3_m_template), ("fork_m", fork_m_template), ("fork3_m", fork3_m_template), ("not_m", not_m_template)].toAssocList

namespace FlipFlop

def d_latch'_m : ExprHigh String × Env := [graphEnv|
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

def d_latch_m : ExprHigh String × Env := [graphEnv|
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

def et_flip_flop_m : ExprHigh String × Env := [graphEnv|
    clk [type="io"];
    d [type="io"];
    q [type="io"];
    q_bar [type="io"];

    n1 [type="nand_m", typeImp = $(⟨_, nand_sm⟩)];
    n2 [type="nand_m", typeImp = $(⟨_, nand_sm⟩)];
    n3 [type="nand3_m", typeImp = $(⟨_, nand3_sm⟩)];
    n4 [type="nand_m", typeImp = $(⟨_, nand_sm⟩)];
    n5 [type="nand_m", typeImp = $(⟨_, nand_sm⟩)];
    n6 [type="nand_m", typeImp = $(⟨_, nand_sm⟩)];

    clkF [type="fork_m", typeImp = $(⟨_, fork_sm⟩)];
    n2F [type="fork3_m", typeImp = $(⟨_, fork3_sm⟩)];
    n3F [type="fork_m", typeImp = $(⟨_, fork_sm⟩)];
    n4F [type="fork_m", typeImp = $(⟨_, fork_sm⟩)];
    n5F [type="fork_m", typeImp = $(⟨_, fork_sm⟩)];
    n6F [type="fork_m", typeImp = $(⟨_, fork_sm⟩)];

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

def env' := env.cons "d_latch_m" d_latch_m_template

def et_flip_flop_spec : NatModule (D × D) :=
  { inputs := [ (0, ⟨ D, λ s tt s' => True ⟩)
              , (1, ⟨ D, λ s tt s' => True ⟩)].toAssocList,
    outputs := [ (0, ⟨ D, λ s tt s' => True ⟩)
               , (1, ⟨ D, λ s tt s' => True ⟩)].toAssocList,
    init_state := λ s => s = default
  }

def et_ms_flip_flop_m : ExprHigh String × Env := [graphEnv|
    clk [type="io"];
    d [type="io"];
    q [type="io"];
    q_bar [type="io"];

    latch1 [type="d_latch_m", typeImp=$(ExprHigh.build_module d_latch_m.2 d_latch_m.1)];
    latch2 [type="d_latch_m", typeImp=$(ExprHigh.build_module d_latch_m.2 d_latch_m.1)];
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
#eval IO.print <| build_verilog_module "et_flip_flop_m" env et_flip_flop_m.1 (simple_interface ["d", "clk"] ["q", "q_bar"])
#eval IO.print <| build_verilog_module "et_ms_flip_flop_m" env' et_ms_flip_flop_m.1 (simple_interface ["d", "clk"] ["q", "q_bar"])

end FlipFlop

end Graphiti.CombModule
