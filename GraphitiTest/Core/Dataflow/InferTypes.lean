/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Core.Dataflow.InferTypes
import Graphiti.Core.Graph.ExprHighElaborator

namespace Graphiti.ExprLow.Test

@[drunfold_defs]
def lhs : ExprHigh String (String × Nat) := [graph|
    i_in [type = "io"];
    o_out [type = "io"];

    mux [type = "mux", arg = $(1)];
    condition_fork [type = "fork2", arg = $(2)];
    branch [type = "branch", arg = $(3)];
    tag_split [type = "split", arg = $(4)];
    mod [type = "pure", arg = $(5)];
    loop_init [type = "initBool", arg = $(6)];
    queue [type = "queue", arg = $(7)];
    queue_out [type = "queue", arg = $(8)];
    output [type = "output", arg = $(9)];

    i_in -> mux [to="in2"];
    queue_out -> output [from="out1", to="in1"];

    loop_init -> mux [from="out1", to="in1"];
    condition_fork -> loop_init [from="out2", to="in1"];
    condition_fork -> branch [from="out1", to="in2"];
    mod -> tag_split [from="out1", to="in1"];
    tag_split -> branch [from="out1", to="in1"];
    tag_split -> condition_fork [from="out2", to="in1"];
    mux -> mod [from="out1", to="in1"];
    branch -> queue [from="out1", to="in1"];
    queue -> mux [from="out1", to="in3"];
    branch -> queue_out [from="out2", to="in1"];
  ]

#guard_msgs(drop info) in
#eval lhs.lower |>.get!

#guard_msgs(drop info) in
#eval lhs.lower |>.get! |> (fun x => match (x : ExprLow String (String × Nat)) with | .connect _ e => e | _ => x) |>.findInputInst ⟨.internal "queue_out", "in1"⟩

#guard_msgs(drop info) in
#eval lhs.lower |>.get! |>.infer_equalities ⟨∅, ∅⟩ |>.map (·.typeMap)

#guard_msgs(drop info) in
#eval lhs.lower |>.get! |>.infer_equalities ⟨∅, ∅⟩ |>.map (·.ufMap) |>.map (·.checkEquiv! 8 6 |>.snd)
#guard_msgs(drop info) in
#eval lhs.lower |>.get! |>.infer_equalities ⟨∅, ∅⟩ |>.map (fun x => x.typeMap |>.toList.map (λ y => (y.fst, x.ufMap.root! y.snd)))
#guard_msgs(drop info) in
#eval lhs.lower |>.get! |>.infer_equalities ⟨∅, ∅⟩ |>.map (fun x => x.findConcr (Graphiti.TypeConstraint.var 4))
#guard_msgs(drop info) in
#eval lhs.lower |>.get! |>.infer_types

end Graphiti.ExprLow.Test
