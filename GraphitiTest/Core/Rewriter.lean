/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Core.Rewriter
import Graphiti.Core.Graph.ExprHighElaborator

namespace Graphiti.Rewriter.Test

/- Having multiple edges between nodes does not introduce additional nodes in the result. -/
/-- info: some true -/
#guard_msgs in
#eval findClosedRegion [graph|
        i [type="io"];
        o [type="io"];
        merge [type="Merge"];
        branch [type="Branch"];

        i -> merge [to="0"];
        branch -> o [from="0"];

        merge -> branch [from="0",to="0"];
        merge -> branch [from="1",to="1"];
      ] "merge" "branch"
  |>.map (·.isPerm ["merge", "branch"])

/- Unconnected nodes do not result in a list of nodes. -/
/-- info: true -/
#guard_msgs in
#eval findClosedRegion [graph|
        i [type="io"];
        o [type="io"];
        merge [type="Merge"];
        branch [type="Branch"];

        i -> merge [to="0"];
        branch -> o [from="0"];
      ] "merge" "branch"
  == none

/- Cases where one of the nodes is not present in the graph should not return a result. -/
/-- info: true -/
#guard_msgs in
#eval findClosedRegion [graph|
        i [type="io"];
        o [type="io"];
        merge [type="Merge"];
        branch2 [type="Branch"];

        i -> merge [to="0"];
        branch2 -> o [from="0"];
        merge -> branch2 [from="0",to="0"];
      ] "merge" "branch"
  == none

/-- info: true -/
#guard_msgs in
#eval findClosedRegion [graph|
        i [type="io"];
        o [type="io"];
        merge2 [type="Merge"];
        branch [type="Branch"];

        i -> merge2 [to="0"];
        branch -> o [from="0"];
        merge2 -> branch [from="0",to="0"];
      ] "merge" "branch"
  == none

/- Having multiple nodes between them should return them all. -/
/-- info: some true -/
#guard_msgs in
#eval findClosedRegion [graph|
        i [type="io"];
        o [type="io"];
        merge [type="Merge"];
        x1 [type="random"];
        x2 [type="random"];
        x3 [type="random"];
        branch [type="Branch"];

        i -> merge [to="0"];
        branch -> o [from="0"];
        merge -> x1 [from="0", to="0"];
        x1 -> x2 [from="0", to="0"];
        x2 -> branch [from="0", to="0"];
        merge -> x3 [from="1", to="0"];
        x3 -> branch [from="0", to="1"];
      ] "merge" "branch"
  |>.map (decide <| ·.isPerm ["x1", "x2", "x3", "merge", "branch"])

/- If an inner node ever reaches an IO port then this is not a region we care about. -/
/-- info: true -/
#guard_msgs in
#eval findClosedRegion [graph|
        i [type="io"];
        o [type="io"];
        o2 [type="io"];
        merge [type="Merge"];
        x1 [type="random"];
        x2 [type="random"];
        x3 [type="random"];
        branch [type="Branch"];

        i -> merge [to="0"];
        branch -> o [from="0"];
        merge -> x1 [from="0", to="0"];
        x1 -> x2 [from="0", to="0"];
        x2 -> branch [from="0", to="0"];
        merge -> x3 [from="1", to="0"];
        x3 -> branch [from="0", to="1"];
        x3 -> o2 [from="0"];
      ] "merge" "branch"
  == none

/- Searching between two instances of the same node will return none -/
/-- info: true -/
#guard_msgs in
#eval findClosedRegion [graph|
        i [type="io"];
        o [type="io"];
        o2 [type="io"];
        merge [type="Merge"];
        x1 [type="random"];
        x2 [type="random"];
        x3 [type="random"];
        branch [type="Branch"];

        i -> merge [to="0"];
        branch -> o [from="0"];
        merge -> x1 [from="0", to="0"];
        x1 -> x2 [from="0", to="0"];
        x2 -> branch [from="0", to="0"];
        merge -> x3 [from="1", to="0"];
        x3 -> branch [from="0", to="1"];
        x3 -> o2 [from="0"];
      ] "merge" "merge"
  == none

end Graphiti.Rewriter.Test
