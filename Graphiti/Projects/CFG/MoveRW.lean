/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Projects.CFG.Basic

open Batteries (AssocList)

namespace Graphiti.CFG.MoveRW

def expand_reads_2 : RewriteHigh String DFGandCFG where
  params := 2
  lhs := fun l _ => [graphv2|
    i [io];
    o1 [io];
    o2 [io];
    o3 [io];

    fork [type=$(.dfg .fork)];
    read [type=$(.rw (.reads (extractList l[1])))];

    i -> fork.in1;
    fork.out2 -> o1;
    read.out1 -> o2;
    read.out2 -> o3;

    fork.out1 -> read.in1;
  ]
  rhs := fun l _ => [graphv2|
    i [io];
    o1 [io];
    o2 [io];
    o3 [io];

    fork [type=$(.dfg .fork)];
    read [type=$(.rw (.reads ((extractList l[1]).take 1)))];
    fork2 [type=$(.dfg .fork)];
    read2 [type=$(.rw (.reads (extractList l[1]).tail))];

    i -> fork.in1;
    fork2.out2 -> o1;
    read.out1 -> o2;
    read2.out1 -> o3;

    fork.out1 -> read.in1;
    fork.out2 -> fork2.in1;
    fork2.out1 -> read2.in1;
  ]
  predicate := fun l =>
    (extractList l[1].type).length == 2
  name := "expand-reads-2"

def rw_noteq : RewriteHigh String DFGandCFG where
  params := 3
  lhs := fun l _ => [graphv2|
    i_ctx [io];
    i_v [io];
    o_ctx [io];
    o_v [io];

    write [type=$(.rw (.writes (extractList l[0])))];
    fork [type=$(.dfg .fork)];
    read [type=$(.rw (.reads (extractList l[2])))];

    i_v -> write [to="in2"];
    i_ctx -> write [to="in1"];
    fork -> o_ctx [from="out2"];
    read -> o_v [from="out1"];

    write -> fork [from="out1", to="in1"];
    fork -> read [from="out1", to="in1"];
  ]
  rhs := fun l _ => [graphv2|
    i_ctx [io];
    i_v [io];
    o_ctx [io];
    o_v [io];

    write [type=$(.rw (.writes (extractList l[0])))];
    fork [type=$(.dfg .fork)];
    read [type=$(.rw (.reads (extractList l[2])))];

    i_ctx -> fork [to="in1"];
    i_v -> write [to="in2"];
    write -> o_ctx [from="out1"];
    read -> o_v [from="out1"];

    fork -> write [from="out2", to="in1"];
    fork -> read [from="out1", to="in1"];
  ]
  predicate := fun v =>
    let l0 := extractList v[0].type
    let l1 := extractList v[2].type
    l0.length == 1
    && l1.length == 1
    && (l0[0]?.getD 0) != (l1[0]?.getD 0)
  name := "rw-noteq"

def rw_eq : RewriteHigh String DFGandCFG where
  params := 3
  lhs := fun l _ => [graphv2|
    i_ctx [io];
    i_v [io];
    o_ctx [io];
    o_v [io];

    write [type=$(.rw (.writes (extractList l[0])))];
    fork [type=$(.dfg .fork)];
    read [type=$(.rw (.reads (extractList l[2])))];

    i_v -> write [to="in2"];
    i_ctx -> write [to="in1"];
    fork -> o_ctx [from="out2"];
    read -> o_v [from="out1"];

    write -> fork [from="out1", to="in1"];
    fork -> read [from="out1", to="in1"];
  ]
  rhs := fun l _ => [graphv2|
    i_ctx [io];
    i_v [io];
    o_ctx [io];
    o_v [io];

    write [type=$(.rw (.writes (extractList l[0])))];
    fork [type=$(.dfg .fork)];

    i_v -> fork [to="in1"];
    i_ctx -> write [to="in1"];
    write -> o_ctx [from="out1"];
    fork -> o_v [from="out1"];

    fork -> write [from="out2", to="in2"];
  ]
  predicate := fun v =>
    let l0 := extractList v[0].type
    let l1 := extractList v[2].type
    l0.length == 1
    && l1.length == 1
    && (l0[0]?.getD 0) == (l1[0]?.getD 1)
  name := "rw-eq"

def combine_rw_2 : RewriteHigh String DFGandCFG where
  params := 4
  lhs := fun l _ => [graphv2|
    i [io];
    o1 [io];
    o2 [io];
    o3 [io];

    fork [type=$(.dfg .fork)];
    read [type=$(.rw (.reads (extractList l[1])))];
    fork2 [type=$(.dfg .fork)];
    read2 [type=$(.rw (.reads (extractList l[3])))];

    i -> fork.in1;
    fork2.out2 -> o1;
    read.out1 -> o2;
    read2.out1 -> o3;

    fork.out1 -> read.in1;
    fork.out2 -> fork2.in1;
    fork2.out1 -> read2.in1;
  ]
  rhs := fun l _ => [graphv2|
    i [io];
    o1 [io];
    o2 [io];
    o3 [io];

    fork [type=$(.dfg .fork)];
    read [type=$(.rw (.reads (extractList l[1] ++ extractList l[3])))];

    i -> fork.in1;
    fork.out2 -> o1;
    read.out1 -> o2;
    read.out2 -> o3;

    fork.out1 -> read.in1;
  ]
  predicate := fun l =>
    (extractList l[1].type).length == 1
    && (extractList l[3].type).length == 1
  name := "combine-rw-2"

def combine_rw_3 : RewriteHigh String DFGandCFG where
  params := 4
  lhs := fun l _ => [graphv2|
    i [io];
    o1 [io];
    o2 [io];
    o3 [io];
    o4 [io];

    fork [type=$(.dfg .fork)];
    read [type=$(.rw (.reads (extractList l[1])))];
    fork2 [type=$(.dfg .fork)];
    read2 [type=$(.rw (.reads (extractList l[3])))];

    i -> fork.in1;
    fork2.out2 -> o1;
    read.out1 -> o2;
    read2.out1 -> o3;
    read2.out2 -> o4;

    fork.out1 -> read.in1;
    fork.out2 -> fork2.in1;
    fork2.out1 -> read2.in1;
  ]
  rhs := fun l _ => [graphv2|
    i [io];
    o1 [io];
    o2 [io];
    o3 [io];
    o4 [io];

    fork [type=$(.dfg .fork)];
    read [type=$(.rw (.reads (extractList l[1] ++ extractList l[3])))];

    i -> fork.in1;
    fork.out2 -> o1;
    read.out1 -> o2;
    read.out2 -> o3;
    read.out3 -> o4;

    fork.out1 -> read.in1;
  ]
  predicate := fun l =>
    (extractList l[1].type).length == 1
    && (extractList l[3].type).length == 2
  name := "combine-rw-3"

def combine_write_2 : RewriteHigh String DFGandCFG where
  params := 2
  lhs := fun l _ => [graphv2|
    i1 [io];
    i2 [io];
    i3 [io];
    o1 [io];

    write1 [type=$(.rw (.writes (extractList l[0])))];
    write2 [type=$(.rw (.writes (extractList l[1])))];

    i1 -> write1.in1;
    i2 -> write1.in2;
    i3 -> write2.in2;
    write2.out1 -> o1;

    write1.out1 -> write2.in1;
  ]
  rhs := fun l _ => [graphv2|
    i1 [io];
    i2 [io];
    i3 [io];
    o1 [io];

    write1 [type=$(.rw (.writes (extractList l[0] ++ extractList l[1])))];

    i1 -> write1.in1;
    i2 -> write1.in2;
    i3 -> write1.in3;
    write1.out1 -> o1;
  ]
  predicate := fun l =>
    (extractList l[0].type).length == 1
    && (extractList l[1].type).length == 1
  name := "combine-write-2"

/-
TODO: This should be generalized by making it possible for each lhs and rhs to rely on the PortMapping (or maybe even
the graph itself).  Actually, requiring on the graph might not work in the final correctness theorem, at least if the
correctness depends on contextual graph structures.
-/

def combine_write_3_1 : RewriteHigh String DFGandCFG where
  params := 2
  lhs := fun l _ => [graphv2|
    i1 [io]; i2 [io]; i3 [io]; i4 [io]; o1 [io];

    write1 [type=$(.rw (.writes (extractList l[0])))];
    write2 [type=$(.rw (.writes (extractList l[1])))];

    i1 -> write1.in1;
    i2 -> write1.in2;
    i3 -> write1.in3;
    i4 -> write2.in2;
    write2.out1 -> o1;

    write1.out1 -> write2.in1;
  ]
  rhs := fun l _ => [graphv2|
    i1 [io]; i2 [io]; i3 [io]; i4 [io]; o1 [io];

    write1 [type=$(.rw (.writes (extractList l[0] ++ extractList l[1])))];

    i1 -> write1.in1;
    i2 -> write1.in2;
    i3 -> write1.in3;
    i4 -> write1.in4;
    write1.out1 -> o1;
  ]
  predicate := fun l =>
    (extractList l[0].type).length == 2
    && (extractList l[1].type).length == 1
  name := "combine-write-3-1"

def combine_write_3_2 : RewriteHigh String DFGandCFG where
  params := 2
  lhs := fun l _ => [graphv2|
    i1 [io]; i2 [io]; i3 [io]; i4 [io]; o1 [io];

    write1 [type=$(.rw (.writes (extractList l[0])))];
    write2 [type=$(.rw (.writes (extractList l[1])))];

    i1 -> write1.in1;
    i2 -> write1.in2;
    i3 -> write2.in2;
    i4 -> write2.in3;
    write2.out1 -> o1;

    write1.out1 -> write2.in1;
  ]
  rhs := fun l _ => [graphv2|
    i1 [io]; i2 [io]; i3 [io]; i4 [io]; o1 [io];

    write1 [type=$(.rw (.writes (extractList l[0] ++ extractList l[1])))];

    i1 -> write1.in1;
    i2 -> write1.in2;
    i3 -> write1.in3;
    i4 -> write1.in4;
    write1.out1 -> o1;
  ]
  predicate := fun l =>
    (extractList l[0].type).length == 1
    && (extractList l[1].type).length == 2
  name := "combine-write-3-2"

def to_readsN_3 : RewriteHigh String DFGandCFG where
  params := 1
  lhs := fun l _ =>
    [graphv2|
      i [io]; o1 [io]; o2 [io]; o3 [io];

      reads [type=$(.rw (.reads (extractList l[0])))];

      i -> reads.in1;
      reads.out1 -> o1;
      reads.out2 -> o2;
      reads.out3 -> o3;
    ]
  rhs := fun l _ =>
    [graphv2|
      i [io]; o1 [io]; o2 [io]; o3 [io];

      reads [type=$(.rw (.readsN (extractList l[0])))];
      split1 [type=$(.dfg .split)];
      split2 [type=$(.dfg .split)];

      i -> reads.in1;
      reads.out1 -> split1.in1;
      split1.out1 -> split2.in1;
      split2.out1 -> o1;
      split2.out2 -> o2;
      split1.out2 -> o3;
    ]
  name := "to-readsN-3"

def to_readsN_1 : RewriteHigh String DFGandCFG where
  params := 1
  lhs := fun l _ =>
    [graphv2|
      i [io]; o1 [io];

      reads [type=$(.rw (.reads (extractList l[0])))];

      i -> reads.in1;
      reads.out1 -> o1;
    ]
  rhs := fun l _ =>
    [graphv2|
      i [io]; o1 [io];

      reads [type=$(.rw (.readsN (extractList l[0])))];

      i -> reads.in1;
      reads.out1 -> o1;
    ]
  name := "to-readsN-1"

def to_writesN_3 : RewriteHigh String DFGandCFG where
  params := 1
  lhs := fun l _ =>
    [graphv2|
      o [io]; i1 [io]; i2 [io]; i3 [io]; i4 [io];

      writes [type=$(.rw (.writes (extractList l[0])))];

      i1 -> writes.in1;
      i2 -> writes.in2;
      i3 -> writes.in3;
      i4 -> writes.in4;
      writes.out1 -> o;
    ]
  rhs := fun l _ =>
    [graphv2|
      o [io]; i1 [io]; i2 [io]; i3 [io]; i4 [io];

      writes [type=$(.rw (.writesN (extractList l[0])))];
      join1 [type=$(.dfg .join)];
      join2 [type=$(.dfg .join)];

      i1 -> writes.in1;
      i2 -> join1.in1;
      i3 -> join1.in2;
      i4 -> join2.in2;
      writes.out1 -> o;

      join1.out1 -> join2.in1;
      join2.out1 -> writes.in2;
    ]
  name := "to-writesN-3"

def move_rw : RWTree (RewriteHigh String DFGandCFG) :=
  .seq (.fix (.base expand_reads_2))
  (.seq (RWTree.fix ([rw_noteq, rw_eq].toRWTreeFix |>.get rfl))
    (RWTree.fix ([combine_rw_2, combine_rw_3, combine_write_2, combine_write_3_1, combine_write_3_2, to_readsN_3, to_writesN_3, to_readsN_1].toRWTreeFix |>.get rfl)))

def normalize_rw : RewriteHigh String DFGandCFG where
  params := 5
  lhs := fun l _ => [graphv2|
      i1 [io]; o1 [io]; i2 [io]; o2 [io];

      branch [type=$(.dfg .branch)];
      read [type=$(.rw (.readsN (extractList l[1])))];
      write [type=$(.rw (.writesN (extractList l[2])))];
      pure [type=$(.dfg .pure)];
      fork [type=$(.dfg .fork)];

      i1 -> branch.in1;
      i2 -> branch.in2;
      branch.out2 -> o1;
      write.out1 -> o2;

      branch.out1 -> fork.in1;
      fork.out1 -> read.in1;
      fork.out2 -> write.in1;
      read.out1 -> pure.in1;
      pure.out1 -> write.in2;
    ]
  rhs := fun l _ => [graphv2|
      i1 [io]; o1 [io]; i2 [io]; o2 [io];

      branch [type=$(.dfg .branch)];
      read [type=$(.rw (.readsN (extractList l[1] ++ extractList l[2])))];
      write [type=$(.rw (.writesN (extractList l[1] ++ extractList l[2])))];
      pure [type=$(.dfg .pure)];
      fork [type=$(.dfg .fork)];
      take [type=$(.dfg (.tuple (.take (extractList l[1]).length)))];
      readFork [type=$(.dfg .fork)];
      append [type=$(.dfg (.tuple .append))];

      i1 -> branch.in1;
      i2 -> branch.in2;
      branch.out2 -> o1;
      write.out1 -> o2;

      branch.out1 -> fork.in1;
      fork.out1 -> read.in1;
      fork.out2 -> write.in1;
      read.out1 -> take.in1;
      take.out1 -> readFork.in1;
      readFork.out1 -> pure.in1;
      readFork.out2 -> append.in1;
      pure.out1 -> append.in2;
      append.out1 -> write.in2;
    ]

def normalize_loop_rw : RewriteHigh String DFGandCFG where
  params := 8
  lhs := fun l _ => [graphv2|
      i1 [io]; o1 [io]; o2 [io];

      fork1 [type=$(.dfg .fork)];
      fork2 [type=$(.dfg .fork)];
      reads1 [type=$(.rw (.readsN (extractList l[2])))];
      reads2 [type=$(.rw (.readsN (extractList l[3])))];
      pure1 [type=$(.dfg .pure)];
      pure2 [type=$(.dfg .pure)];
      branch [type=$(.dfg .branch)];
      writes [type=$(.rw (.writesN (extractList l[7])))];

      i1 -> fork1.in1;
      branch.out2 -> o1;
      writes.out1 -> o2;

      fork1.out1 -> reads1.in1;
      reads1.out1 -> pure1.in1;
      pure1.out1 -> branch.in2;
      fork1.out2 -> branch.in1;
      branch.out1 -> fork2.in1;
      fork2.out1 -> reads2.in1;
      fork2.out2 -> writes.in1;
      reads2.out1 -> pure2.in1;
      pure2.out1 -> writes.in2;
    ]
  rhs := fun l _ => [graphv2|
      i1 [io]; o1 [io]; o2 [io];

      fork1 [type=$(.dfg .fork)];
      fork2 [type=$(.dfg .fork)];
      reads1 [type=$(.rw (.readsN (extractList l[2] ++ extractList l[3])))];
      reads2 [type=$(.rw (.readsN (extractList l[2] ++ extractList l[3])))];
      pure1 [type=$(.dfg .pure)];
      pure2 [type=$(.dfg .pure)];
      branch [type=$(.dfg .branch)];
      writes [type=$(.rw (.writesN (extractList l[2] ++ extractList l[7])))];

      fork3 [type=$(.dfg .fork)];
      drop [type=$(.dfg (.tuple (.drop 1)))];
      take1 [type=$(.dfg (.tuple (.take 1)))];
      take2 [type=$(.dfg (.tuple (.take 1)))];
      append [type=$(.dfg (.tuple .append))];

      i1 -> fork1.in1;
      branch.out2 -> o1;
      writes.out1 -> o2;

      fork1.out1 -> reads1.in1;
      pure1.out1 -> branch.in2;
      fork1.out2 -> branch.in1;
      branch.out1 -> fork2.in1;
      fork2.out1 -> reads2.in1;
      fork2.out2 -> writes.in1;

      reads2.out1 -> fork3.in1;
      fork3.out1 -> take1.in1;
      fork3.out2 -> drop.in1;
      drop.out1 -> pure2.in1;
      pure2.out1 -> append.in2;
      take1.out1 -> append.in1;
      append.out1 -> writes.in2;

      reads1.out1 -> take2.in1;
      take2.out1 -> pure1.in1;
    ]

def normalize_loop_rw2 : RewriteHigh String DFGandCFG where
  params := 8
  lhs := fun l _ => [graphv2|
      i1 [io]; o1 [io]; o2 [io];

      fork1 [type=$(.dfg .fork)];
      fork2 [type=$(.dfg .fork)];
      reads1 [type=$(.rw (.readsN (extractList l[2])))];
      reads2 [type=$(.rw (.readsN (extractList l[3])))];
      pure1 [type=$(.dfg .pure)];
      pure2 [type=$(.dfg .pure)];
      branch [type=$(.dfg .branch)];
      writes [type=$(.rw (.writesN (extractList l[7])))];

      i1 -> fork1.in1;
      branch.out2 -> o1;
      writes.out1 -> o2;

      fork1.out1 -> reads1.in1;
      reads1.out1 -> pure1.in1;
      pure1.out1 -> branch.in2;
      fork1.out2 -> branch.in1;
      branch.out1 -> fork2.in1;
      fork2.out1 -> reads2.in1;
      fork2.out2 -> writes.in1;
      reads2.out1 -> pure2.in1;
      pure2.out1 -> writes.in2;
    ]
  rhs := fun l _ => [graphv2|
      i1 [io]; o1 [io]; o2 [io];

      fork1 [type=$(.dfg .fork)];
      fork2 [type=$(.dfg .fork)];
      reads1 [type=$(.rw (.readsN (extractList l[2])))];
      reads2 [type=$(.rw (.readsN (extractList l[3])))];
      pure1 [type=$(.dfg .pure)];
      pure2 [type=$(.dfg .pure)];
      branch [type=$(.dfg .branch)];
      writes [type=$(.rw (.writesN (extractList l[7])))];

      i1 -> fork1.in1;
      branch.out2 -> o1;
      writes.out1 -> o2;

      fork1.out1 -> reads1.in1;
      reads1.out1 -> pure1.in1;
      pure1.out1 -> branch.in2;
      fork1.out2 -> branch.in1;
      branch.out1 -> fork2.in1;
      fork2.out1 -> reads2.in1;
      fork2.out2 -> writes.in1;
      reads2.out1 -> pure2.in1;
      pure2.out1 -> writes.in2;
    ]

def normalize_loop_rw3 : RewriteHigh String DFGandCFG where
  params := 8
  lhs := fun l _ => [graphv2|
      i1 [io]; o1 [io]; o2 [io];

      fork1 [type=$(.dfg .fork)];
      fork2 [type=$(.dfg .fork)];
      reads1 [type=$(.rw (.readsN (extractList l[2])))];
      reads2 [type=$(.rw (.readsN (extractList l[3])))];
      pure1 [type=$(.dfg .pure)];
      pure2 [type=$(.dfg .pure)];
      branch [type=$(.dfg .branch)];
      writes [type=$(.rw (.writesN (extractList l[7])))];

      i1 -> fork1.in1;
      branch.out2 -> o1;
      writes.out1 -> o2;

      fork1.out1 -> reads1.in1;
      reads1.out1 -> pure1.in1;
      pure1.out1 -> branch.in2;
      fork1.out2 -> branch.in1;
      branch.out1 -> fork2.in1;
      fork2.out1 -> reads2.in1;
      fork2.out2 -> writes.in1;
      reads2.out1 -> pure2.in1;
      pure2.out1 -> writes.in2;
    ]
  rhs := fun l _ => [graphv2|
      i1 [io]; o1 [io]; o2 [io];

      fork1 [type=$(.dfg .fork)];
      fork2 [type=$(.dfg .fork)];
      reads1 [type=$(.rw (.readsN (extractList l[2])))];
      reads2 [type=$(.rw (.readsN (extractList l[3])))];
      pure1 [type=$(.dfg .pure)];
      pure2 [type=$(.dfg .pure)];
      branch [type=$(.dfg .branch)];
      writes [type=$(.rw (.writesN (extractList l[7])))];

      i1 -> fork1.in1;
      branch.out2 -> o1;
      writes.out1 -> o2;

      fork1.out1 -> reads1.in1;
      reads1.out1 -> pure1.in1;
      pure1.out1 -> branch.in2;
      fork1.out2 -> branch.in1;
      branch.out1 -> fork2.in1;
      fork2.out1 -> reads2.in1;
      fork2.out2 -> writes.in1;
      reads2.out1 -> pure2.in1;
      pure2.out1 -> writes.in2;
    ]

end Graphiti.CFG.MoveRW
