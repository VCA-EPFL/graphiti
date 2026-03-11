/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Projects.CFG.Basic

open Batteries (AssocList)

namespace Graphiti.CFG.TranslateNode

def getOp : DFGandCFG → Operation × List Reg × Reg × Node
| .cfg (.Iop op regs dest next) => (op, regs, dest, next)
| _ => default

def getInop : DFGandCFG → Node
| .cfg (.Inop next) => next
| _ => default

def getIcond : DFGandCFG → Condition × List Reg × Node × Node
| .cfg (.Icond a b c d) => (a, b, c, d)
| _ => default

def op1 : RewriteHigh String DFGandCFG where
  params := 1
  lhs := fun l _ =>
    let op := getOp l[0]
    [graphv2|
      i [io];
      o [io];

      op [type=$(.cfg (.Iop op.1 op.2.1 op.2.2.1 op.2.2.2))];

      i -> op [to="in1"];
      op -> o [from="out1"];
    ]
  rhs := fun l _ =>
    let op := getOp l[0]
    [graphv2|
      i [io];
      o [io];

      fork [type=$(.dfg .fork)];
      read [type=$(.rw (.reads op.2.1))];
      write [type=$(.rw (.writes [op.2.2.1]))];
      op [type=$(.dfg (.op op.1))];

      i -> fork [to="in1"];
      write -> o [from="out1"];

      fork -> read [from="out1", to="in1"];
      fork -> write [from="out2", to="in1"];
      read -> op [from="out1", to="in1"];
      op -> write [from="out1", to="in2"];
    ]
  predicate := fun l =>
    let op := getOp l[0].type
    op.2.1.length == 1
  name := "translate-node-op1"

def op2 : RewriteHigh String DFGandCFG where
  params := 1
  lhs := fun l _ =>
    let op := getOp l[0]
    [graphv2|
      i [io];
      o [io];

      op [type=$(.cfg (.Iop op.1 op.2.1 op.2.2.1 op.2.2.2))];

      i -> op [to="in1"];
      op -> o [from="out1"];
    ]
  rhs := fun l _ =>
    let op := getOp l[0]
    [graphv2|
      i [io];
      o [io];

      fork [type=$(.dfg .fork)];
      read [type=$(.rw (.reads op.2.1))];
      write [type=$(.rw (.writes [op.2.2.1]))];
      op [type=$(.dfg (.op op.1))];

      i -> fork [to="in1"];
      write -> o [from="out1"];

      fork -> read [from="out1", to="in1"];
      fork -> write [from="out2", to="in1"];
      read -> op [from="out1", to="in1"];
      read -> op [from="out2", to="in2"];
      op -> write [from="out1", to="in2"];
    ]
  predicate := fun l =>
    let op := getOp l[0].type
    op.2.1.length == 2
  name := "translate-node-op2"

def inop : RewriteHigh String DFGandCFG where
  params := 1
  lhs := fun l _ =>
    let op := getInop l[0]
    [graphv2|
      i [io];
      o [io];

      op [type=$(.cfg (.Inop (getInop l[0])))];

      i -> op [to="in1"];
      op -> o [from="out1"];
    ]
  rhs := fun _ _ =>
    [graphv2|
      i [io];
      o [io];

      op [type=$(.dfg .queue)];

      i -> op [to="in1"];
      op -> o [from="out1"];
    ]
  name := "translate-node-inop"

def icond1 : RewriteHigh String DFGandCFG where
  params := 1
  lhs := fun l _ =>
    let op := getIcond l[0]
    [graphv2|
      i [io];
      o1 [io];
      o2 [io];

      op [type=$(.cfg (.Icond op.1 op.2.1 op.2.2.1 op.2.2.2))];

      i -> op [to="in1"];
      op -> o1 [from="out1"];
      op -> o2 [from="out2"];
    ]
  rhs := fun l _ =>
    let op := getIcond l[0]
    [graphv2|
      i [io];
      o1 [io];
      o2 [io];

      read [type=$(.rw (.reads op.2.1))];
      branch [type=$(.dfg .branch)];
      fork [type=$(.dfg .fork)];
      cop [type=$(.dfg (.cond op.1))];

      i -> fork.in1;
      fork.out1 -> read.in1;
      read.out1 -> cop.in1;
      cop.out1 -> branch.in2;
      fork.out2 -> branch.in1;
      branch.out1 -> o1;
      branch.out2 -> o2;
    ]
  predicate := fun l =>
    let op := getIcond l[0].type
    op.2.1.length == 1
  name := "translate-node-icond1"

def translate : RWTree (RewriteHigh String DFGandCFG) :=
  [op1, op2, icond1, inop].toRWTreeFix |>.get rfl

end Graphiti.CFG.TranslateNode
