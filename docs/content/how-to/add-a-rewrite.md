+++
title = "Add a rewrite"
description = "Define a new graph rewrite, register it, and apply it from Lean or from the executable."
weight = 20
[menus.main]
  parent = "how-to"
  weight = 20
+++

This guide adds a rewrite called `queue-sink`. It removes a `queue` whose output goes straight into a `sink`, because
buffering values that are then thrown away changes nothing a user of the circuit can observe. The file follows the same
layout as `Graphiti/Core/Dataflow/Rewrites/PureSink.lean`, so use that file as a second example.

## Create the rewrite file

Create `Graphiti/Core/Dataflow/Rewrites/QueueSink.lean`:

```lean
module

public import Graphiti.Core.Rewriter
public import Graphiti.Core.Graph.ExprHighElaborator
public import Graphiti.Core.Dataflow.Component

@[expose] public section

namespace Graphiti.QueueSink

open StringModule

def matcher : Pattern String (String × Nat) 2 := fun g => do
  let (.some list) ← g.modules.foldlM (λ s inst (_pmap, typ) => do
       if s.isSome then return s
       unless "queue" == typ.1 do return none

       let (.some sink) := followOutput g inst "out1" | return none
       unless "sink" == sink.typ.1 do return none

       return some ([inst, sink.inst], #v[typ, sink.typ])
    ) none | MonadExceptOf.throw RewriteError.done
  return list

variable (types : Vector Nat 2)

def lhs : ExprHigh String (String × Nat) := [graph|
    i [type = "io"];

    queue [type = "queue", arg = $(types[0])];
    sink [type = "sink", arg = $(types[1])];

    i -> queue [to = "in1"];
    queue -> sink [from = "out1", to = "in1"];
  ]

def lhs_extract := (lhs types).extract ["queue", "sink"] |>.get rfl

theorem double_check_empty_snd : (lhs_extract types).snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower := (lhs_extract types).fst.lower.get rfl

variable (max_type : Nat)

def rhs : ExprHigh String (String × Nat) := [graph|
    i [type = "io"];

    sink [type = "sink", arg = $(max_type + 1)];

    i -> sink [to = "in1"];
  ]

def rhs_extract := (rhs max_type).extract ["sink"] |>.get rfl

def rhsLower := (rhs_extract max_type).fst.lower.get rfl

def findRhs mod := (rhs_extract 0).1.modules.find? mod |>.map Prod.fst

def rewrite : Rewrite String (String × Nat) :=
  { params := 2
    pattern := matcher
    rewrite := λ l n => ⟨lhsLower (l.map (·.2)), rhsLower n.2⟩
    name := "queue-sink"
    transformedNodes := [.none, findRhs "sink" |>.get rfl]
    fresh_types := fun x => (x.1, x.2 + 1)
  }

end Graphiti.QueueSink
```

When you adapt this to your own rewrite, keep these rules:

- The matcher returns node names in the same order as the list passed to `extract` in `lhs_extract`, and types in the
  same order as `types[0]`, `types[1]` and so on. `params` is the length of that type vector.
- The matcher throws `RewriteError.done` when it finds nothing. The loop combinators treat `done` as "try the next
  rewrite" and any other error as a failure.
- `double_check_empty_snd` checks by `rfl` that the extract list names every node in `lhs`. If it fails, a node is
  missing from the list.
- Nodes that the right-hand side creates get type numbers above `max_type`, and `fresh_types` advances the counter by
  the count you used. Here that is one.
- `transformedNodes` has one entry per matched node, in matcher order. Use `.none` for a node that disappears and
  `findRhs "name"` for the right-hand node that takes its place. List right-hand nodes with no left-hand counterpart in
  `addedNodes`. The log and the undo machinery read both lists.

## Register the rewrite

Add the import to `Graphiti/Core/Dataflow/Rewrites.lean`:

```lean
public import Graphiti.Core.Dataflow.Rewrites.QueueSink
```

If the rewrite will ever run inside `withUndo`, also add `QueueSink.rewrite` to the `rewrite_index` list in the same
file. `reverseRewrites` finds rewrites to undo by their name in that list and fails with
`'queue-sink' reverse rewrite generation failed` when a name is missing.

## Apply it from Lean

Run it once with `Rewrite.run`, or until it stops matching with `rewrite_fix`:

```lean
#eval match (rewrite_fix [QueueSink.rewrite] g).run st with
  | .ok g' _ => IO.println g'
  | .error e _ => IO.println e
```

Here `g` is an `ExprHigh String (String × Nat)` and `st` is a `RewriteState` whose `fresh_type` is above every type
number in `g`.

## Apply it from the executable

`Dataflow.lean` groups rewrites into lists and applies each list at a fixed point during a pipeline stage. Add
`QueueSink.rewrite` to the list where it belongs. For a clean-up rewrite like this one, that is `reduceSink`:

```lean
def reduceSink := [SplitSinkRight.rewrite, SplitSinkLeft.rewrite, PureSink.rewrite, QueueSink.rewrite]
```

Then rebuild with `lake build graphiti`.

## Add a test

Create `GraphitiTest/Core/Dataflow/QueueSink.lean`. The `GraphitiTest` library picks up every file under that
directory, so no other registration is needed:

```lean
import Graphiti.Core.Rewriter
import Graphiti.Core.Graph.ExprHighElaborator
import Graphiti.Core.Dataflow.Rewrites.QueueSink

namespace Graphiti.QueueSink.Test

def buffered : ExprHigh String (String × Nat) := [graph|
    src [type = "io"];

    q [type = "queue", arg = $(0)];
    s [type = "sink", arg = $(1)];

    src -> q [to = "in1"];
    q -> s [from = "out1", to = "in1"];
  ]

/-- info: true -/
#guard_msgs in
#eval match (rewrite.run buffered).run
    { (default : RewriteState String (String × Nat)) with fresh_type := ("", 2) } with
  | .ok g _ => g.modules.valsList.map (·.2) == [("sink", 3)]
  | .error _ _ => false

end Graphiti.QueueSink.Test
```

Run `lake test`. The test fails if the rewrite stops producing a single `sink` of type `("sink", 3)`.

## Next step

A rewrite added this way runs, but nothing proves it correct yet. To prove it, follow
[Prove a rewrite correct]({{< relref "prove-a-rewrite-correct" >}}).

Projects that need many small rewrites can skip the hand-written matcher. `create_rewrite` and `RewriteHigh` in
`Graphiti/Core/Rewriter.lean` build the matcher from the left-hand graph with `defaultMatcher`. `Graphiti/Projects/CFG`
uses that style.
