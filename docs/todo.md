- [Paper writing](#orge7def0a)
- [Framework development](#orga0bd1c8)
- [Preprocessing of dot-graph for Dynamatic](#orgb73bf34)
- [Post processing of dot-graph for Dynamatic](#orgb7b0723)



<a id="orge7def0a"></a>

# Paper writing


## TODO Section 1: introduction


### TODO Add section structure to introduction


### TODO Add more references


## TODO Section 2: reread the motivation section


## TODO Section 3: add signposting and address comments


## TODO Section 3: rewrite introduction of syntax and semantics


## TODO Section 3: better introduce dot graph syntax in fork example


## TODO Section 3: add a concrete example of rewriting


## TODO Section 4: add signposting and make refinement definition more concrete


## TODO Section 5: make sure overall rewriting algorithm is clear


## TODO Section 5: describe pure generation in more detail


## TODO Section 6: describe the use of ghost state


## TODO Section 7: ensure text described experiments performed


## TODO Section 7: describe the implementation of the tagger used


## TODO Section 8: describe Lean MLIR in related work


## TODO Section 8: describe Cigr/Cilan more accurately


## TODO Section 8: add related work on graph rewriting (with applications in SSA), as well as term rewriting for hardware


<a id="orga0bd1c8"></a>

# Framework development


## TODO Prove LHS specification given termination     :loop_rewrite:


## TODO Prove RHS Ghost to RHS     :loop_rewrite:


## TODO Prove φ holds for initial state     :loop_rewrite:


## TODO Lift loop rewrite into a verified rewrite     :loop_rewrite:


## SMDY Prove termination of the loop     :loop_rewrite:

Either:

-   prove that the loop terminates.
-   add fuel to the implementation which deadlocks when fuel is reached.


## TODO Adding environments to rewrites     :ORDERED:


<a id="org0b44596"></a>

### TODO Generate a new environment from the rewrite     :environment:


### TODO Prove environment changes are monotonic     :environment:

1.  Dependencies

    -   [Generate a new environment from the rewrite](#org0b44596)


## SMDY Make rewriter run in Lean 4     :rewriter:

-   Allows proofs using the the rewriter itself.
-   Allows the proof of transformations using the existing rewrite rules.
-   This could be done at runtime of the rewriter itself too, but this would provide more control.


## WAIT Lift the rewriter correctness proof to support environment extensions     :rewriter:


### Dependencies

-   [Generate a new environment from the rewrite](#org0b44596)


## TODO Minimise the number of nodes that are rewritten     :rewriter:


## TODO Backwards rewriting     :ORDERED:


<a id="org1be65ba"></a>

### TODO Add option to rewrite without renaming     :rewriter:


### TODO Backwards rewriting instead of abstraction     :rewriter:

-   The rewriter currently does not support performing a rewrite without renaming. Why is that?
-   Renaming should not be needed, the worst it will do is make the lower to higher conversion invalid, because some base components will not be able to be moved under some connections.

1.  Dependencies

    -   [Add option to rewrite without renaming](#org1be65ba)


## TODO Support rewriting of loop bodies with `if` statements     :rewriter:

-   This is needed for `gsum-single` and `gsum-many`.
-   We need to recursively generate pures and then apply the branch-merge to pure conversion.


<a id="orgb73bf34"></a>

# Preprocessing of dot-graph for Dynamatic


## TODO Split up read-only memory controllers intro their own banks

-   Attached to a single load.


## TODO Transform `Merge` into `init Bool false`

-   Remove the unnecessary additional input, and rewire the conditional input from in2 to in1.


## TODO Rewire the fork trees

-   I have found though that in all the cases for dot-graphs that you have sent me, the only thing I had to change is switch out2 which was feeding the init to out1. The rest of the fork tree then lined up. But having a more general solution would be useful too.


<a id="orgb7b0723"></a>

# Post processing of dot-graph for Dynamatic


## TODO Merge memories again

-   Ideally, we wouldn't need to do this, but I guess that this is because don't know how to synthesise the right arguments for the memory controllers.


## TODO Expand/Implement the tagger

-   Either expand the tagger into the implementation of FPGA'24, or implement the tagger from scratch.
