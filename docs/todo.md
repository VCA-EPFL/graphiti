- [Paper writing](#org2d498a8)
- [Framework development](#org0d2b586)
- [Preprocessing of dot-graph for Dynamatic](#org16e50df)
- [Post processing of dot-graph for Dynamatic](#org9b62e9b)
- [Non-main-project todos](#orgc5631ea)



<a id="org2d498a8"></a>

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


<a id="org0d2b586"></a>

# Framework development


## TODO Prove LHS specification given termination     :loop_rewrite:

-   **Effort:** 1 day(s)


## TODO Prove RHS Ghost to RHS     :loop_rewrite:

-   **Effort:** 1 day(s)


## TODO Prove φ holds for initial state     :loop_rewrite:

-   **Effort:** 0.25 day(s)


## TODO Lift loop rewrite into a verified rewrite     :loop_rewrite:

-   **Effort:** 0.5 day(s)


## SMDY Prove termination of the loop     :loop_rewrite:

Either:

-   prove that the loop terminates.
-   add fuel to the implementation which deadlocks when fuel is reached.


## TODO Adding environments to rewrites     :ORDERED:

-   **Effort:** 2 day(s)


<a id="org6e6e8ad"></a>

### TODO Generate a new environment from the rewrite     :environment:


### TODO Prove environment changes are monotonic     :environment:

1.  Dependencies

    -   [Generate a new environment from the rewrite](#org6e6e8ad)


## SMDY Make rewriter run in Lean 4     :rewriter:

-   Allows proofs using the the rewriter itself.
-   Allows the proof of transformations using the existing rewrite rules.
-   This could be done at runtime of the rewriter itself too, but this would provide more control.


## WAIT Lift the rewriter correctness proof to support environment extensions     :rewriter:

-   **Effort:** 1 day(s)


### Dependencies

-   [Generate a new environment from the rewrite](#org6e6e8ad)


## TODO Minimise the number of nodes that are rewritten     :rewriter:

-   **Effort:** 1 day(s)


## TODO Backwards rewriting     :ORDERED:

-   **Effort:** 4 day(s)


### TODO Improve debugging information for renaming in rewrites

Currently it is difficult to trace renaming problems. Use existing infrastructure to add more detailed renaming information.


### Rework renaming so that it is stable with respect to `higher` and `lower` transformations


<a id="org1366e4f"></a>

### TODO Add option to rewrite without renaming     :rewriter:


### TODO Backwards rewriting instead of abstraction     :rewriter:

-   The rewriter currently does not support performing a rewrite without renaming. Why is that?
-   Renaming should not be needed, the worst it will do is make the lower to higher conversion invalid, because some base components will not be able to be moved under some connections.

1.  Dependencies

    -   [Add option to rewrite without renaming](#org1366e4f)


## TODO Support rewriting of loop bodies with `if` statements     :rewriter:

-   **Effort:** 4 day(s)

-   This is needed for `gsum-single` and `gsum-many`.
-   We need to recursively generate pures and then apply the branch-merge to pure conversion.


<a id="org16e50df"></a>

# Preprocessing of dot-graph for Dynamatic

-   **Effort:** 1 day(s)


## TODO Split up read-only memory controllers intro their own banks

-   Attached to a single load.


## TODO Transform `Merge` into `init Bool false`

-   Remove the unnecessary additional input, and rewire the conditional input from in2 to in1.


## TODO Rewire the fork trees

-   I have found though that in all the cases for dot-graphs that you have sent me, the only thing I had to change is switch out2 which was feeding the init to out1. The rest of the fork tree then lined up. But having a more general solution would be useful too.


<a id="org9b62e9b"></a>

# Post processing of dot-graph for Dynamatic

-   **Effort:** 2 day(s)


## TODO Merge memories again

-   Ideally, we wouldn't need to do this, but I guess that this is because don't know how to synthesise the right arguments for the memory controllers.


## TODO Expand/Implement the tagger

-   Either expand the tagger into the implementation of FPGA'24, or implement the tagger from scratch.


<a id="orgc5631ea"></a>

# Non-main-project todos


## TODO Connect directly to bluespec back-end


## TODO Explore implementation of buffer size 0

-   Will require a reimplementation of
