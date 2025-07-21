- [Paper writing <code>[0/15]</code>](#orgb9b2529)
- [Framework development <code>[2/13]</code>](#org9902882)
- [Preprocessing of dot-graph for Dynamatic <code>[0/3]</code>](#org519f7c8)
- [Post processing of dot-graph for Dynamatic <code>[0/4]</code>](#org5252620)
- [Non-main-project todos <code>[0/4]</code>](#org95c0e02)



<a id="orgb9b2529"></a>

# Paper writing <code>[0/15]</code>

1.  TODO Section 1: introduction

    1.  TODO Add section structure to introduction
    
    2.  TODO Add more references

2.  TODO Section 2: reread the motivation section

3.  TODO Section 3: add signposting and address comments

4.  TODO Section 3: rewrite introduction of syntax and semantics

5.  TODO Section 3: better introduce dot graph syntax in fork example

6.  TODO Section 3: add a concrete example of rewriting

7.  TODO Section 4: add signposting and make refinement definition more concrete

8.  TODO Section 5: make sure overall rewriting algorithm is clear

9.  TODO Section 5: describe pure generation in more detail

10. TODO Section 6: describe the use of ghost state

11. TODO Section 7: ensure text described experiments performed

12. TODO Section 7: describe the implementation of the tagger used

13. TODO Section 8: describe Lean MLIR in related work

14. TODO Section 8: describe Cigr/Cilan more accurately

15. TODO Section 8: add related work on graph rewriting (with applications in SSA), as well as term rewriting for hardware


<a id="org9902882"></a>

# Framework development <code>[2/13]</code>

1.  TODO Prove LHS specification given termination     :loop_rewrite:

    -   **Effort:** 1d day(s)

2.  TODO Prove RHS Ghost to RHS     :loop_rewrite:

    -   **Effort:** 1d day(s)

3.  TODO Prove φ holds for initial state     :loop_rewrite:

    -   **Effort:** 0.25d day(s)

4.  TODO Lift loop rewrite into a verified rewrite     :loop_rewrite:

    -   **Effort:** 0.5d day(s)

5.  SMDY Prove termination of the loop     :loop_rewrite:

    Either:
    
    -   prove that the loop terminates.
    -   add fuel to the implementation which deadlocks when fuel is reached.

6.  TODO Adding environments to rewrites     :ORDERED:

    -   **Effort:** 2d day(s)
    
    1.  TODO Generate a new environment from the rewrite     :environment:
    
    2.  TODO Prove environment changes are monotonic     :environment:
    
        1.  Dependencies
        
            -   [Generate a new environment from the rewrite](#org8dd143b)

7.  SMDY Make rewriter run in Lean 4     :rewriter:

    -   Allows proofs using the the rewriter itself.
    -   Allows the proof of transformations using the existing rewrite rules.
    -   This could be done at runtime of the rewriter itself too, but this would provide more control.

8.  WAIT Lift the rewriter correctness proof to support environment extensions     :rewriter:

    -   **Effort:** 1d day(s)
    
    1.  Dependencies
    
        -   [Generate a new environment from the rewrite](#org8dd143b)

9.  DONE Minimise the number of nodes that are rewritten     :rewriter:

    -   **Effort:** 1d day(s)

10. DONE Backwards rewriting     :ORDERED:

    -   **Effort:** 4d day(s)
    
    1.  DONE Improve debugging information for renaming in rewrites
    
        Currently it is difficult to trace renaming problems. Use existing infrastructure to add more detailed renaming information.
    
    2.  DONE Rework renaming so that it is stable with respect to `higher` and `lower` transformations
    
    3.  DONE Add option to rewrite without renaming     :rewriter:
    
    4.  DONE Backwards rewriting instead of abstraction     :rewriter:
    
        -   The rewriter currently does not support performing a rewrite without renaming. Why is that?
        -   Renaming should not be needed, the worst it will do is make the lower to higher conversion invalid, because some base components will not be able to be moved under some connections.
        
        1.  Dependencies
        
            -   [Add option to rewrite without renaming](#orgd54012a)

11. TODO Support rewriting of loop bodies with `if` statements     :rewriter:

    -   **Effort:** 4d day(s)
    
    -   This is needed for `gsum-single` and `gsum-many`.
    -   We need to recursively generate pures and then apply the branch-merge to pure conversion.

12. TODO Improve the performance of rewriting by only checking for invertibility once     :rewriter:

13. SMDY Improve on the universe bounds in proofs

    -   Currently many of the proofs limit universes within module inputs/outputs as well as the environment.


<a id="org519f7c8"></a>

# Preprocessing of dot-graph for Dynamatic <code>[0/3]</code>

-   **Effort:** 2d day(s)

1.  TODO Split up read-only memory controllers intro their own banks

    -   Attached to a single load.

2.  TODO Transform `Merge` into `init Bool false`

    -   Remove the unnecessary additional input, and rewire the conditional input from in2 to in1.

3.  TODO Rewire the fork trees

    -   I have found though that in all the cases for dot-graphs that you have sent me, the only thing I had to change is switch out2 which was feeding the init to out1. The rest of the fork tree then lined up. But having a more general solution would be useful too.


<a id="org5252620"></a>

# Post processing of dot-graph for Dynamatic <code>[0/4]</code>

-   **Effort:** 4d day(s)

1.  TODO Merge memories again

    -   Ideally, we wouldn't need to do this, but I guess that this is because don't know how to synthesise the right arguments for the memory controllers.

2.  TODO Expand/Implement the tagger

    -   Either expand the tagger into the implementation of FPGA'24, or implement the tagger from scratch.

3.  TODO Adhere to the research codebase manifesto

    -   <https://www.moderndescartes.com/essays/research_code/>

4.  TODO Support split and join of tag in loop body


<a id="org95c0e02"></a>

# Non-main-project todos <code>[0/4]</code>

1.  TODO Connect directly to bluespec back-end

2.  TODO Explore implementation of buffer size 0

    -   Will require a reimplementation of

3.  TODO Verify abstraction

4.  TODO Verify concretisation
