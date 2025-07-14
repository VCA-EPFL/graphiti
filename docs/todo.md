- [Roadmap for Graphiti](#org1b908c0)
  - [Paper writing](#org6c3d77d)
    - [Section 1: introduction](#orga87a72e)
    - [Section 2: reread the motivation section](#orgd76056c)
    - [Section 3: add signposting and address comments](#org0c542e0)
    - [Section 3: rewrite introduction of syntax and semantics](#orgf1c77c9)
    - [Section 3: better introduce dot graph syntax in fork example](#orga4e5864)
    - [Section 3: add a concrete example of rewriting](#org6213b84)
    - [Section 4: add signposting and make refinement definition more concrete](#orge6c3657)
    - [Section 5: make sure overall rewriting algorithm is clear](#org2f83401)
    - [Section 5: describe pure generation in more detail](#org3c1f78e)
    - [Section 6: describe the use of ghost state](#orgfe23e4f)
    - [Section 7: ensure text described experiments performed](#org205df50)
    - [Section 7: describe the implementation of the tagger used](#orgae62951)
    - [Section 8: describe Lean MLIR in related work](#orgcf2cb03)
    - [Section 8: describe Cigr/Cilan more accurately](#org4cc4002)
    - [Section 8: add related work on graph rewriting (with applications in SSA), as well as term rewriting for hardware](#org63db07a)
  - [Framework development](#org8374618)
    - [Prove LHS specification given termination](#orgff89550)
    - [Prove RHS Ghost to RHS](#org08dfb8a)
    - [Prove φ holds for initial state](#org68d2f89)
    - [Lift loop rewrite into a verified rewrite](#org0ee8f59)
    - [Prove termination of the loop](#org2e9b496)
    - [Adding environments to rewrites](#org018245b)
    - [Make rewriter run in Lean 4](#org8e41f92)
    - [Lift the rewriter correctness proof to support environment extensions](#org374ee23)
    - [Minimise the number of nodes that are rewritten](#org5e97f00)
    - [Backwards rewriting](#orgb4dc79a)
    - [Support rewriting of loop bodies with `if` statements](#org9a644a8)
  - [Preprocessing of dot-graph for Dynamatic](#org4607a2f)
    - [Split up read-only memory controllers intro their own banks](#orgf366ba8)
    - [Transform `Merge` into `init Bool false`](#orgc434b69)
    - [Rewire the fork trees](#org8c46b37)
  - [Post processing of dot-graph for Dynamatic](#org35ca9e8)
    - [Merge memories again](#org2789b72)
    - [Expand/Implement the tagger](#org4845622)



<a id="org1b908c0"></a>

# Roadmap for Graphiti


<a id="org6c3d77d"></a>

## Paper writing


<a id="orga87a72e"></a>

### TODO Section 1: introduction

1.  TODO Add section structure to introduction

2.  TODO Add more references


<a id="orgd76056c"></a>

### TODO Section 2: reread the motivation section


<a id="org0c542e0"></a>

### TODO Section 3: add signposting and address comments


<a id="orgf1c77c9"></a>

### TODO Section 3: rewrite introduction of syntax and semantics


<a id="orga4e5864"></a>

### TODO Section 3: better introduce dot graph syntax in fork example


<a id="org6213b84"></a>

### TODO Section 3: add a concrete example of rewriting


<a id="orge6c3657"></a>

### TODO Section 4: add signposting and make refinement definition more concrete


<a id="org2f83401"></a>

### TODO Section 5: make sure overall rewriting algorithm is clear


<a id="org3c1f78e"></a>

### TODO Section 5: describe pure generation in more detail


<a id="orgfe23e4f"></a>

### TODO Section 6: describe the use of ghost state


<a id="org205df50"></a>

### TODO Section 7: ensure text described experiments performed


<a id="orgae62951"></a>

### TODO Section 7: describe the implementation of the tagger used


<a id="orgcf2cb03"></a>

### TODO Section 8: describe Lean MLIR in related work


<a id="org4cc4002"></a>

### TODO Section 8: describe Cigr/Cilan more accurately


<a id="org63db07a"></a>

### TODO Section 8: add related work on graph rewriting (with applications in SSA), as well as term rewriting for hardware


<a id="org8374618"></a>

## Framework development


<a id="orgff89550"></a>

### TODO Prove LHS specification given termination     :loop_rewrite:


<a id="org08dfb8a"></a>

### TODO Prove RHS Ghost to RHS     :loop_rewrite:


<a id="org68d2f89"></a>

### TODO Prove φ holds for initial state     :loop_rewrite:


<a id="org0ee8f59"></a>

### TODO Lift loop rewrite into a verified rewrite     :loop_rewrite:


<a id="org2e9b496"></a>

### SMDY Prove termination of the loop     :loop_rewrite:

Either:

-   prove that the loop terminates.
-   add fuel to the implementation which deadlocks when fuel is reached.


<a id="org018245b"></a>

### TODO Adding environments to rewrites     :ORDERED:

1.  TODO Generate a new environment from the rewrite     :environment:

2.  TODO Prove environment changes are monotonic     :environment:

    1.  Dependencies
    
        -   [Generate a new environment from the rewrite](#orga2a9235)


<a id="org8e41f92"></a>

### SMDY Make rewriter run in Lean 4     :rewriter:

-   Allows proofs using the the rewriter itself.
-   Allows the proof of transformations using the existing rewrite rules.
-   This could be done at runtime of the rewriter itself too, but this would provide more control.


<a id="org374ee23"></a>

### WAIT Lift the rewriter correctness proof to support environment extensions     :rewriter:

1.  Dependencies

    -   [Generate a new environment from the rewrite](#orga2a9235)


<a id="org5e97f00"></a>

### TODO Minimise the number of nodes that are rewritten     :rewriter:


<a id="orgb4dc79a"></a>

### TODO Backwards rewriting     :ORDERED:

1.  TODO Add option to rewrite without renaming     :rewriter:

2.  TODO Backwards rewriting instead of abstraction     :rewriter:

    -   The rewriter currently does not support performing a rewrite without renaming. Why is that?
    -   Renaming should not be needed, the worst it will do is make the lower to higher conversion invalid, because some base components will not be able to be moved under some connections.
    
    1.  Dependencies
    
        -   [Add option to rewrite without renaming](#org30492e3)


<a id="org9a644a8"></a>

### TODO Support rewriting of loop bodies with `if` statements     :rewriter:

-   This is needed for `gsum-single` and `gsum-many`.
-   We need to recursively generate pures and then apply the branch-merge to pure conversion.


<a id="org4607a2f"></a>

## Preprocessing of dot-graph for Dynamatic


<a id="orgf366ba8"></a>

### TODO Split up read-only memory controllers intro their own banks

-   Attached to a single load.


<a id="orgc434b69"></a>

### TODO Transform `Merge` into `init Bool false`

-   Remove the unnecessary additional input, and rewire the conditional input from in2 to in1.


<a id="org8c46b37"></a>

### TODO Rewire the fork trees

-   I have found though that in all the cases for dot-graphs that you have sent me, the only thing I had to change is switch out2 which was feeding the init to out1. The rest of the fork tree then lined up. But having a more general solution would be useful too.


<a id="org35ca9e8"></a>

## Post processing of dot-graph for Dynamatic


<a id="org2789b72"></a>

### TODO Merge memories again

-   Ideally, we wouldn't need to do this, but I guess that this is because don't know how to synthesise the right arguments for the memory controllers.


<a id="org4845622"></a>

### TODO Expand/Implement the tagger

-   Either expand the tagger into the implementation of FPGA'24, or implement the tagger from scratch.
