# Notes

## Routing Policy

- We want to keep the routing policy deterministic, but we would like a router
  state for dynamic routing

- Router should probably also have the information about which output channels
  are full or not?

- Maybe it is not that important that `Data` can be modified by routers and we
  are only interested in modifying headers

- It is currently not really possible for a routing policy to drop packets / to
  broadcast them to multiple outputs.
  This should be fixable by making a routing policy return a `List` of output
  where to put packets.

## Correctness

We are currently only proving functional correctness, but it would be
interesting to prove deadlock and livelock freedom.

- Study how deadlock freedom is a liveness property in trace-based semantics:
  + Study how to express liveness property refinement.
    A thing would be to have a φ which is preserved with a ∀ instead of an ∃
  + Trace prefix equivalence in deterministic modules should be enough for
    liveness equivalence

For the routing policy:
- Prove that the strong correctness implies full equivalence

- Prove that the weak correctness implies one way refinement

- Prove that the strong correctness implies weak correctness

An interesting thing is that we have a non-deterministic model even though every
implementation is non-deterministic.
This makes some sense, but can also make verification harder?

## Proof of BuildExpr correctness

- Tried using Vector for `fin_range` to keep the length information in the type
  to avoid cast, did not work

## Implementation

- We want an implementation of an ordered router and show that it is correct, so
  that we can use it to implement a `Torus` router and we can actually extract
  it to hardware

- We need to clean up proofs and definitions, it is getting everywhere…

- We need to simplify `dep_foldr` when β is a product type, so when we are
  producing DPList'

- We cannot compile computable function into pure module unfortunately.
  We could have our own custom small language to do it

- We could have a `Router` implementation which depends on an `Arbiter`
  definition

- `Router` is a name which is too generic, we should probably instead have a
  router string along the line of `RelativeRouter 5 5 Data` or maybe first
  argument is `Router Arbiter RouterID`

## Compiling to hadrware

Our language is currently not compilable to hardware.

Problems:

- Our function are manipulating Lean4 values

- Buffer definition is defined with a transition relation

- Routing is a Lean4 function

## References

- Take a more in depth look at the P4 language

- Ask Thomas for more reference on routing strictly with routing tables

- Search for background on latency-insensitive NoC
