# Notes

## Noc language

- `UnboundedQueueInUnboundedBag` could be proven using `RouterIn`

## Routing Policy

- The `Route` function is currently necessarily deterministic, which we don't
  want

## Routers

- `Router.init_state` should be a relation

- Non homogeneous routers: They are a huge pain and should be left for later

## Interesting for later

- Study how deadlock freedom is a liveness property in trace-based semantics:
  + Study how to express liveness property refinement. A thing would be to have
    a φ which is preserved with a ∀ instead of an ∃

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

- With insight, we could have sort of compiled to Constellation right?

## Compiling to hadrware

- We have the problem of component names:
  + We currently consider `Router` to be a bit of a magic type, which only take
    one argument, the RouterID. We should probably instead consider a more
    careful naming, where the router take as a parameter the routing policy
    (Which itself might be dependent on Data type and other stuff?)
    We currently have `Router 0`, but would maybe want:
    `RouterBounded Data (ArbiterAbsolute Topology Data RouterID) RouterID`
    Maybe we could change the Noc language and merge `RoutingPolicy` into `Router`,
    but the problem is that at a language level they are different things, but
    when instantiated they become related.
    OR: In our build expr, we would instead want to have a RoutingPolicy (Wich
    really should be renamed to arbiter), and also build using this arbiter,
    which would make a lot more sense.
    But this would require having extra `output / input` to Router, which
    would be annoying, and would split the router significantly.
    The solution where the arbiter is just part of the router from a noc level
    might be easier for the purpose

## Current limitations

- Necessarily uniform routers
- Routers are necessarily deterministic
- Routers only have one initial state

## Design choices

- We have embedded the `FlitHeader` into the `Noc` definition to allow
  refinement. We could consider relying on the user to embed it into `Data`, but
  we wouldn't be able to compare multiple `Noc` implementation this way
