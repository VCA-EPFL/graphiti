# Checklist to turn a Dynamatic graph into a Graphiti one

1. `Merge` node to `init Bool false` node
   - rename `in2` to `in1` and remove the previous `in1` port and edges.
2. Rearrange fork outputs so that they match between the `branch` and `fork` nodes.
   - `out1` of the fork which connects to the `branch` should feed to the `init Bool false`.
   - Otherwise, `out2` of the `branch` fork should match `out1` of the `mux` fork.
3. Rearrange fork outputs for `branch` and `mux` inside of the loop.
   - There should be three forks, one top-level fork which drives two lower-level forks (one for the `branch` and one
     for the `mux`).
   - `out1` of the top-level fork should drive the fork meant for `branch`.
   - `out2` of the top-level fork should drive the fork meant for `mux`.
4. Split up `MC`s
   - Make sure that any connections to `end` are also removed.
   - Renaming MC inputs and outputs to `in1` and `out1`.
