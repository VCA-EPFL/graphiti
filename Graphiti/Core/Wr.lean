/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

/--
Wrapper type which can be used to try and reduce reduction of types during
elaboration.  However, this does not prevent reduction in definitions, so even
just a simple program can lead to expensive evaluation.

```
def unwrap (t : Wr (expensive_type' 1000)) : expensive_type' 1000 := t.unwrap
```

Reduction of types occurs when elaborating an identifier.  In this case `t` is
elaborated, but the type does not have to be reduced.  Intead, the type does end
up getting reduced when elaborating the definition of the function.
-/
structure Wr (T : Type _) where
  unwrap : T
deriving Repr, Inhabited, Hashable, DecidableEq, Ord
