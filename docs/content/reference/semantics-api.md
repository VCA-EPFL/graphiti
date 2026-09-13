+++
title = "Semantics API"
description = "Ports, modules, refinement, the two graph types, environments and the tactics used in proofs."
weight = 80
[menus.main]
  parent = "reference"
  weight = 80
+++

Everything on this page is in namespace `Graphiti`. Paths are relative to `Graphiti/Core`.

## Ports

Defined in `Types.lean`.

| Name | Definition |
| --- | --- |
| `InstIdent Ident` | `top` for the enclosing module, or `internal (i : Ident)` for a named instance. |
| `InternalPort Ident` | `inst : InstIdent Ident` and `name : Ident`. An `Ident` coerces to a port with `inst := .top`. |
| `IdentMap Ident α` | `Batteries.AssocList Ident α`. |
| `PortMap Ident α` | `Batteries.AssocList (InternalPort Ident) α`. |
| `PortMap.getIO l n` | The rule for port `n`, or `⟨PUnit, fun _ _ _ => False⟩` when `n` is absent. |
| `PortMapping Ident` | `input` and `output`, both `PortMap Ident (InternalPort Ident)`. Maps a component's ports to wire names. |
| `PortMapping.hashPortMapping` | Eight hex digits of a hash of the sorted mapping. Used as a node name. |
| `Interface Ident` | Lists of input and output ports. |

## Modules

Defined in `Graph/Module.lean`.

| Name | Definition |
| --- | --- |
| `RelIO S` | `Σ T : Type, S → T → S → Prop`, an input or output rule carrying a value of type `T`. |
| `RelInt S` | `S → S → Prop`, an internal rule. |
| `Module Ident S` | `inputs : PortMap Ident (RelIO S)`, `outputs : PortMap Ident (RelIO S)`, `internals : List (RelInt S)`, `init_state : S → Prop`. |
| `Module.empty S` | No ports, no internal rules, every state initial. |
| `Module.product m₁ m₂` | State `S × S'`. Ports and rules of both modules, each acting on its half of the state. |
| `Module.connect' m o i` | Removes output `o` and input `i` and adds an internal rule that fires both with the same value. The rule requires equal port types. |
| `Module.renamePorts m p` | Renames ports with the bijection built from `p`. |
| `Module.mapIdent f g m` | Changes the identifier type of input and output port names. |
| `existSR rules s s'` | `s'` is reachable from `s` by zero or more rules from `rules`. |
| `NatModule`, `StringModule` | `Module Nat` and `Module String`. |
| `NatModule.stringify m` | Renames input `n` to `in{n+1}` and output `n` to `out{n+1}`. |
| `TModule Ident`, `TModule1 Ident` | A module paired with its state type, `Σ T, Module Ident T`. `TModule1` fixes `T : Type`. |

## Refinement

Defined in `Graph/ModuleLemmas.lean`. `imod` has state `I` and `smod` has state `S`.

| Name | Definition |
| --- | --- |
| `MatchInterface imod smod` | Class. Both modules have the same input and output ports, with the same value types. |
| `comp_refines imod smod φ i s` | Every input, output and internal step of `imod` from `i` is matched by `smod` from `s`, ending in states related by `φ`. Inputs are matched by the input then internal steps, outputs by internal steps then the output, internal steps by internal steps. |
| `imod ⊑_{φ} smod` | `refines_φ`: `comp_refines` holds for every pair related by `φ`. |
| `Module.refines_initial imod smod φ` | Every initial state of `imod` is related to an initial state of `smod`. |
| `imod ⊑ smod` | `refines`: there exist a `MatchInterface` instance and a `φ` with `imod ⊑_{φ} smod` and `refines_initial`. |
| `imod ⊒ smod` | `smod ⊑ imod`. |
| `imod ≡ smod` | `equivalent`: refinement in both directions. |

Lemmas used throughout the proofs:

| Lemma | Statement |
| --- | --- |
| `Module.refines_reflexive` | `imod ⊑ imod`. |
| `Module.refines_transitive` | Refinement composes. |
| `Module.refines_product` | Refinement is preserved by `product` on both sides. |
| `Module.refines_connect` | Refinement is preserved by `connect'`. |
| `Module.refines_renamePorts` | Refinement is preserved by port renaming. |
| `Module.refines_product_associative`, `refines_product_commutative` | Products can be reassociated, and swapped when the modules are disjoint. |
| `Module.refines_eq_relax` | Rewrites both sides of a refinement along equalities of modules with different state types. |

## Transition systems and traces

| Name | File | Definition |
| --- | --- | --- |
| `StateTransition State Event` | `StateTransition.lean` | Class with `init` and `step : State → List Event → State → Prop`. |
| `s -[ t ]-> s'`, `s -[ t ]*> s'` | `StateTransition.lean` | One step and `star`, many steps. |
| `behaviour`, `reachable`, `future` | `StateTransition.lean` | Event lists possible from an initial state, states reachable by a list, and lists possible from a state. |
| `IOEvent Ident` | `Trace.lean` | `input p v` or `output p v`, where `v : Σ T, T`. |
| `Module.state_transition m` | `Trace.lean` | `m` as a `StateTransition` over `IOEvent`s. Internal steps produce no event. |
| `Module.trace_inclusion imp spec` | `Trace.lean` | Every behaviour of `imp` is a behaviour of `spec`. |
| `Module.refines_implies_trace_inclusion` | `Trace.lean` | `imp ⊑ spec → trace_inclusion imp spec`. |

`StateTrace.lean` defines another `Module.state_transition` whose events are the states visited.

## Graph expressions

| Name | File | Definition |
| --- | --- | --- |
| `Connection Ident` | `Graph/ExprLow.lean` | `output` and `input`, both `InternalPort Ident`. |
| `ExprLow Ident Typ` | `Graph/ExprLow.lean` | `base (map : PortMapping Ident) (typ : Typ)`, `product l r`, `connect (c : Connection Ident) e`. |
| `ExprHigh Ident Typ` | `Graph/ExprHigh.lean` | `modules : IdentMap Ident (PortMapping Ident × Typ)` and `connections : List (Connection Ident)`. |
| `ExprHigh.lower`, `lower_TR` | `Graph/ExprHigh.lean` | Nest the nodes into products and wrap them in connections. `none` for an empty graph. |
| `ExprLow.higher_correct f e` | `Graph/ExprHigh.lean` | Back to `ExprHigh`, naming nodes with `f`. `ExprLow.higher` uses `hashPortMapping`. |
| `ExprHigh.extract g names` | `Graph/ExprHigh.lean` | Splits `g` into the subgraph of `names` with its internal connections, and the rest. |
| `ExprHigh.renameModules`, `normaliseNames`, `normaliseNames_fast` | `Graph/ExprHigh.lean` | Rename nodes, and rename wires after the node that owns them. |
| `ExprHigh.hash_portmappings` | `Graph/ExprHigh.lean` | Rename nodes to their hashes and return the mapping back. |
| `ExprHigh.asDot` | `Graph/ExprHigh.lean` | DOT text. Also the `ToString` instance. |
| `ExprLow.weak_beq e e'` | `Graph/ExprLow.lean` | For terms of the same shape, the renaming of external and internal wires that turns `e` into `e'`. |
| `ExprLow.force_replace e e_sub e_new` | `Graph/ExprLow.lean` | Replaces subterms equal to `e_sub` and reports whether one was found. |
| `ExprLow.comm_bases`, `comm_connections'` | `Graph/ExprLow.lean` | Reorder products and connections without changing meaning. |
| `NextNode Ident Typ` | `Graph/ExprHigh.lean` | Result of `followOutput` and `followInput`. |

## Environments and building modules

| Name | File | Definition |
| --- | --- | --- |
| `Env Ident Typ` | `Graph/Environment.lean` | `Typ → Option (TModule1 Ident)`. |
| `FinEnv Ident Typ` | `Graph/Environment.lean` | `Batteries.AssocList Typ (TModule1 Ident)`. `FinEnv.toEnv` is lookup. |
| `Env.union`, `Env.subsetOf`, `Env.independent` | `Graph/Environment.lean` | Left-biased union, inclusion, and disjoint domains. |
| `FinEnv.max_typeD` | `Graph/Environment.lean` | Largest type number in the environment. |
| `ExprLow.build_module' ε e` | `Graph/ExprLowLemmas.lean` | The module of `e`: `renamePorts` for `base`, `connect'` for `connect`, `product` for `product`. `none` if a type is missing from `ε`. |
| `[e| e, ε ]`, `[T| e, ε ]` | `Graph/ExprLowLemmas.lean` | The module and the state type of `build_module ε e`, with the empty module as fallback. |
| `[Ge| g, ε ]` | `Graph/ExprHighLemmas.lean` | The same for an `ExprHigh` graph, through `lower`. |
| `ExprLow.wf`, `wf_mapping`, `well_formed` | `Graph/ExprLowLemmas.lean` | Every type is in `ε`. `well_formed` also requires each port mapping to cover exactly the component's ports and to be invertible. |
| `ExprLow.locally_wf` | `Graph/ExprLowLemmas.lean` | Every port mapping is invertible. |
| `ExprLow.well_typed ε e`, `ExprHigh.well_typed` | `Graph/WellTyped.lean` | Every connection joins ports of the same value type. |
| `Env.well_formed ε` | `Dataflow/Component.lean` | Each type named like a component maps to that component. See [Components]({{< relref "components" >}}). |

## Rewrite correctness

Defined in `RewriterLemmas.lean`, with `env_well_formed : Env String (String × Nat) → Prop` as a parameter.

| Name | Definition |
| --- | --- |
| `WellFormedEnv env_well_formed ε max_type` | `ε` satisfies `env_well_formed` and `ε.max_typeD ≤ max_type`. |
| `Environment env_well_formed lhs` | Class giving `ε`, `max_type`, `types`, and proofs that `lhs types` is well formed and well typed in `ε`. |
| `VerifiedRewrite env_well_formed rw ε` | `ε_ext`, `ε_ext_wf`, `ε_independent`, `rhs_wf`, `rhs_wt`, `lhs_locally_wf` and `refinement`. |
| `VerifiedConditionalRewrite` | Same fields as `VerifiedRewrite`. |
| `run'_refines` | Under a match, a well-formed and well-typed lowering and a `VerifiedRewrite`, the result of `Rewrite.run'` refines the input graph. |
| `run'_preserves_well_formed`, `run'_preserves_well_typed` | The result lowers to a term that is again well formed and well typed, in `ε_global ++ ε_ext`. |

## Simp sets

Registered in `Simp.lean`.

| Attribute | Contents |
| --- | --- |
| `drunfold` | Definitions to unfold when reducing modules. |
| `drcompute` | Lemmas and simprocs for computing with association lists and lists. |
| `drunfold_defs` | Top-level definitions of rewrites, such as `lhs` and `rhs`. |
| `drcomponents` | Definitions used to build `StringModule` components from `NatModule` ones. |
| `drenv` | Environment lookups proved in a rewrite proof. |
| `drlogic` | Propositional simplifications. |
| `drnat`, `drdecide`, `drcommon`, `drnorm`, `dmod` | Registered for smaller groups of lemmas. |

## Commands and tactics

| Name | File | Behaviour |
| --- | --- | --- |
| `def_module name : type := term reduction_by tac` | `Graph/ModuleReduction.lean` | Defines `name` as `term` after running `tac` on it at elaboration time. |
| `def_module name : type := term` | `Graph/ModuleReduction.lean` | The same with `dr_reduce_module`. |
| `defmodule` | `Graph/ModuleReduction.lean` | Variant that takes binders and states the reduction as an equation. |
| `dr_reduce_module` | `Graph/ModuleReduction.lean` | Unfolds `build_module`, environment lookups, renamings and products into a concrete `Module` record. |
| `solve_match_interface` | `Graph/ModuleReduction.lean` | Proves a `MatchInterface` goal for reduced modules. |
| `precomputeTac t by tac` | `Tactic.lean` | Runs `tac` on the expression `t` and uses the result. |
| `specializeAll t` | `Tactic.lean` | Instantiates every hypothesis whose first binder has the type of `t`. |
| `case_transition h : ct, i, ht` | `Tactic.lean` | Adds the hypothesis that port `i` is in `ct`, given a proof that its absence is contradictory. |
| `prove_refines_φ t` | `Tactic.lean` | Opens a `⊑_{φ}` goal into its input, output and internal cases. Handles one input and one output. |
| `have_hole` | `Tactic.lean` | A `have` whose proof may contain holes. |
| `named_sorry n` | `Tactic.lean` | Closes the goal with a new axiom named after the declaration and `n`. It shows up in `#print axioms`. |
