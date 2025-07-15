/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Rewriter
import Graphiti.ExprHighElaborator

namespace Graphiti.PureSeqComp

open StringModule

variable (T₁ T₂ T₃ : Type)
variable (f : T₁ → T₂) (g : T₂ → T₃)
variable (S₁ S₂ S₃ : String)

def matcher (g : ExprHigh String) : RewriteResult (List String × List String) := do
  let (.some list) ← g.modules.foldlM (λ s inst (pmap, typ) => do
       if s.isSome then return s
       unless "pure".isPrefixOf typ do return none

       let (.some join) := followOutput g inst "out1" | return none
       unless "pure".isPrefixOf join.typ do return none

       let (.some t1) := typ.splitOn |>.get? 1 | return none
       let (.some t2) := typ.splitOn |>.get? 2 | return none
       let (.some t2') := join.typ.splitOn |>.get? 1 | return none
       let (.some t3) := join.typ.splitOn |>.get? 2 | return none

       unless t2 = t2' do return none

       return some ([inst, join.inst], [t1, t2, t3])
    ) none | MonadExceptOf.throw RewriteError.done
  return list

def lhs : ExprHigh String × IdentMap String (TModule1 String) := [graphEnv|
    i_0 [type = "io"];
    o_out [type = "io"];

    puref [typeImp = $(⟨_, StringModule.pure f⟩), type = $(s!"pure {S₁} {S₂}")];
    pureg [typeImp = $(⟨_, StringModule.pure g⟩), type = $(s!"pure {S₂} {S₃}")];

    i_0 -> puref [to="in1"];

    puref -> pureg [from="out1", to="in1"];

    pureg -> o_out [from="out1"];
  ]

def lhs_extract := (lhs Unit Unit Unit (λ _ => default) (λ _ => default) S₁ S₂ S₃).fst.extract ["puref", "pureg"] |>.get rfl

theorem double_check_empty_snd : (lhs_extract S₁ S₂ S₃).snd = ExprHigh.mk ∅ ∅ := by rfl

def lhsLower := (lhs_extract S₁ S₂ S₃).fst.lower.get rfl

def rhs : ExprHigh String × IdentMap String (TModule1 String) := [graphEnv|
    i_0 [type = "io"];
    o_out [type = "io"];

    pure [typeImp = $(⟨_, StringModule.pure (g ∘ f)⟩), type = $(s!"pure {S₁} {S₃}")];

    i_0 -> pure [to="in1"];
    pure -> o_out [from="out1"];
  ]

def rhsLower := (rhs Unit Unit Unit (λ _ => default) (λ _ => default) S₁ S₃).fst.lower.get rfl

def findRhs mod := (rhs Unit Unit Unit (λ _ => default) (λ _ => default) "" "").1.modules.find? mod |>.map Prod.fst

def rewrite : Rewrite String :=
  { abstractions := [],
    pattern := matcher,
    rewrite := λ | [S₁, S₂, S₃] => .some ⟨lhsLower S₁ S₂ S₃, rhsLower S₁ S₃⟩ | _ => failure,
    name := "pure-seq-comp"
    transformedNodes := [.none, .none]
    addedNodes := [findRhs "pure" |>.get rfl]
  }

def generateRenamingPortMap (p1 p2 : PortMap String (InternalPort String)) : Option (PortMap String (InternalPort String)) :=
  p1.foldlM (λ pm k v => do
    let v' ← p2.find? k
    pm.cons v v'
  ) ∅

def generateRenamingPortMapping (p1 p2 : PortMapping String) : Option (PortMapping String) := do
  let inp ← generateRenamingPortMap p1.input p2.input
  let out ← generateRenamingPortMap p1.output p2.output
  .some ⟨inp, out⟩

def combinePortMapping (p : List (PortMapping String)) : PortMapping String := p.foldl (· ++ ·) ∅

def getPortMaps (g : ExprHigh String) : List (PortMapping String) :=
  g.modules.toList.map (λ (x, (y, z)) => y)

def getPortMaps' : ExprLow String → List (PortMapping String)
| .base inst typ => [inst]
| .connect c e => getPortMaps' e
| .product e₁ e₂ => getPortMaps' e₁ ++ getPortMaps' e₂

def generateRenaming (l : List (PortMapping String)) (e : ExprLow String) : Option (PortMapping String) :=
  (l.zip (getPortMaps' e))
  |>.mapM (Function.uncurry generateRenamingPortMapping)
  |>.map combinePortMapping

/--
Generate a reverse rewrite from a rewrite and the RewriteInfo associated with the execution.
-/
def reverse_rewrite (rw : Rewrite String) (rinfo : RewriteInfo) : RewriteResult (Rewrite String) := do
  let lhsNodes ← ofOption (.error "reverse_rewrite: nodes not found")
    <| rinfo.matched_subgraph.mapM (λ x => rinfo.input_graph.modules.find? x |>.map Prod.fst)

  let rhsNodes_renamed' := rinfo.renamed_input_nodes.toList.flatMap (λ (x, y) => y.toList)
  let rhsNodes_renamed ← ofOption (.error "reverse_rewrite: nodes not found")
    <| rhsNodes_renamed'.mapM (λ x => rinfo.output_graph.modules.find? x |>.map Prod.fst)
  let rhsNodes_added ← ofOption (.error "reverse_rewrite: nodes not found")
    <| rinfo.new_output_nodes.mapM (λ x => rinfo.output_graph.modules.find? x |>.map Prod.fst)
  let rhsNodes' := rhsNodes_renamed' ++ rinfo.new_output_nodes
  let rhsNodes := rhsNodes_renamed ++ rhsNodes_added

  -- TODO: add types into rinfo
  let (_nodes, [A, B, C]) ← matcher rinfo.input_graph
    | throw (.error "reverse_rewrite: matcher returned unexpected results")

  let def_rewrite ← ofOption (.error "could not generate rewrite") <| rw.rewrite [A, B, C]

  let rhs_renaming ← ofOption (.error "could not generate renaming map")
    <| generateRenaming rhsNodes def_rewrite.output_expr

  let lhs_renaming ← ofOption (.error "could not generate renaming map")
    <| generateRenaming lhsNodes def_rewrite.input_expr

  let full_renaming := rhs_renaming ++ lhs_renaming

  -- let newLhs := lhs_extract A B C
  -- let lhs_renaming ← ofOption (.error "could not generate renaming map")
  --   <| (addedNodes.zip (getPortMaps newLhs.1) |>.mapM (Function.uncurry generateRenamingPortMapping) |>.map combinePortMapping)
  -- let lr_renaming := lhs_renaming ++ rhs_renaming
  -- let newReplacedRhs ← ofOption (.error "renaming failed") <| newRhs.1.renamePorts hashPortMapping lr_renaming
  -- let newRhsLowered ← ofOption (.error "could not lower") newReplacedRhs.lower

  -- -- let addedNodesMap := newLhs.1.modules.keysList.zip addedNodes |>.toAssocList
  -- -- let newLhsConnections ← ofOption (.error "connections failed") <|
  -- --   newLhs.1.connections.mapM (λ | ⟨⟨.internal x, y⟩, ⟨.internal w, z⟩⟩ => do
  -- --                                  let newXInst ← addedNodesMap.find? x
  -- --                                  let newXPort ← newXInst.output.find? ⟨.top, y⟩
  -- --                                  let newWInst ← addedNodesMap.find? w
  -- --                                  let newWPort ← newWInst.input.find? ⟨.top, z⟩
  -- --                                  return ⟨newXPort, newWPort⟩
  -- --                                | _ => failure)
  -- -- let newLhsReplaced : ExprHigh String := ⟨(newLhs.1.modules.toList.zip addedNodes).map (λ (x, a) => (x.1, (a, x.2.2))) |>.toAssocList, newLhsConnections⟩
  -- let newLhsReplaced ← ofOption (.error "could not rename 2") <| newLhs.1.renamePorts hashPortMapping lr_renaming
  -- let newLhsLowered ← ofOption (.error "could not lower") newLhsReplaced.lower

  let lhs_renamed ← ofOption (.error "could not rename") <| def_rewrite.input_expr.renamePorts full_renaming
  let rhs_renamed ← ofOption (.error "could not rename") <| def_rewrite.output_expr.renamePorts full_renaming

  return ({ pattern := λ _ => return (rhsNodes', []),
            rewrite := λ _ => some ⟨rhs_renamed, lhs_renamed⟩,
            name := "rev-pure-seq-comp",
            -- TODO: These dictate ordering of nodes quite strictly.
            transformedNodes := rhsNodes_renamed.map some ++ rhsNodes_added.map (λ _ => none),
            addedNodes := lhsNodes.drop rhsNodes_renamed.length
          })

end Graphiti.PureSeqComp
