import Graphiti.Tactic

set_option autoImplicit false

inductive Node where
  | done
  | epsilon (next : Nat)

def Node.InBounds (n : Node) (size : Nat) : Prop :=
  match n with
  | .done => True
  | .epsilon next => next < size

def WF (nodes : Array Node) : Prop := ∀ i : Fin nodes.size, nodes[i].InBounds nodes.size

def WF.InBounds {nodes : Array Node} {node : Node} (wf : WF nodes) (i : Fin nodes.size) (hn : nodes[i] = node) : node.InBounds nodes.size :=
  hn ▸ wf i

def getNext (nodes : Array Node) (wf : WF nodes) (state : Fin nodes.size) : Option (Fin nodes.size) :=
  match h : nodes[state] with
  | .done => .none
  | .epsilon next =>
    -- This proof makes `rw` fail with `motive is not type correct`. It seems that `rw` tries to rewrite the proof as well?
    have isLt : next < nodes.size := wf.InBounds state h
    some ⟨next, isLt⟩

set_option pp.proofs true in
theorem getNext_done {nodes : Array Node} {wf : WF nodes} {state : Fin nodes.size} (h : nodes[state] = .done) :
  getNext nodes wf state = .none := by
  unfold getNext
  rewrite! [h]
