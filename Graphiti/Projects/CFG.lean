/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Core.Simp
import Graphiti.Core.AssocList.Basic
import Graphiti.Core.Graph.Module
import Graphiti.Core.Graph.ExprHigh
import Graphiti.Core.Graph.Environment
import Graphiti.Core.Graph.ExprHighElaborator
import Graphiti.Core.Rewriter

open Batteries (AssocList)

namespace Graphiti.CombModule

@[simp] abbrev Val := Int
@[simp] abbrev Reg := Nat
@[simp] abbrev Ptrofs := Int
@[simp] abbrev Node := Nat
@[simp] abbrev Ident := Nat

structure Context where
  memory : AssocList Reg Val
  deriving Inhabited

def update_loc (loc: Reg) (val: Val) (c: Context) : Context :=
  ⟨c.memory.cons loc val⟩

abbrev CFG := ExprHigh String (String × Nat)

abbrev Port := InternalPort String

inductive Comparison: Type where
| Ceq : Comparison
| Cne : Comparison
| Clt : Comparison
| Cle : Comparison
| Cgt : Comparison
| Cge : Comparison
deriving Repr, DecidableEq, Lean.ToJson, Lean.FromJson, Inhabited

instance : ToString Comparison where
  toString
  | .Ceq => "Ceq"
  | .Cne => "Cne"
  | .Clt => "Clt"
  | .Cle => "Cle"
  | .Cgt => "Cgt"
  | .Cge => "Cge"

inductive Condition: Type where
| Ccomp (comp: Comparison)
| Ccompu (comp: Comparison)
| Ccompimm (comp: Comparison) (imm: Int)
| Ccompuimm (comp: Comparison) (imm: Int)
| Ccompl (comp: Comparison)
| Ccomplu (comp: Comparison)
| Ccomplimm (comp: Comparison) (imm: Int)
| Ccompluimm (comp: Comparison) (imm: Int)
| Ccompf (comp: Comparison)
| Cnotcompf (comp: Comparison)
| Ccompfs (comp: Comparison)
| Cnotcompfs (comp: Comparison)
deriving Repr, DecidableEq, Lean.ToJson, Lean.FromJson, Inhabited

instance : ToString Condition where
  toString
  | .Ccomp comp => s!"Ccomp {comp}"
  | .Ccompu comp => s!"Ccompu {comp}"
  | .Ccompimm comp _ => s!"Ccomp {comp}"
  | .Ccompuimm comp _ => s!"Ccompu {comp}"
  | _ => panic! "<not implemented>"

inductive Operation: Type where
| Omove
| Ointconst (imm: Int)
| Olongconst (imm: Int)
| Ofloatconst (imm: Float)
| Osingleconst (imm: Float)
| Oaddrsymbol (id: Ident) (ofs: Ptrofs)
| Oaddrstack (ofs: Ptrofs)
| Ocast8signed
| Ocast16signed
| Oadd
| Oaddimm (imm: Int)
| Oneg
| Osub
| Omul
| Omulhs
| Omulhu
| Odiv
| Odivu
| Omod
| Omodu
| Oand
| Oandimm (imm: Int)
| Oor
| Oorimm (imm: Int)
| Oxor
| Oxorimm (imm: Int)
| Oshl
| Oshlimm (imm: Int)
| Oshr
| Oshrimm (imm: Int)
| Oshru
| Oshruimm (imm: Int)
| Oshrximm (imm: Int)
| Omakelong
| Olowlong
| Ohighlong
| Ocast32signed
| Ocast32unsigned
| Oaddl
| Oaddlimm (imm: Int)
| Onegl
| Osubl
| Omull
| Omullhs
| Omullhu
| Odivl
| Odivlu
| Omodl
| Omodlu
| Oandl
| Oandlimm (imm: Int)
| Oorl
| Oorlimm (imm: Int)
| Oxorl
| Oxorlimm (imm: Int)
| Oshll
| Oshllimm (imm: Int)
| Oshrl
| Oshrlimm (imm: Int)
| Oshrlu
| Oshrluimm (imm: Int)
| Oshrxlimm (imm: Int)
| Onegf
| Oabsf
| Oaddf
| Osubf
| Omulf
| Odivf
| Onegfs
| Oabsfs
| Oaddfs
| Osubfs
| Omulfs
| Odivfs
| Osingleoffloat
| Ofloatofsingle
| Ointoffloat
| Ointuoffloat
| Ofloatofint
| Ofloatofintu
| Ointofsingle
| Ointuofsingle
| Osingleofint
| Osingleofintu
| Olongoffloat
| Olonguoffloat
| Ofloatoflong
| Ofloatoflongu
| Olongofsingle
| Olonguofsingle
| Osingleoflong
| Osingleoflongu
| Ocmp (cond: Condition)
| Osel (cond: Condition)
deriving Repr, Lean.ToJson, Lean.FromJson, Inhabited

instance : ToString Operation where
  toString
  | .Omove => "Omove"
  | .Omod => "Omod"
  | _ => panic! "<not implemented>"

inductive MemoryChunk : Type where
| Mbool
| Mint8signed
| Mint8unsigned
| Mint16signed
| Mint16unsigned
| Mint32
| Mint64
| Mfloat32
| Mfloat64
| Many32
| Many64
deriving Repr, DecidableEq, Lean.ToJson, Lean.FromJson, Inhabited

inductive Addressing: Type where
| Aindexed (ofs: Ptrofs)
| Aglobal (id: Ident) (ofs: Ptrofs)
| Ainstack (ofs: Ptrofs)
deriving Repr, DecidableEq, Lean.ToJson, Lean.FromJson, Inhabited

deriving instance Lean.ToJson for Sum
deriving instance Lean.FromJson for Sum

inductive Instruction: Type where
| Inop (next : Node)
| Iop (operation : Operation) (regs : List Reg) (dest : Reg) (next : Node)
| Iload (chunk: MemoryChunk) (addr: Addressing) (regs: List Reg) (dest: Reg) (next: Node)
| Istore (chunk: MemoryChunk) (addr: Addressing) (regs: List Reg) (source: Reg) (next: Node)
| Icall (dest: Reg) (function: Sum Reg String) (args: List Reg) (next: Node)
| Icond (cond: Condition) (regs: List Reg) (true_next: Node) (false_next: Node)
| Ijumptable (reg: Reg) (table: List Node)
| Ireturn (reg: Option Reg)
deriving Repr, Lean.ToJson, Lean.FromJson, Inhabited

def Code: Type := Std.TreeMap String Instruction
deriving Repr, Lean.ToJson, Lean.FromJson, Inhabited

structure Function: Type where
  params: List Reg
  stacksize: Nat
  code: Code
  entrypoint: Node
deriving Repr, Lean.ToJson, Lean.FromJson, Inhabited

def Program: Type := Std.TreeMap String Function
deriving Repr, Lean.ToJson, Lean.FromJson, Inhabited

def random := "
{
\"f\": {
  \"params\": [2, 1],
  \"entrypoint\": 10,
  \"stacksize\": 0,
  \"code\": {
    \"10\": {\"Iop\": {\"dest\": 5, \"operation\": \"Omove\", \"regs\": [2], \"next\": 9}},
    \"9\": {\"Iop\": {\"dest\": 4, \"operation\": \"Omove\", \"regs\": [1], \"next\": 8}},
    \"8\": {\"Inop\": {\"next\": 7}},
    \"7\": {\"Icond\": {\"cond\": {\"Ccompimm\": {\"comp\": \"Cne\", \"imm\": 0}}, \"regs\": [4], \"true_next\": 6, \"false_next\": 2}},
    \"6\": {\"Iop\": {\"dest\": 3, \"operation\": \"Omove\", \"regs\": [4], \"next\": 5}},
    \"5\": {\"Iop\": {\"dest\": 4, \"operation\": \"Omod\", \"regs\": [5, 4], \"next\": 4}},
    \"4\": {\"Iop\": {\"dest\": 5, \"operation\": \"Omove\", \"regs\": [3], \"next\": 3}},
    \"3\": {\"Inop\": {\"next\": 7}},
    \"2\": {\"Iop\": {\"dest\": 6, \"operation\": \"Omove\", \"regs\": [5], \"next\": 1}},
    \"1\": {\"Ireturn\": {\"reg\": 6}}
  }
},
\"main\": {
  \"params\": [],
  \"entrypoint\": 6,
  \"stacksize\": 0,
  \"code\": {
    \"6\": {\"Iop\": {\"dest\": 3, \"operation\": {\"Ointconst\": {\"imm\": 10}}, \"regs\": [], \"next\": 5}},
    \"5\": {\"Iop\": {\"dest\": 4, \"operation\": {\"Ointconst\": {\"imm\": 12}}, \"regs\": [], \"next\": 4}},
    \"4\": {\"Icall\": {\"dest\": 1, \"function\": {\"inr\": {\"val\": \"f\"}}, \"args\": [3, 4], \"next\": 3}},
    \"3\": {\"Iop\": {\"dest\": 2, \"operation\": \"Omove\", \"regs\": [1], \"next\": 1}},
    \"2\": {\"Iop\": {\"dest\": 2, \"operation\": {\"Ointconst\": {\"imm\": 0}}, \"regs\": [], \"next\": 1}},
    \"1\": {\"Ireturn\": {\"reg\": 2}}
  }
}
}
"

def prog : Function := (Lean.Json.parse random >>= Lean.fromJson? (α := Program)).toOption.get! |> (·.get! "f")

#eval IO.println <| repr <| prog

def isInputConnected? (graph : CFG) (inp : Port) : Option Port :=
  graph.connections.filter (·.input == inp) |>.head? |>.map (·.output)

def PortMap.generate (name label : String) (n : Nat) : PortMap String (InternalPort String) :=
  List.range n
  |>.map (fun i => (⟨.top, label ++ toString (i+1)⟩, ⟨.internal name, label ++ toString (i+1)⟩))
  |>.toAssocList

def PortMapping.generate (name : String) (inp out : Nat) : PortMapping String :=
  ⟨PortMap.generate name "in" inp, PortMap.generate name "out" out⟩

def connectMaybeWithMerge (graph : CFG) (out inp : Port) : CFG :=
  match isInputConnected? graph inp with
  | some cur_out =>
    let m := s!"merge_{graph.modules.length}"
    ⟨ graph.modules.cons m (PortMapping.generate m 2 1, ("merge", 0)),
      graph.connections.filter (· != ⟨cur_out, inp⟩)
      |>.cons ⟨⟨.internal m, "out1"⟩, inp⟩
      |>.cons ⟨out, ⟨.internal m, "in1"⟩⟩
      |>.cons ⟨cur_out, ⟨.internal m, "in2"⟩⟩
     ⟩
  | none =>
    {graph with connections := ⟨out, inp⟩ :: graph.connections}

def addFork (g : CFG) (label : String) (ports : List Port) : Port × CFG :=
  let new_mods := g.modules
    |>.cons s!"{label}" (PortMapping.generate s!"{label}" 1 ports.length, (s!"fork{ports.length}", 0))
  (⟨.internal s!"{label}", "in1"⟩, ((List.range ports.length).zip ports).foldl (fun st (n, r) =>
    let n := n + 1
    connectMaybeWithMerge st ⟨.internal s!"{label}", s!"out{n}"⟩ r
  ) {g with modules := new_mods})

def operationToGraph {α} [ToString α] (g : CFG) (label : String) (operation : α) (regs : List Reg) : Port × Port × CFG :=
  let read_write_graph :=
    ((List.range regs.length).zip regs).foldl (fun st (n, r) =>
      let n := n+1
      let mods := st.modules.cons s!"{label}_reg{n}" (PortMapping.generate s!"{label}_reg{n}" 0 1, (s!"Reg", r))
                  |>.cons s!"{label}_read{n}" (PortMapping.generate s!"{label}_read{n}" 2 1, (s!"Read", 0))
      {st with modules := mods}
      |> (connectMaybeWithMerge ·
           ⟨.internal s!"{label}_read{n}", "out1"⟩ ⟨.internal s!"{label}_op", s!"in{n}"⟩)
      |> (connectMaybeWithMerge ·
           ⟨.internal s!"{label}_fork", s!"out{n}"⟩ ⟨.internal s!"{label}_read{n}", s!"in1"⟩)
      |> (connectMaybeWithMerge ·
           ⟨.internal s!"{label}_reg{n}", s!"out1"⟩ ⟨.internal s!"{label}_read{n}", s!"in2"⟩)
    ) g
  let new_mods := read_write_graph.modules.cons s!"{label}_fork" (PortMapping.generate s!"{label}_fork" 1 regs.length, (s!"fork{regs.length}", 0))
                  |>.cons s!"{label}_op" (PortMapping.generate s!"{label}_op" regs.length 1, (toString operation, 0))
  (⟨.internal s!"{label}_fork", "in1"⟩, ⟨.internal s!"{label}_op", "out1"⟩, {read_write_graph with modules := new_mods})

def operationWithImmToGraph {α β} [ToString α] [ToString β] (g : CFG) (label : String) (operation : α) (imm : β) (regs : List Reg) : Port × Port × CFG :=
  let read_write_graph :=
    ((List.range regs.length).zip regs).foldl (fun st (n, r) =>
      let n := n+1
      let mods := st.modules.cons s!"{label}_reg{n}" (PortMapping.generate s!"{label}_reg{n}" 0 1, (s!"Reg", r))
                  |>.cons s!"{label}_read{n}" (PortMapping.generate s!"{label}_read{n}" 2 1, (s!"Read", 0))
      {st with modules := mods}
      |> (connectMaybeWithMerge ·
           ⟨.internal s!"{label}_read{n}", "out1"⟩ ⟨.internal s!"{label}_op", s!"in{n}"⟩)
      |> (connectMaybeWithMerge ·
           ⟨.internal s!"{label}_fork", s!"out{n}"⟩ ⟨.internal s!"{label}_read{n}", s!"in1"⟩)
      |> (connectMaybeWithMerge ·
           ⟨.internal s!"{label}_reg{n}", s!"out1"⟩ ⟨.internal s!"{label}_read{n}", s!"in2"⟩)
    ) g
  let new_mods := read_write_graph.modules.cons s!"{label}_fork" (PortMapping.generate s!"{label}_fork" 1 regs.length, (s!"fork{regs.length}", 0))
                  |>.cons s!"{label}_op" (PortMapping.generate s!"{label}_op" regs.length 1, (toString operation, 0))
  (⟨.internal s!"{label}_fork", "in1"⟩, ⟨.internal s!"{label}_op", "out1"⟩, {read_write_graph with modules := new_mods})

def writeGraph (g : CFG) (label : String) (dest : Node) : Port × Port × Port × CFG :=
  let new_mods := g.modules
    |>.cons s!"{label}_write" (PortMapping.generate s!"{label}_write" 3 1, (s!"Write", 0))
    |>.cons s!"{label}_dest" (PortMapping.generate s!"{label}_dest" 0 1, (s!"Reg", dest))
  (⟨.internal s!"{label}_write", "in1"⟩, ⟨.internal s!"{label}_write", "in3"⟩, ⟨.internal s!"{label}_write", "out1"⟩, {g with modules := new_mods}
  |> (connectMaybeWithMerge ·
       ⟨.internal s!"{label}_dest", s!"out1"⟩ ⟨.internal s!"{label}_write", "in2"⟩))

def instrToGraph (g : CFG) (label : String) : Instruction → CFG
| .Inop next =>
  connectMaybeWithMerge {g with modules := g.modules.cons s!"{label}" (PortMapping.generate s!"{label}" 1 1, ("Inop", 0))}
  ⟨.internal s!"{label}", "out1"⟩ ⟨.internal s!"{next}", "in1"⟩
| .Iop operation regs dest next =>
  let (st1, val, cfg) := operationToGraph g s!"{label}_sub" operation regs
  let (st2, inp, out, cfg) := writeGraph cfg label dest
  let (_, cfg) := addFork cfg label [st2, st1]
  cfg
  |> (connectMaybeWithMerge · val inp)
  |> (connectMaybeWithMerge · out ⟨.internal s!"{next}", "in1"⟩)
| .Icond cond regs true_next false_next =>
  let (st1, val, cfg) := operationToGraph g s!"{label}_cond" cond regs
  let (_, cfg) := addFork cfg label [st1, ⟨.internal s!"{label}_branch", "in1"⟩]
  {cfg with modules := g.modules.cons s!"{label}_branch" (PortMapping.generate s!"{label}_branch" 2 2, ("branch", 0))}
  |> (connectMaybeWithMerge · ⟨.internal s!"{label}_branch", "out1"⟩ ⟨.internal s!"{true_next}", "in1"⟩)
  |> (connectMaybeWithMerge · ⟨.internal s!"{label}_branch", "out2"⟩ ⟨.internal s!"{false_next}", "in1"⟩)
  |> (connectMaybeWithMerge · val ⟨.internal s!"{label}_branch", "in2"⟩)
| .Ireturn (.some reg) =>
  {g with modules := g.modules.cons s!"{label}" (PortMapping.generate s!"{label}" 1 0, ("Ireturn", reg))}
| .Ireturn .none =>
  {g with modules := g.modules.cons s!"{label}" (PortMapping.generate s!"{label}" 1 0, ("Ireturn", 0))}
| _ => panic! "<not implemented>"

def codeToGraph (code : Code) : ExprHigh String (String × Nat) :=
  code.foldl instrToGraph ⟨∅, ∅⟩

/- #eval IO.FS.writeFile "random.dot" <| toString <| codeToGraph prog.code
 - #eval IO.Process.run {cmd := "dot", args := #["-Tsvg", "random.dot", "-o", "random.svg"] } -/

namespace Rewrites

namespace RWNotEQ

variable (T : Vector Nat 2)

def lhs : ExprHigh String (String × Nat) := [graph|
    i_ctx [type="io"];
    i_v [type="io"];
    o_ctx [type="io"];
    o_v [type="io"];

    write [type="Write", arg=$(0)];
    fork [type="fork2", arg=$(0)];
    read [type="Read", arg=$(0)];
    w_reg [type="Reg", arg=$(T[0])];
    r_reg [type="Reg", arg=$(T[1])];

    i_v -> write [to="in3"];
    i_ctx -> write [to="in1"];
    fork -> o_ctx [from="out2"];
    read -> o_v [from="out1"];

    w_reg -> write [from="out1", to="in2"];
    write -> fork [from="out1", to="in1"];
    fork -> read [from="out1", to="in1"];
    r_reg -> read [from="out1", to="in2"];
  ]

def lhs_extract := (lhs T).extract ["write", "fork", "read", "w_reg", "r_reg"] |>.get rfl
theorem double_check_empty_snd : (lhs_extract T).snd = ExprHigh.mk ∅ ∅ := by rfl
def lhsLower := (lhs_extract T).fst.lower.get rfl

def rhs : ExprHigh String (String × Nat) := [graph|
    i_ctx [type="io"];
    i_v [type="io"];
    o_ctx [type="io"];
    o_v [type="io"];

    write [type="Write", arg=$(0)];
    fork [type="fork2", arg=$(0)];
    read [type="Read", arg=$(0)];
    w_reg [type="Reg", arg=$(T[0])];
    r_reg [type="Reg", arg=$(T[1])];

    i_ctx -> fork [to="in1"];
    i_v -> write [to="in3"];
    write -> o_ctx [from="out1"];
    read -> o_v [from="out1"];

    w_reg -> write [from="out1", to="in2"];
    r_reg -> read [from="out1", to="in2"];
    fork -> write [from="out2", to="in1"];
    fork -> read [from="out1", to="in1"];
  ]

def rhs_extract := (rhs T).extract ["write", "fork", "w_reg"] |>.get rfl
def rhsLower := (rhs_extract T).fst.lower.get rfl
def findRhs mod := (rhs_extract #v[0, 0]).fst.modules.find? mod |>.map Prod.fst

def rewrite : Rewrite String (String × Nat) where
  abstractions := []
  params := _
  pattern := defaultMatcher (lhs #v[0, 0])
  rewrite := λ l n => ⟨lhsLower #v[l[3].2, l[4].2], rhsLower #v[l[3].2, l[4].2]⟩
  name := "RWEQ"
  transformedNodes := [findRhs "write" |>.get!, findRhs "fork" |>.get!, .none, findRhs "w_reg" |>.get!, .none]

end RWNotEQ

namespace RWEQ

variable (T : Vector Nat 1)

def lhs : ExprHigh String (String × Nat) := [graph|
    i_ctx [type="io"];
    i_v [type="io"];
    o_ctx [type="io"];
    o_v [type="io"];

    write [type="Write", arg=$(0)];
    fork [type="fork2", arg=$(0)];
    read [type="Read", arg=$(0)];
    w_reg [type="Reg", arg=$(T[0])];
    r_reg [type="Reg", arg=$(T[0])];

    i_v -> write [to="in3"];
    i_ctx -> write [to="in1"];
    fork -> o_ctx [from="out2"];
    read -> o_v [from="out1"];

    w_reg -> write [from="out1", to="in2"];
    write -> fork [from="out1", to="in1"];
    fork -> read [from="out1", to="in1"];
    r_reg -> read [from="out1", to="in2"];
  ]

def lhs_extract := (lhs T).extract ["write", "fork", "read", "w_reg", "r_reg"] |>.get rfl
theorem double_check_empty_snd : (lhs_extract T).snd = ExprHigh.mk ∅ ∅ := by rfl
def lhsLower := (lhs_extract T).fst.lower.get rfl

def rhs : ExprHigh String (String × Nat) := [graph|
    i_ctx [type="io"];
    i_v [type="io"];
    o_ctx [type="io"];
    o_v [type="io"];

    write [type="Write", arg=$(0)];
    fork [type="fork2", arg=$(0)];
    w_reg [type="Reg", arg=$(T[0])];

    i_v -> fork [to="in1"];
    i_ctx -> write [to="in1"];
    write -> o_ctx [from="out1"];
    fork -> o_v [from="out1"];

    w_reg -> write [from="out1", to="in2"];
    fork -> write [from="out2", to="in3"];
  ]

def rhs_extract := (rhs T).extract ["write", "fork", "w_reg"] |>.get rfl
def rhsLower := (rhs_extract T).fst.lower.get rfl
def findRhs mod := (rhs_extract #v[0]).fst.modules.find? mod |>.map Prod.fst

def rewrite : Rewrite String (String × Nat) where
  abstractions := []
  params := _
  pattern := defaultMatcher (lhs #v[0])
  rewrite := λ l n => ⟨lhsLower #v[l[3].2], rhsLower #v[l[3].2]⟩
  name := "RWEQ"
  transformedNodes := [findRhs "write" |>.get!, findRhs "fork" |>.get!, .none, findRhs "w_reg" |>.get!, .none]

end RWEQ

namespace ForkSummary

def lhs : ExprHigh String (String × Nat) := [graph|
    i [type="io"];
    o1 [type="io"];
    o2 [type="io"];

    fork1 [type="fork1", arg=$(0)];
    fork2 [type="fork2", arg=$(0)];

    i -> fork2 [to="in1"];
    fork1 -> o2 [from="out1"];
    fork2 -> o1 [from="out2"];

    fork2 -> fork1 [from="out1", to="in1"];
  ]

def lhs_extract := lhs.extract ["fork1", "fork2"] |>.get rfl
theorem double_check_empty_snd : lhs_extract.snd = ExprHigh.mk ∅ ∅ := by rfl
def lhsLower := lhs_extract.fst.lower.get rfl

def rhs : ExprHigh String (String × Nat) := [graph|
    i [type="io"];
    o1 [type="io"];
    o2 [type="io"];

    fork2 [type="fork2", arg=$(0)];

    i -> fork2 [to="in1"];
    fork2 -> o2 [from="out1"];
    fork2 -> o1 [from="out2"];
  ]

def rhs_extract := rhs.extract ["fork2"] |>.get rfl
def rhsLower := rhs_extract.fst.lower.get rfl
def findRhs mod := rhs_extract.fst.modules.find? mod |>.map Prod.fst

def rewrite : Rewrite String (String × Nat) where
  abstractions := []
  params := _
  pattern := defaultMatcher lhs
  rewrite := λ l n => ⟨lhsLower, rhsLower⟩
  name := "fork-summary"
  transformedNodes := [.none, findRhs "fork2" |>.get!]

end ForkSummary

namespace ForkAssoc

def lhs : ExprHigh String (String × Nat) := [graph|
    i [type="io"];
    o1 [type="io"];
    o2 [type="io"];
    o3 [type="io"];

    fork1 [type="fork2", arg=$(0)];
    fork2 [type="fork2", arg=$(0)];

    i -> fork2 [to="in1"];
    fork1 -> o1 [from="out1"];
    fork2 -> o2 [from="out1"];
    fork2 -> o3 [from="out2"];

    fork1 -> fork2 [from="out2", to="in1"];
  ]

def lhs_extract := lhs.extract ["fork1", "fork2"] |>.get rfl
theorem double_check_empty_snd : lhs_extract.snd = ExprHigh.mk ∅ ∅ := by rfl
def lhsLower := lhs_extract.fst.lower.get rfl

def rhs : ExprHigh String (String × Nat) := [graph|
    i [type="io"];
    o1 [type="io"];
    o2 [type="io"];
    o3 [type="io"];

    fork1 [type="fork2", arg=$(0)];
    fork2 [type="fork2", arg=$(0)];

    i -> fork2 [to="in1"];
    fork2 -> o1 [from="out2"];
    fork1 -> o2 [from="out1"];
    fork2 -> o3 [from="out1"];

    fork1 -> fork2 [from="out2", to="in1"];
  ]

def rhs_extract := rhs.extract ["fork1", "fork2"] |>.get rfl
def rhsLower := rhs_extract.fst.lower.get rfl
def findRhs mod := rhs_extract.fst.modules.find? mod |>.map Prod.fst

def rewrite : Rewrite String (String × Nat) where
  abstractions := []
  params := _
  pattern := defaultMatcher lhs
  rewrite := λ l n => ⟨lhsLower, rhsLower⟩
  name := "fork-assoc"
  transformedNodes := [findRhs "fork1" |>.get!, findRhs "fork2" |>.get!]

end ForkAssoc

end Rewrites

namespace Denotation

def moduleGen (f : Context → Option Context) : StringModule (Option Context) :=
  NatModule.stringify {
    inputs := [(0, ⟨ Context, fun
      | .none, s, .some c' => f s = .some c'
      | _, _, _ => False ⟩)].toAssocList,
    outputs := [(0, ⟨ Context, fun
      | .some c, s, .none => s = c
      | _, _, _ => False ⟩)].toAssocList,
    init_state := λ s => s = default
  }

end Denotation

namespace Example

/- gcd(x2, x1) {
 -     7:  nop
 -     6:  if (x1 !=s 0) goto 5 else goto 2
 -     5:  x3 = x2 %s x1
 -     4:  x2 = x1
 -     3:  x1 = x3
 -         goto 6
 -     2:  x4 = x2
 -     1:  return x4
 - } -/

def gcd : ExprHigh String (String × Nat) := [graph|
    context [type = "inputContext", arg = 0];

    merge [type = "merge", arg = 0];
    l6rd [type = "rd", arg = 0];
    l6const [type = "constant", arg = 0];
    l6neq [type = "mod", arg = 0];
    l6cont [type = "fork2", arg = 0];
    l6 [type = "if", arg = 0];  -- if (x1 !=s 0) goto 5 else goto 2
    l5cont [type = "fork3", arg = 0];
    l5rdx2 [type = "rd", arg = 2];
    l5rdx1 [type = "rd", arg = 1];
    l5mod [type = "mod", arg = 0];
    l5 [type = "upd", arg = 3]; -- x3 = x2 %s x1
    l4cont [type = "fork2", arg = 0];
    l4rd [type = "rd", arg = 1];
    l4 [type = "upd", arg = 2]; -- x2 = x1
    l3cont [type = "fork2", arg = 0];
    l3rd [type = "rd", arg = 3];
    l3 [type = "upd", arg = 1]; -- x1 = x3; goto 6

    l1cont [type = "fork2", arg = 0];
    l1rdx2 [type = "rd", arg=2];
    l1 [type = "outputVal", arg=0]; -- return x2

    -- CFG
    context -> merge [from="O", to="I1"];
    merge -> l6cont [from="O", to="I"];
    l6 -> l5cont [from="true", to="I"];
    l6 -> l1cont [from="false", to="I"];

    l5 -> l4cont [from="O", to="I"];
    l4 -> l3cont [from="O", to="I"];
    l3 -> merge [from="O", to="I2"];

    -- DATA
    l6cont -> l6rd [from="O2", to="I"];
    l6cont -> l6 [from="O1", to="I"];
    l6rd -> l6neq [from="O", to="I1"];
    l6const -> l6neq [from="O", to="I2"];
    l6neq -> l6 [from="O", to="cond"];

    l5cont -> l5rdx2 [from="O3", to="I"];
    l5cont -> l5rdx1 [from="O2", to="I"];
    l5cont -> l5 [from="O1", to="I"];
    l5rdx2 -> l5mod [from="O", to="I1"];
    l5rdx1 -> l5mod [from="O", to="I2"];
    l5mod -> l5 [from="O", to="val"];

    l4cont -> l4rd [from="O2", to="I"];
    l4cont -> l4 [from="O1", to="I"];
    l4rd -> l4 [from="O", to="val"];

    l3cont -> l3rd [from="O2", to="I"];
    l3cont -> l3 [from="O1", to="I"];
    l3rd -> l3 [from="O", to="val"];

    l1cont -> l1 [from="O1", to="I"];
    l1cont -> l1rdx2 [from="O2", to="I"];
    l1rdx2 -> l1 [from="O", to="val"];
  ]

#eval IO.println <| toString gcd

end Example

end Graphiti.CombModule
