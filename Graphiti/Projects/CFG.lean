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

instance : DecidableEq Float := fun a b =>
  if a <= b && b <= a then
    isTrue sorry
  else
    isFalse sorry

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
deriving Repr, Lean.ToJson, Lean.FromJson, Inhabited, DecidableEq

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
deriving Repr, DecidableEq, Lean.ToJson, Lean.FromJson, Inhabited, DecidableEq

instance : ToString MemoryChunk where
  toString
  | .Mbool => "bool"
  | .Mint8signed => "int8signed"
  | .Mint8unsigned => "int8unsigned"
  | .Mint16signed => "int16signed"
  | .Mint16unsigned => "int16unsigned"
  | .Mint32 => "int32"
  | .Mint64 => "int64"
  | .Mfloat32 => "float32"
  | .Mfloat64 => "float64"
  | .Many32 => "any32"
  | .Many64 => "any64"

inductive Addressing: Type where
| Aindexed (ofs: Ptrofs)
| Aglobal (id: Ident) (ofs: Ptrofs)
| Ainstack (ofs: Ptrofs)
deriving Repr, DecidableEq, Lean.ToJson, Lean.FromJson, Inhabited, DecidableEq

instance : ToString Addressing where
  toString
  | .Aindexed ofs => s!"Aindexed {ofs}"
  | .Aglobal id ofs => s!"Aindexed {id} {ofs}"
  | .Ainstack ofs => s!"Ainstack {ofs}"

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
deriving Repr, Lean.ToJson, Lean.FromJson, Inhabited, DecidableEq

instance : ToString Instruction where
  toString
  | .Inop _ => "Inop"
  | .Iop op r d _ => s!"Iop ({op}, {r}, {d})"
  | .Iload chk addr r d _ => s!"Iop ({chk}, {addr}, {r}, {d})"
  | .Istore chk addr r s _ => s!"Iop ({chk}, {addr}, {r}, {s})"
  | .Icall d f a _ => "Icall"
  | .Icond c r _ _ => s!"Icond ({c}, {r})"
  | .Ijumptable r _ => s!"Ijumptable ({r})"
  | .Ireturn r => s!"Ireturn {r}"

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

inductive Component where
| merge
| branch
| fork
| pure
| split
| queue
| exit
| op (o : Operation)
| cond (o : Condition)
deriving Repr, Inhabited, Lean.ToJson, Lean.FromJson, DecidableEq

instance : ToString Component where
  toString
  | .merge => "merge"
  | .branch => "branch"
  | .fork => "fork"
  | .pure => "pure"
  | .split => "split"
  | .op o => s!"op {o}"
  | .cond o => s!"cond {o}"
  | .queue => "queue"
  | .exit => "exit"

inductive RW where
| reads (l : List Reg)
| writes (l : List Reg)
deriving Repr, Inhabited, Lean.ToJson, Lean.FromJson, DecidableEq

instance : ToString RW where
  toString
  | .reads l => s!"reads {l}"
  | .writes l => s!"writes {l}"

inductive DFGandCFG where
| cfg (i : Instruction)
| dfg (i : Component)
| rw (i : RW)
deriving Repr, Inhabited, Lean.ToJson, Lean.FromJson, DecidableEq

instance : ToString DFGandCFG where
  toString
  | .cfg i => toString i
  | .dfg i => toString i
  | .rw i => toString i

def DFGandCFG.compare (a b : DFGandCFG) : Bool :=
  match a, b with
  | .cfg a, .cfg b
  | .dfg a, .dfg b => a == b
  | .rw (.reads _), .rw (.reads _) => true
  | .rw (.writes _), .rw (.writes _) => true
  | _, _ => false

abbrev CCCFG := ExprHigh String DFGandCFG

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

def isInputConnected? {β} (graph : ExprHigh String β) (inp : Port) : Option Port :=
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
      let mods := st.modules -- .cons s!"{label}_reg{n}" (PortMapping.generate s!"{label}_reg{n}" 0 1, (s!"Reg", r))
                  |>.cons s!"{label}_read{n}" (PortMapping.generate s!"{label}_read{n}" 1 1, (s!"Read", r))
      {st with modules := mods}
      |> (connectMaybeWithMerge ·
           ⟨.internal s!"{label}_read{n}", "out1"⟩ ⟨.internal s!"{label}_op", s!"in{n}"⟩)
      |> (connectMaybeWithMerge ·
           ⟨.internal s!"{label}_fork", s!"out{n}"⟩ ⟨.internal s!"{label}_read{n}", s!"in1"⟩)
      /- |> (connectMaybeWithMerge ·
       -      ⟨.internal s!"{label}_reg{n}", s!"out1"⟩ ⟨.internal s!"{label}_read{n}", s!"in2"⟩) -/
    ) g
  let new_mods := read_write_graph.modules.cons s!"{label}_fork" (PortMapping.generate s!"{label}_fork" 1 regs.length, (s!"fork{regs.length}", 0))
                  |>.cons s!"{label}_op" (PortMapping.generate s!"{label}_op" regs.length 1, (toString operation, 0))
  (⟨.internal s!"{label}_fork", "in1"⟩, ⟨.internal s!"{label}_op", "out1"⟩, {read_write_graph with modules := new_mods})

def operationWithImmToGraph {α β} [ToString α] [ToString β] (g : CFG) (label : String) (operation : α) (imm : β) (regs : List Reg) : Port × Port × CFG :=
  let read_write_graph :=
    ((List.range regs.length).zip regs).foldl (fun st (n, r) =>
      let n := n+1
      let mods := st.modules --.cons s!"{label}_reg{n}" (PortMapping.generate s!"{label}_reg{n}" 0 1, (s!"Reg", r))
                  |>.cons s!"{label}_read{n}" (PortMapping.generate s!"{label}_read{n}" 1 1, (s!"Read", r))
      {st with modules := mods}
      |> (connectMaybeWithMerge ·
           ⟨.internal s!"{label}_read{n}", "out1"⟩ ⟨.internal s!"{label}_op", s!"in{n}"⟩)
      |> (connectMaybeWithMerge ·
           ⟨.internal s!"{label}_fork", s!"out{n}"⟩ ⟨.internal s!"{label}_read{n}", s!"in1"⟩)
      /- |> (connectMaybeWithMerge ·
       -      ⟨.internal s!"{label}_reg{n}", s!"out1"⟩ ⟨.internal s!"{label}_read{n}", s!"in2"⟩) -/
    ) g
  let new_mods := read_write_graph.modules.cons s!"{label}_fork" (PortMapping.generate s!"{label}_fork" 1 regs.length, (s!"fork{regs.length}", 0))
                  |>.cons s!"{label}_op" (PortMapping.generate s!"{label}_op" regs.length 1, (toString operation, 0))
  (⟨.internal s!"{label}_fork", "in1"⟩, ⟨.internal s!"{label}_op", "out1"⟩, {read_write_graph with modules := new_mods})

def writeGraph (g : CFG) (label : String) (dest : Node) : Port × Port × Port × CFG :=
  let new_mods := g.modules
    |>.cons s!"{label}_write" (PortMapping.generate s!"{label}_write" 2 1, (s!"Write", dest))
    /- |>.cons s!"{label}_dest" (PortMapping.generate s!"{label}_dest" 0 1, (s!"Reg", dest)) -/
  (⟨.internal s!"{label}_write", "in1"⟩, ⟨.internal s!"{label}_write", "in2"⟩, ⟨.internal s!"{label}_write", "out1"⟩, {g with modules := new_mods}
  /- |> (connectMaybeWithMerge ·
   -      ⟨.internal s!"{label}_dest", s!"out1"⟩ ⟨.internal s!"{label}_write", "in2"⟩) -/)

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
  {cfg with modules := cfg.modules.cons s!"{label}_branch" (PortMapping.generate s!"{label}_branch" 2 2, ("branch", 0))}
  |> (connectMaybeWithMerge · ⟨.internal s!"{label}_branch", "out1"⟩ ⟨.internal s!"{true_next}", "in1"⟩)
  |> (connectMaybeWithMerge · ⟨.internal s!"{label}_branch", "out2"⟩ ⟨.internal s!"{false_next}", "in1"⟩)
  |> (connectMaybeWithMerge · val ⟨.internal s!"{label}_branch", "in2"⟩)
| .Ireturn (.some reg) =>
  {g with modules := g.modules.cons s!"{label}" (PortMapping.generate s!"{label}" 1 0, ("Ireturn", reg))}
| .Ireturn .none =>
  {g with modules := g.modules.cons s!"{label}" (PortMapping.generate s!"{label}" 1 0, ("Ireturn", 0))}
| _ => panic! "<not implemented>"

def connectCCCFG (graph : CCCFG) (out inp : Port) : CCCFG :=
  match isInputConnected? graph inp with
  | some cur_out =>
    let m := s!"merge_{graph.modules.length}"
    ⟨ graph.modules.cons m (PortMapping.generate m 2 1, .dfg .merge),
      graph.connections.filter (· != ⟨cur_out, inp⟩)
      |>.cons ⟨⟨.internal m, "out1"⟩, inp⟩
      |>.cons ⟨out, ⟨.internal m, "in1"⟩⟩
      |>.cons ⟨cur_out, ⟨.internal m, "in2"⟩⟩
     ⟩
  | none =>
    {graph with connections := ⟨out, inp⟩ :: graph.connections}

def instrToCCCFG (g : CCCFG) (label : String) : Instruction → CCCFG
| op@(.Inop next) =>
  connectCCCFG {g with modules := g.modules.cons s!"{label}" (PortMapping.generate s!"{label}" 1 1, .cfg op)}
  ⟨.internal s!"{label}", "out1"⟩ ⟨.internal s!"{next}", "in1"⟩
| op@(.Iop operation regs dest next) =>
  connectCCCFG {g with modules := g.modules.cons s!"{label}" (PortMapping.generate s!"{label}" 1 1, .cfg op)}
  ⟨.internal s!"{label}", "out1"⟩ ⟨.internal s!"{next}", "in1"⟩
| op@(.Icond cond regs true_next false_next) =>
  {g with modules := g.modules.cons s!"{label}" (PortMapping.generate s!"{label}" 1 2, .cfg op)}
  |> (connectCCCFG · ⟨.internal s!"{label}", "out1"⟩ ⟨.internal s!"{true_next}", "in1"⟩)
  |> (connectCCCFG · ⟨.internal s!"{label}", "out2"⟩ ⟨.internal s!"{false_next}", "in1"⟩)
| op@(.Ireturn (.some reg)) =>
  {g with modules := g.modules.cons s!"{label}" (PortMapping.generate s!"{label}" 1 0, .cfg op)}
| op@(.Ireturn .none) =>
  {g with modules := g.modules.cons s!"{label}" (PortMapping.generate s!"{label}" 1 0, .cfg op)}
| _ => panic! "<not implemented>"

def codeToGraph (code : Code) : ExprHigh String (String × Nat) :=
  code.foldl instrToGraph ⟨∅, ∅⟩

def codeToCCCFG (code : Code) : ExprHigh String DFGandCFG :=
  code.foldl instrToCCCFG ⟨∅, ∅⟩

def graph := codeToGraph prog.code

def cccfg := codeToCCCFG prog.code

def existsInPath (cmd : String) : IO Bool := do
  let result ← IO.Process.output {
    cmd := "which"
    args := #[cmd]
  }
  return result.exitCode == 0

def toSVG {α} [ToString α] [Repr α] (file : String) (graph : ExprHigh String α) := do
  IO.FS.writeFile (file ++ ".dot") <| toString <| graph
  if ← existsInPath "dot" then
    let _ ← IO.Process.run {cmd := "dot", args := #["-Tsvg", (file ++ ".dot"), "-o", file ++ ".svg"] }

#eval toSVG "random" graph
#eval toSVG "cccfg" cccfg

namespace Rewrites

namespace RWNotEQ

variable (T : Vector Nat 2)

def lhs : ExprHigh String (String × Nat) := [graph|
    i_ctx [type="io"];
    i_v [type="io"];
    o_ctx [type="io"];
    o_v [type="io"];

    write [type="Write", arg=$(T[0])];
    fork [type="fork2", arg=$(0)];
    read [type="Read", arg=$(T[1])];

    i_v -> write [to="in2"];
    i_ctx -> write [to="in1"];
    fork -> o_ctx [from="out2"];
    read -> o_v [from="out1"];

    write -> fork [from="out1", to="in1"];
    fork -> read [from="out1", to="in1"];
  ]

def lhs_extract := (lhs T).extract ["write", "fork", "read"] |>.get rfl
theorem double_check_empty_snd : (lhs_extract T).snd = ExprHigh.mk ∅ ∅ := by rfl
def lhsLower := (lhs_extract T).fst.lower.get rfl

def rhs : ExprHigh String (String × Nat) := [graph|
    i_ctx [type="io"];
    i_v [type="io"];
    o_ctx [type="io"];
    o_v [type="io"];

    write [type="Write", arg=$(T[0])];
    fork [type="fork2", arg=$(0)];
    read [type="Read", arg=$(T[1])];

    i_ctx -> fork [to="in1"];
    i_v -> write [to="in2"];
    write -> o_ctx [from="out1"];
    read -> o_v [from="out1"];

    fork -> write [from="out2", to="in1"];
    fork -> read [from="out1", to="in1"];
  ]

def rhs_extract := (rhs T).extract ["write", "fork", "read"] |>.get rfl
def rhsLower := (rhs_extract T).fst.lower.get rfl
def findRhs mod := (rhs_extract #v[0, 0]).fst.modules.find? mod |>.map Prod.fst

def rewrite : Rewrite String (String × Nat) where
  abstractions := []
  params := _
  pattern := defaultMatcher (cmp := fun a b => a.1 == b.1) (pred := fun v => v[0].type.2 != v[2].type.2) (lhs_extract #v[0, 0]).fst
  rewrite := λ l n => ⟨lhsLower #v[l[0].2, l[2].2], rhsLower #v[l[0].2, l[2].2]⟩
  name := "RWEQ"
  transformedNodes := [findRhs "write" |>.get!, findRhs "fork" |>.get!, findRhs "read" |>.get!]

end RWNotEQ

namespace RWEQ

variable (T : Vector Nat 1)

def lhs : ExprHigh String (String × Nat) := [graph|
    i_ctx [type="io"];
    i_v [type="io"];
    o_ctx [type="io"];
    o_v [type="io"];

    write [type="Write", arg=$(T[0])];
    fork [type="fork2", arg=$(0)];
    read [type="Read", arg=$(T[0])];

    i_v -> write [to="in2"];
    i_ctx -> write [to="in1"];
    fork -> o_ctx [from="out2"];
    read -> o_v [from="out1"];

    write -> fork [from="out1", to="in1"];
    fork -> read [from="out1", to="in1"];
  ]

def lhs_extract := (lhs T).extract ["write", "fork", "read"] |>.get rfl
theorem double_check_empty_snd : (lhs_extract T).snd = ExprHigh.mk ∅ ∅ := by rfl
def lhsLower := (lhs_extract T).fst.lower.get rfl

def rhs : ExprHigh String (String × Nat) := [graph|
    i_ctx [type="io"];
    i_v [type="io"];
    o_ctx [type="io"];
    o_v [type="io"];

    write [type="Write", arg=$(T[0])];
    fork [type="fork2", arg=$(0)];

    i_v -> fork [to="in1"];
    i_ctx -> write [to="in1"];
    write -> o_ctx [from="out1"];
    fork -> o_v [from="out1"];

    fork -> write [from="out2", to="in2"];
  ]

def rhs_extract := (rhs T).extract ["write", "fork"] |>.get rfl
def rhsLower := (rhs_extract T).fst.lower.get rfl
def findRhs mod := (rhs_extract #v[0]).fst.modules.find? mod |>.map Prod.fst

def rewrite : Rewrite String (String × Nat) where
  abstractions := []
  params := _
  pattern := defaultMatcher (cmp := fun a b => a.1 == b.1) (pred := fun v => v[0].type.2 == v[2].type.2)  (lhs_extract #v[0]).fst
  rewrite := λ l n => ⟨lhsLower #v[l[0].2], rhsLower #v[l[0].2]⟩
  name := "RWEQ"
  transformedNodes := [findRhs "write" |>.get!, findRhs "fork" |>.get!, .none]

end RWEQ

namespace ForkSummary1

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
  pattern := defaultMatcher (cmp := fun a b => a.1 == b.1) lhs_extract.fst
  rewrite := λ l n => ⟨lhsLower, rhsLower⟩
  name := "fork-summary"
  transformedNodes := [.none, findRhs "fork2" |>.get!]

end ForkSummary1

namespace ForkSummary2

def lhs : ExprHigh String (String × Nat) := [graph|
    i [type="io"];
    o1 [type="io"];
    o2 [type="io"];

    fork1 [type="fork1", arg=$(0)];
    fork2 [type="fork2", arg=$(0)];

    i -> fork2 [to="in1"];
    fork1 -> o2 [from="out1"];
    fork2 -> o1 [from="out1"];

    fork2 -> fork1 [from="out2", to="in1"];
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
  pattern := defaultMatcher (cmp := fun a b => a.1 == b.1) lhs_extract.fst
  rewrite := λ l n => ⟨lhsLower, rhsLower⟩
  name := "fork-summary"
  transformedNodes := [.none, findRhs "fork2" |>.get!]

end ForkSummary2

namespace ForkAssoc

def lhs : ExprHigh String (String × Nat) := [graph|
    i [type="io"];
    o1 [type="io"];
    o2 [type="io"];
    o3 [type="io"];

    fork1 [type="fork2", arg=$(0)];
    fork2 [type="fork2", arg=$(0)];

    i -> fork1 [to="in1"];
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

    i -> fork1 [to="in1"];
    fork1 -> o2 [from="out1"];
    fork2 -> o3 [from="out1"];
    fork2 -> o1 [from="out2"];

    fork1 -> fork2 [from="out2", to="in1"];
  ]

def rhs_extract := rhs.extract ["fork1", "fork2"] |>.get rfl
def rhsLower := rhs_extract.fst.lower.get rfl
def findRhs mod := rhs_extract.fst.modules.find? mod |>.map Prod.fst

def rewrite : Rewrite String (String × Nat) where
  abstractions := []
  params := _
  pattern := defaultMatcher (cmp := fun a b => a.1 == b.1) lhs_extract.fst
  rewrite := λ l n => ⟨lhsLower, rhsLower⟩
  name := "fork-assoc"
  transformedNodes := [findRhs "fork1" |>.get!, findRhs "fork2" |>.get!]

end ForkAssoc

namespace LoopRewrite

def lhs (l : List Reg) : ExprHigh String DFGandCFG := [graphv2|
    i [type=$("io")];
    o [type=$("io")];

    merge [type=$(.dfg .merge)];
    cond [type=$(.dfg .pure)];
    condSplit [type=$(.dfg .split)];
    branch [type=$(.dfg .branch)];
    readFork [type=$(.dfg .fork)];
    reads [type=$(.rw (.reads l))];
    cReads [type=$(.rw (.reads l))];
    pure [type=$(.dfg .pure)];
    writes [type=$(.rw (.writes l))];

    i -> merge [to="in1"];
    writes -> merge [from="out1", to="in2"];
    merge -> cReads [from="out1", to="in1"];
    cReads -> cond [from="out1", to="in1"];
    cond -> condSplit [from="out1", to="in1"];
    condSplit -> branch [from="out1", to="in1"];
    condSplit -> branch [from="out2", to="in2"];
    branch -> o [from="out2"];
    branch -> readFork [from="out1", to="in1"];
    readFork -> reads [from="out1", to="in1"];
    readFork -> writes [from="out2", to="in1"];
    reads -> pure [from="out1", to="in1"];
    pure -> writes [from="out1", to="in2"];
  ]

def lhs_extract l := (lhs l).extract ["merge", "cond", "condSplit", "branch", "readFork", "reads", "cReads", "pure", "writes"] |>.get rfl
theorem double_check_empty_snd : (lhs_extract []).snd = ExprHigh.mk ∅ ∅ := by rfl
def lhsLower l := (lhs_extract l).fst.lower.get rfl

def rhs (l : List Reg) : ExprHigh String DFGandCFG := [graphv2|
    i [type=$("io")];
    o [type=$("io")];

    merge [type=$(.dfg .merge)];
    cond [type=$(.dfg .pure)];
    condSplit [type=$(.dfg .split)];
    branch [type=$(.dfg .branch)];
    readFork [type=$(.dfg .fork)];
    reads [type=$(.rw (.reads l))];
    pure [type=$(.dfg .pure)];
    writes [type=$(.rw (.writes l))];

    i -> readFork [to="in1"];
    readFork -> reads [from="out1", to="in1"];
    readFork -> writes [from="out2", to="in1"];
    reads -> merge [from="out1", to="in1"];
    pure -> merge [from="out1", to="in2"];
    merge -> cond [from="out1", to="in1"];
    cond -> condSplit [from="out1", to="in1"];
    condSplit -> branch [from="out1", to="in1"];
    condSplit -> branch [from="out2", to="in2"];
    branch -> o [from="out2"];
    branch -> pure [from="out1", to="in1"];
    pure -> writes [from="out1", to="in2"];
  ]

def rhs_extract l := (rhs l).extract ["merge", "cond", "condSplit", "branch", "readFork", "reads", "pure", "writes"] |>.get rfl
def rhsLower l := (rhs_extract l).fst.lower.get rfl
def findRhs mod := (rhs_extract []).fst.modules.find? mod |>.map Prod.fst

def rewrite : Rewrite String DFGandCFG where
  abstractions := []
  params := _
  pattern := defaultMatcher (cmp := DFGandCFG.compare) (lhs_extract []).fst
  rewrite := λ l n =>
    match l[5] with
    | .rw (.reads l') =>
      ⟨lhsLower l', rhsLower l'⟩
    | _ => default
  name := "fork-assoc"
  /- transformedNodes := [findRhs "fork1" |>.get!, findRhs "fork2" |>.get!] -/

end LoopRewrite

def forkAssoc (s : String) : Rewrite String DFGandCFG :=
  create_rewrite (cmp := DFGandCFG.compare) (pred := fun a => a[0]!.name == s) "fork-assoc"
    (λ _ _ => ([graphv2|
        i [type=$("io")];
        o1 [type=$("io")];
        o2 [type=$("io")];
        o3 [type=$("io")];

        fork1 [type=$(.dfg .fork)];
        fork2 [type=$(.dfg .fork)];

        i -> fork1 [to="in1"];
        fork1 -> fork2 [from="out2",to="in1"];
        fork1 -> o1 [from="out1"];
        fork2 -> o2 [from="out1"];
        fork2 -> o3 [from="out2"];
      ] : ExprHigh String DFGandCFG).extract ["fork1", "fork2"] |>.get rfl |>.1)
      (λ _ _ => ([graphv2|
        i [type=$("io")];
        o1 [type=$("io")];
        o2 [type=$("io")];
        o3 [type=$("io")];

        fork1 [type=$(.dfg .fork)];
        fork2 [type=$(.dfg .fork)];

        i -> fork1 [to="in1"];
        fork1 -> fork2 [from="out1",to="in1"];
        fork2 -> o1 [from="out1"];
        fork2 -> o2 [from="out2"];
        fork1 -> o3 [from="out2"];
      ] : ExprHigh String DFGandCFG).extract ["fork1", "fork2"] |>.get rfl |>.1)

def extractList : DFGandCFG → List Nat
| .rw (.reads l) => l
| .rw (.writes l) => l
| _ => []

def combineReads : Rewrite String DFGandCFG :=
  create_rewrite (n := 3) (cmp := DFGandCFG.compare) "combine-reads"
    (λ l _ => [graphv2|
          i [io];
          o1 [io];
          o2 [io];

          fork [type=$(.dfg .fork)];
          read1 [type=$(.rw (.reads (extractList l[1])))];
          read2 [type=$(.rw (.reads (extractList l[2])))];

          i -> fork [to="in1"];
          fork -> read1 [from="out1",to="in1"];
          fork -> read2 [from="out2",to="in1"];
          read1 -> o1 [from="out1"];
          read2 -> o2 [from="out1"];
        ])
      (λ l _ => [graphv2|
          i [io];
          o1 [io];
          o2 [io];

          read1 [type=$(.rw (.reads (extractList l[1] ++ extractList l[2])))];
          split [type=$(.dfg .split)];

          i -> read1 [to="in1"];
          read1 -> split [from="out1",to="in1"];
          split -> o1 [from="out1"];
          split -> o2 [from="out2"];
        ])

inductive RWTree α β where
| base (r : Rewrite α β)
| seq (r1 r2 : RWTree α β)
| par (r1 r2 : RWTree α β)
| fix (r : RWTree α β)

def RWTree.execFuel {α} [DecidableEq α] [Repr α] (fuel : Nat) (g : ExprHigh String α) : RWTree String α → RewriteResult' String α ExprHigh
| base r => r.run' g
| seq r1 r2 => r1.execFuel fuel g >>= r2.execFuel fuel
| par r1 r2 => fun s =>
  match r1.execFuel fuel g s with
  | .error .done _ => r2.execFuel fuel g s
  | x => x
| fix r => fun s =>
  match r.execFuel fuel g s with
  | .error e s' => .error e s'
  | .ok g' s' =>
    match fuel with
    | fuel'+1 => (RWTree.fix r).execFuel fuel' g' s'
    | _ => .error (.error "ran out of fuel") s'

def RWTree.exec {α} [DecidableEq α] [Repr α] (g : ExprHigh String α) (r : RWTree String α) : RewriteResult' String α ExprHigh :=
  r.execFuel 100000 g

/--
Removes a node from the graph, creating a hole, returning the port mapping for that hole, which will either point to IO
ports inside of the graph when connections were removed, or they will point to new IO ports that were present in the
graph beforehand.
-/
def pokeHole {Ident Typ} [Inhabited Ident] [DecidableEq Ident] (i : Ident) (e : ExprHigh Ident Typ) : Option (ExprHigh Ident Typ × PortMapping Ident) := do
  let pm ← e.modules.find? i
  return ({modules := e.modules.eraseAll i,
           connections := e.connections.filter (fun x => not (x.output ∈ pm.1.output.valsList || x.input ∈ pm.1.input.valsList))},
          pm.1.mapPairs (λ k x => e.connections.find? (fun ⟨o, i⟩ => i == x || o == x)
                                  |>.map (fun ⟨o, i⟩ => if i == x then o else i) |>.getD x))

/--
IO ports are generally just unconnected ports, however, they are normally represented by a .top InternPort, which is
assumed to be the case in other parts of the code.  This function therefore takes a graph with unconnected ports, and
transforms them into the .top representation when necessary.

This only works for strings, because we are using the toString function do form the unique label of the top port.
-/
def normalizeIOPorts {α} (g : ExprHigh String α) : ExprHigh String α :=
  {g with
   modules :=
     g.modules.mapVal
       (fun _ v =>
         ⟨v.1.mapPairs (fun | _, p@⟨.internal _, _⟩ => if g.portIsIO p then ⟨.top, toString p⟩ else p | _, p => p), v.2⟩)}



/- def extendWithDFS {Ident Typ} [DecidableEq Ident] (e : ExprHigh Ident Typ) (out inp : InternalPort Ident) := -/


/- def generatePureForMatch {β : Type}
 -   (genPureRewrites : RWTree String β)
 -   : RWTree String β := -/

/- #eval (defaultMatcher ForkSummary2.lhs_extract.fst) graph -/
def graph_1 := (rewrite_fix [ForkSummary2.rewrite] graph).run' ⟨[], 0, ("", 0)⟩ |>.get!
#eval toSVG "random2" graph_1

def resToOption {α β γ} (res : EStateM.Result α β γ) : Option γ :=
  match res with
  | .ok s _ => .some s
  | _ => .none

def stateToOption {α β γ} (res : EStateM.Result α β γ) : β :=
  match res with
  | .ok _ s => s
  | .error _ s => s

def typeToDFGandCFG : String × Nat → DFGandCFG
| ("merge", _) => .dfg .merge
| ("split", _) => .dfg .split
| ("fork2", _) => .dfg .fork
| ("fork1", _) => .dfg .fork
| ("fork3", _) => .dfg .fork
| ("fork4", _) => .dfg .fork
| ("branch", _) => .dfg .branch
| ("Read", n) => .rw (.reads [n])
| ("Write", n) => .rw (.writes [n])
| ("Ccomp Cne", _) => .dfg (.cond (.Ccomp .Cne))
| ("Omove", _) => .dfg .queue
| ("Inop", _) => .dfg .queue
| ("Omod", _) => .dfg (.op .Omod)
| ("Ireturn", n) => .cfg (.Ireturn (.some n))
| _ => .cfg (.Ireturn .none)

def toDFGandCFG (e : ExprHigh String (String × Nat)) : ExprHigh String DFGandCFG :=
  ⟨e.modules.mapVal (fun k v => (v.1, typeToDFGandCFG v.2)), e.connections⟩

#eval RWNotEQ.rewrite.pattern graph_1
def graph_2_int := (rewrite_fix [RWNotEQ.rewrite] graph_1).run ⟨[], 10, ("", 0)⟩
def graph_2 := resToOption graph_2_int |>.get!
#eval graph_2_int
#eval resToOption graph_2_int |>.get!
#eval (stateToOption graph_2_int).runtime_trace.length |> Lean.toJson
#eval toSVG "random3" graph_2

#eval ForkAssoc.rewrite.pattern graph_2
def graph_3_int := (ForkAssoc.rewrite.run' graph_2).run ⟨[], 20, ("", 0)⟩
def graph_3 := resToOption graph_3_int |>.get!
#eval toSVG "random4" graph_3

def graph_4_int := (rewrite_fix [RWNotEQ.rewrite, RWEQ.rewrite] graph_3).run ⟨[], 30, ("", 0)⟩
def graph_4 := resToOption graph_4_int |>.get!
#eval toSVG "random5" graph_4

def graph_5_int := (rewrite_fix [RWNotEQ.rewrite] graph_4).run ⟨[], 40, ("", 0)⟩
def graph_5 := resToOption graph_5_int |>.get!
#eval toSVG "random6" graph_5

def graph_6 := toDFGandCFG graph_5
#eval toSVG "random7" graph_6

#eval! (forkAssoc "b23eebf3").pattern graph_6
def graph_7_int := ((forkAssoc "b23eebf3").run' graph_6).run ⟨[], 50, default⟩
def graph_7 := resToOption graph_7_int |>.get!
#eval! toSVG "random8" graph_7

#eval! combineReads.pattern graph_7
def graph_8_int := (combineReads.run' graph_7).run ⟨[], 60, default⟩
#eval! graph_8_int
def graph_8 := resToOption graph_8_int |>.get!
#eval! toSVG "random9" graph_8

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
