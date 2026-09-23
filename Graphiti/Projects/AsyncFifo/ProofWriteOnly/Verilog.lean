/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.ProofWriteOnly.Modules
import Graphiti.Projects.AsyncFifo.ProofWriteOnly.WriteNext
import Graphiti.Core.Netlist.VerilogExport

/-!
# Verilog export of the asynchronous FIFO

`Graphiti.Core.Netlist.VerilogExport` is a syntactic netlister: every leaf module comes with
a hand-written Verilog template, and the top-level module is generated from the very same
`ExprHigh` graph that defines the Lean circuit (one instantiation per node, one `assign` per
connection).  Two limitations of the core exporter matter here:

* it never declares the internal nets, so they become implicit 1-bit wires, which is wrong as
  soon as a wire carries a bus (the Gray pointers, the data, the memory);
* it returns `Option String`, and the repository's own `#eval IO.print <| …` calls print
  `none` / `(some …)` without anybody noticing.

This file adds a small, self-contained extension: a `TypedTemplate` carries the declared
type of every port, and `build_verilog_module_typed` declares each internal net with the
type of the port driving it.  Everything else is reused from the core exporter.

The export here is `gateNextVerilog`: its leaves *are* gates, and it is generated from
`WriteNext.gateNextExpr`, the very expression the refinement theorem is about.  What is still
unverified is the exporter and the templates, not the circuit.

`VerilogGates.lean` builds on this file and exports the *whole* FIFO the same way, one module
per proved netlist.  A register-level export with hand-written clock-domain bodies used to live
here as well; it was removed once the gate-level one covered the whole design.

-/

namespace Graphiti.AsyncFifo.Verilog

open Graphiti Graphiti.VerilogExport

/-- A leaf template that also records the declared type of each port. -/
structure TypedTemplate where
  iface : VerilogInterface
  typ : String
  body : String

def TypedTemplate.module (t : TypedTemplate) : String := build_local_module t.typ t.iface t.body

/-- `"input wire [7:0]"` ↦ `"wire [7:0]"`. -/
def declType (s : String) : String := (s.replace "input " "").replace "output " ""

/-! ### Export of the gate netlist

The next-state logic of the write domain is the one part of the design that is already a
netlist of gates (`WriteNext.lean`, depth `4` and 1-bit data), and `gateNext_refines` is proved
about the very expression exported here: `build_verilog_of_exprLow` walks `gateNextExpr`
itself, rather than a graph transcribed from it.

The record-typed buses of the Lean netlist become flat vectors, lowest field first:

    st = {q2[2:0], full, ptr[2:0]}                          (7 bits, the state register)
    d  = {data, addr[1:0], we, gnext[2:0], st'[6:0]}        (14 bits, the next-state bus)

`unpack2` and `pack2` are exactly these bit selections, so they carry no logic.  Gates get the
`#1` delay of the Lean model; forks and the bus adapters are plain wires. -/

/-- The connections of a lowered expression, outermost first. -/
def exprConns : ExprLow String String → List (Connection String)
  | .base _ _ => []
  | .product a b => exprConns a ++ exprConns b
  | .connect c e => c :: exprConns e

/-- The instance name of a base module: the node name its internal ports carry. -/
def instName (pm : PortMapping String) (fallback : Nat) : String :=
  match (pm.input.toList ++ pm.output.toList).findSome?
      (fun x => match x.2 with | ⟨.internal n, _⟩ => some n | _ => none) with
  | some n => n
  | none => s!"u{fallback}"

/-- Like `build_verilog_module_typed`, but for a lowered expression: one instantiation per
`base`, one `assign` per `connect`. -/
def build_verilog_of_exprLow (modName : String) (env : IdentMap String TypedTemplate)
    (e : ExprLow String String) (v : VerilogInterface) : Option String := do
  let insts := e.build_module_names
  let decls ← insts.mapM (fun (pm, typ) => do
    let t ← env.find? typ
    let decl (m : PortMap String String) (p : PortMap String (InternalPort String)) : List String :=
      p.toList.filterMap (fun (port, target) =>
        match target with
        | ⟨.internal _, _⟩ => (m.find? port).map (fun d => s!"{declType d} {format_ident target};")
        | _ => none)
    return decl t.iface.input pm.input ++ decl t.iface.output pm.output)
  let bodies ← insts.zipIdx.mapM (fun ((pm, typ), k) => do
    let t ← env.find? typ
    return format_instantiation t.typ (instName pm k) pm)
  let conns := (exprConns e).map (fun ⟨o, i⟩ => s!"assign {format_ident i} = {format_ident o};")
  let mods := "\n\n".intercalate (env.toList.map (·.2.module) |>.eraseDups)
  let args := ", ".intercalate ((v.input.toList ++ v.output.toList).map (fun x => format_ident x.1))
  return s!"{mods}\n\nmodule {modName}({args});\n{format_declarations_with_interface v}\n\n" ++
    s!"{"\n".intercalate decls.flatten}\n\n{"\n".intercalate bodies}\n\n{"\n".intercalate conns}\nendmodule\n"

def gate2_t (typ op : String) : TypedTemplate :=
  ⟨simple_interface ["a", "b"] ["out"], typ, s!"assign #1 out = {op};"⟩

def gateEnv : IdentMap String TypedTemplate :=
  [ ("g2_Bool_and", gate2_t "g2_Bool_and" "a & b")
  , ("g2_Bool_xor", gate2_t "g2_Bool_xor" "a ^ b")
  , ("g2_xnor", gate2_t "g2_xnor" "~(a ^ b)")
  , ("g1_not", ⟨simple_interface ["a"] ["out"], "g1_not", "assign #1 out = ~a;"⟩)
  , ("fork2", ⟨simple_interface ["in"] ["out1", "out2"], "fork2",
      "assign out1 = in;\nassign out2 = in;"⟩)
  , ("fork3", ⟨simple_interface ["in"] ["out1", "out2", "out3"], "fork3",
      "assign out1 = in;\nassign out2 = in;\nassign out3 = in;"⟩)
  , ("fork4", ⟨simple_interface ["in"] ["out1", "out2", "out3", "out4"], "fork4",
      "assign out1 = in;\nassign out2 = in;\nassign out3 = in;\nassign out4 = in;"⟩)
  , ("unpack2", ⟨⟨[(↑"st", "input wire [6:0]"), (↑"q1", "input wire [2:0]")].toAssocList,
      ["p0", "p1", "p2", "fl", "q20", "q21", "q22", "q10", "q11", "q12"].map
        (fun x => (⟨.top, x⟩, "output wire [0:0]")) |>.toAssocList⟩, "unpack2",
      "assign p0 = st[0];\nassign p1 = st[1];\nassign p2 = st[2];\nassign fl = st[3];\n" ++
      "assign q20 = st[4];\nassign q21 = st[5];\nassign q22 = st[6];\n" ++
      "assign q10 = q1[0];\nassign q11 = q1[1];\nassign q12 = q1[2];"⟩)
  , ("pack2", ⟨⟨["p0", "p1", "p2", "fl", "q0", "q1", "q2", "g0", "g1", "g2", "we", "a0", "a1", "dt"].map
        (fun x => (⟨.top, x⟩, "input wire [0:0]")) |>.toAssocList,
      [(↑"d", "output wire [13:0]")].toAssocList⟩, "pack2",
      "assign d = {dt, a1, a0, we, g2, g1, g0, q2, q1, q0, fl, p2, p1, p0};"⟩)
  ].toAssocList

def next_if : VerilogInterface :=
  ⟨[(↑"st", "input wire [6:0]"), (↑"inc", "input wire [0:0]"), (↑"data", "input wire [0:0]"),
    (↑"q1", "input wire [2:0]")].toAssocList,
   [(↑"d", "output wire [13:0]")].toAssocList⟩

/-- **The exported Verilog of the gate netlist**, from the expression `gateNext_refines` is
about. -/
def gateNextVerilog : Option String :=
  build_verilog_of_exprLow "next_state" gateEnv WriteNext.gateNextExpr next_if

-- The export succeeds, instantiates every gate and fork of the netlist (16 gates, 9 forks and
-- the two bus adapters) and wires the carry chain.
#guard gateNextVerilog.isSome
#guard ((gateNextVerilog.getD "").splitOn "g2_Bool_xor ").length == 9   -- 8 XOR instances
#guard ((gateNextVerilog.getD "").splitOn "g2_Bool_and ").length == 6   -- 5 AND instances
#guard ((gateNextVerilog.getD "").splitOn "g2_xnor ").length == 3       -- 2 XNOR instances
#guard ((gateNextVerilog.getD "").splitOn "g1_not ").length == 2        -- 1 inverter
#guard ((gateNextVerilog.getD "").splitOn "fork").length == 13          -- 3 + 4 + 2 forks, 3 modules
#guard ((gateNextVerilog.getD "").splitOn "assign cp1_b = fc0_out2;").length == 2
#guard ((gateNextVerilog.getD "").splitOn "wire [13:0] pk_d;").length == 1 -- `d` is a top port

end Graphiti.AsyncFifo.Verilog
