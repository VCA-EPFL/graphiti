/-
Copyright (c) 2026 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bourgeat, Claude
-/

import Graphiti.Projects.AsyncFifo.GateLiftingR
import Graphiti.Projects.AsyncFifo.Verilog

/-!
# Gate-level Verilog export of the whole FIFO

`Verilog.lean`'s `asyncFifoVerilog` exports the top-level graph with the two clock domains as
*hand-written* Verilog bodies: nothing connects them to the proofs.  This file replaces that.

Every module below is generated from the very `ExprLow` that a refinement theorem is about, and
the module hierarchy is the proof's hierarchy: `dff` from `Dff.dffLowered`, `busreg` from
`BusReg.busLowered` (which instantiates `dff`), and so on up to `async_fifo` from
`asyncFifoLowered`.  The leaves are Boolean gates, wiring, and two cells that are not
hardware in the Lean model and are called out as such:

* `clear_src` --- the reset source.  `Timed.clearSrc`'s contract is `ClearOK Rc`: the clear is
  released by instant `Rc` and stays released.  It exports as a constant, as the oracle does.
* `settling_dff` --- **the metastability assumption**.  `SyncStage.settlingDffO` takes the oracle
  on two ports (`osel`, `ojunk`) that are not wires, so what is left in Verilog is an ordinary
  edge-triggered flip-flop.  Six instances, three per clock domain.  That the real cell settles
  is exactly what this development assumes and cannot prove (`Dff.dff_metastable`).

Nothing here is proved: the framework has no semantics for Verilog, so the templates and the
netlister are trusted.  What *is* different from the old export is that the structure --- every
instance and every connection --- comes from the proved expression rather than from a person.
-/

namespace Graphiti.AsyncFifo.VerilogGates

open Batteries (AssocList)
open Graphiti Graphiti.VerilogExport Graphiti.AsyncFifo.Verilog

/-! ### Emitting one module at a time -/

/-- Like `build_verilog_of_exprLow`, but emits **only** this module: the definitions of its
leaves come from elsewhere, so that a netlist can instantiate another netlist. -/
def build_unit (modName : String) (env : IdentMap String TypedTemplate)
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
  let args := ", ".intercalate ((v.input.toList ++ v.output.toList).map (fun x => format_ident x.1))
  return s!"module {modName}({args});\n{format_declarations_with_interface v}\n\n" ++
    s!"{"\n".intercalate decls.flatten.eraseDups}\n\n{"\n".intercalate bodies}\n\n" ++
    s!"{"\n".intercalate conns}\nendmodule\n"

/-! ### Port lists and cells -/

/-- A declared width: `w 1` is a single wire. -/
def w (n : Nat) : String := s!"[{n-1}:0]"

def ifc (ins outs : List (String × Nat)) : VerilogInterface :=
  ⟨(ins.map (fun x => ((↑x.1 : InternalPort String), s!"input wire {w x.2}"))).toAssocList,
   (outs.map (fun x => ((↑x.1 : InternalPort String), s!"output wire {w x.2}"))).toAssocList⟩

def cell (typ : String) (ins outs : List (String × Nat)) (body : String) : TypedTemplate :=
  ⟨ifc ins outs, typ, body⟩

/-- A fork of `k` outputs, `n` bits wide. -/
def forkCell (typ : String) (k n : Nat) : TypedTemplate :=
  cell typ [("in", n)] ((List.range k).map (fun j => (s!"out{j+1}", n)))
    ("\n".intercalate ((List.range k).map (fun j => s!"assign out{j+1} = in;")))

/-- A boundary cut is stream bookkeeping, not logic: in hardware it is a wire. -/
def cutCell (typ : String) (refs : List String) : TypedTemplate :=
  cell typ (("in", 1) :: refs.map (fun r => (r, 1))) [("out", 1)] "assign out = in;"


def c_and2 : TypedTemplate := cell "and2" [("a",1),("b",1)] [("out",1)] "assign #1 out = a & b;"
def c_or2 : TypedTemplate := cell "or2" [("a",1),("b",1)] [("out",1)] "assign #1 out = a | b;"
def c_nand2 : TypedTemplate := cell "nand2" [("a",1),("b",1)] [("out",1)] "assign #1 out = ~(a & b);"
def c_g2_Bool_and : TypedTemplate := cell "g2_Bool_and" [("a",1),("b",1)] [("out",1)] "assign #1 out = a & b;"
def c_g2_Bool_xor : TypedTemplate := cell "g2_Bool_xor" [("a",1),("b",1)] [("out",1)] "assign #1 out = a ^ b;"
def c_g2_xnor : TypedTemplate := cell "g2_xnor" [("a",1),("b",1)] [("out",1)] "assign #1 out = ~(a ^ b);"
def c_nand3 : TypedTemplate := cell "nand3" [("a",1),("b",1),("c",1)] [("out",1)] "assign #1 out = ~(a & b & c);"
def c_not1 : TypedTemplate := cell "not1" [("a",1)] [("out",1)] "assign #1 out = ~a;"
def c_inv : TypedTemplate := cell "inv" [("a",1)] [("out",1)] "assign #1 out = ~a;"
def c_g1_not : TypedTemplate := cell "g1_not" [("a",1)] [("out",1)] "assign #1 out = ~a;"

def c_fork2 : TypedTemplate := forkCell "fork2" 2 1
def c_fork3 : TypedTemplate := forkCell "fork3" 3 1
def c_fork4 : TypedTemplate := forkCell "fork4" 4 1
def c_fork5 : TypedTemplate := forkCell "fork5" 5 1
def c_fork7 : TypedTemplate := forkCell "fork7" 7 1
def c_fork2_7 : TypedTemplate := forkCell "fork2_7" 2 7

def c_cut3 : TypedTemplate := cutCell "cut3" ["r1","r2","r3"]
def c_cut4 : TypedTemplate := cutCell "cut4" ["r1","r2","r3","r4"]
def c_cutRD : TypedTemplate := cutCell "cutRD" ["r1","r2"]

def c_unpack3 : TypedTemplate := cell "unpack3" [("d",3)] [("b0",1),("b1",1),("b2",1)]
  "assign b0 = d[0];\nassign b1 = d[1];\nassign b2 = d[2];"
def c_pack3 : TypedTemplate := cell "pack3" [("b0",1),("b1",1),("b2",1)] [("q",3)]
  "assign q = {b2, b1, b0};"
def c_unpackSt : TypedTemplate := cell "unpackSt" [("d",7)]
  ((List.range 7).map (fun i => (s!"b{i}", 1)))
  ("\n".intercalate ((List.range 7).map (fun i => s!"assign b{i} = d[{i}];")))
def c_packSt : TypedTemplate := cell "packSt" ((List.range 7).map (fun i => (s!"b{i}", 1))) [("q",7)]
  "assign q = {b6, b5, b4, b3, b2, b1, b0};"
def c_unpack2A : TypedTemplate := cell "unpack2A" [("a",2)] [("b0",1),("b1",1)]
  "assign b0 = a[0];\nassign b1 = a[1];"
def c_packMem : TypedTemplate := cell "packMem" [("q0",1),("q1",1),("q2",1),("q3",1)] [("mem",4)]
  "assign mem = {q3, q2, q1, q0};"
def c_unpackNextW : TypedTemplate := cell "unpackNext_w" [("d",14)]
  [("st",7),("gnext",3),("we",1),("addr",2),("data",1)]
  "assign st = d[6:0];\nassign gnext = d[9:7];\nassign we = d[10];\nassign addr = d[12:11];\nassign data = d[13];"
def c_unpackNextR : TypedTemplate := cell "unpackNext_r" [("d",10)] [("st",7),("gnext",3)]
  "assign st = d[6:0];\nassign gnext = d[9:7];"
def c_fullOf : TypedTemplate := cell "fullOf" [("q",7)] [("full",1)] "assign full = q[3];"
def c_emptyOf : TypedTemplate := cell "emptyOf" [("q",7)] [("empty",1)]
  "assign empty = ~q[3];   // the read state register stores !empty (StRegR.stBit)"
def c_unpRD : TypedTemplate := cell "unpRD" [("st",7),("mem",4)]
  [("a0",1),("a0c",1),("a1",1),("m0",1),("m0c",1),("m1",1),("m2",1),("m3",1)]
  ("assign a0 = st[0];\nassign a0c = st[0];\nassign a1 = st[1];\n" ++
   "assign m0 = mem[0];\nassign m0c = mem[0];\nassign m1 = mem[1];\n" ++
   "assign m2 = mem[2];\nassign m3 = mem[3];")
def c_unpB : TypedTemplate := cell "unpB" [("d",3)] [("b0",1),("b1",1),("b2",1)]
  "assign b0 = d[0];\nassign b1 = d[1];\nassign b2 = d[2];"
def c_unpO : TypedTemplate := cell "unpO" [("orc",6)]
  [("s0",1),("s1",1),("s2",1),("j0",1),("j1",1),("j2",1)]
  ("assign s0 = orc[0];\nassign s1 = orc[1];\nassign s2 = orc[2];\n" ++
   "assign j0 = orc[3];\nassign j1 = orc[4];\nassign j2 = orc[5];")

/-- **The metastability assumption, as a cell.**  `osel`/`ojunk` carry the oracle and are not
wires, so what is left is an ordinary flip-flop. -/
def c_sdff : TypedTemplate := cell "settling_dff"
  [("clk",1),("d",1),("osel",1),("ojunk",1)] [("q",1)]
  "reg qr = 1'b0;\nalways @(posedge clk) qr <= d;\nassign q = qr;"

/-- The reset source.  `Timed.clearSrc`'s contract is `ClearOK Rc`: the clear is held low, is
released by instant `Rc`, and stays released forever after.  Only the *released* half is a
circuit; the pulse itself belongs to the environment, so the cell exports as a constant.  A
simulator that zero-initialises nets starts the latches in exactly the state the pulse would
have left them in, which is what makes this faithful rather than merely convenient. -/
def c_clearSrc : TypedTemplate := cell "clear_src" [] [("crn",1)] "assign crn = 1'b1;"

/-! ### The modules, bottom up -/

def dffEnv : IdentMap String TypedTemplate :=
  [("and2", c_and2), ("nand2", c_nand2), ("nand3", c_nand3), ("fork2", c_fork2), ("fork3", c_fork3), ("fork5", c_fork5), ("cut3", c_cut3)].toAssocList
def dff_if : VerilogInterface := ifc [("clk",1),("d",1),("clrn",1)] [("q",1)]
def m_dff : Option String := build_unit "dff" dffEnv Dff.dffLowered dff_if

def enEnv : IdentMap String TypedTemplate :=
  [("and2", c_and2), ("cut4", c_cut4), ("fork2", c_fork2), ("fork3", c_fork3), ("fork5", c_fork5), ("nand2", c_nand2), ("nand3", c_nand3), ("not1", c_not1), ("or2", c_or2)].toAssocList
def en_if : VerilogInterface := ifc [("clk",1),("en",1),("data",1),("clrn",1)] [("q",1)]
def m_enreg : Option String := build_unit "enreg" enEnv EnReg.enLowered en_if

def s_dff : TypedTemplate := cell "dff" [("clk",1), ("d",1), ("clrn",1)] [("q",1)] ""
def busEnv : IdentMap String TypedTemplate :=
  [("dff", s_dff), ("fork3", c_fork3), ("pack3", c_pack3), ("unpack3", c_unpack3)].toAssocList
def bus_if : VerilogInterface := ifc [("clk",1),("d",3),("clrn",1)] [("q",3)]
def m_busreg : Option String := build_unit "busreg" busEnv BusReg.busLowered bus_if

def stEnv : IdentMap String TypedTemplate :=
  [("dff", s_dff), ("fork7", c_fork7), ("packSt", c_packSt), ("unpackSt", c_unpackSt)].toAssocList
def st_if : VerilogInterface := ifc [("clk",1),("d",7),("clrn",1)] [("q",7)]
def m_streg : Option String := build_unit "streg" stEnv StReg.stLowered st_if
def m_stregr : Option String := build_unit "streg_r" stEnv StRegR.stLowered st_if

def s_enreg : TypedTemplate := cell "enreg" [("clk",1), ("en",1), ("data",1), ("clrn",1)] [("q",1)] ""
def memEnv : IdentMap String TypedTemplate :=
  [("unpack2A", c_unpack2A), ("fork2", c_fork2), ("fork3", c_fork3), ("fork4", c_fork4), ("not1", c_not1), ("and2", c_and2), ("cell", s_enreg), ("packMem", c_packMem)].toAssocList
def mem_if : VerilogInterface :=
  ifc [("clk",1),("we",1),("addr",2),("data",1),("clrn",1)] [("mem",4)]
def m_mem : Option String := build_unit "mem" memEnv Mem.memLowered mem_if

def s_streg : TypedTemplate := cell "streg" [("clk",1), ("d",7), ("clrn",1)] [("q",7)] ""
def s_stregr : TypedTemplate := cell "streg_r" [("clk",1), ("d",7), ("clrn",1)] [("q",7)] ""
def s_busreg : TypedTemplate := cell "busreg" [("clk",1), ("d",3), ("clrn",1)] [("q",3)] ""
def s_mem : TypedTemplate := cell "mem" [("clk",1), ("we",1), ("addr",2), ("data",1), ("clrn",1)] [("mem",4)] ""
def bankEnv : IdentMap String TypedTemplate :=
  [("unpackNext", c_unpackNextW), ("fork3", c_fork3), ("streg", s_streg), ("forkSt", c_fork2_7), ("fullOf", c_fullOf), ("busreg", s_busreg), ("memory", s_mem)].toAssocList
def bank_if : VerilogInterface :=
  ifc [("clk",1),("d",14),("clrn",1)] [("st",7),("full",1),("gray",3),("mem",4)]
def m_bank : Option String := build_unit "bank" bankEnv Bank.bankLowered bank_if

def bankREnv : IdentMap String TypedTemplate :=
  [("unpackNext", c_unpackNextR), ("fork2", c_fork2), ("streg", s_stregr), ("forkSt", c_fork2_7), ("emptyOf", c_emptyOf), ("busreg", s_busreg)].toAssocList
def bankr_if : VerilogInterface :=
  ifc [("clk",1),("d",10),("clrn",1)] [("st",7),("empty",1),("gray",3)]
def m_bankr : Option String := build_unit "bankr" bankREnv BankR.bankLowered bankr_if

def c_unpack2 : TypedTemplate := cell "unpack2" [("st",7),("q1",3)]
  [("p0",1),("p1",1),("p2",1),("fl",1),("q20",1),("q21",1),("q22",1),("q10",1),("q11",1),("q12",1)]
  ("assign p0 = st[0];\nassign p1 = st[1];\nassign p2 = st[2];\nassign fl = st[3];\n" ++
   "assign q20 = st[4];\nassign q21 = st[5];\nassign q22 = st[6];\n" ++
   "assign q10 = q1[0];\nassign q11 = q1[1];\nassign q12 = q1[2];")
def c_pack2 : TypedTemplate := cell "pack2"
  [("p0",1),("p1",1),("p2",1),("fl",1),("q0",1),("q1",1),("q2",1),("g0",1),("g1",1),("g2",1),
   ("we",1),("a0",1),("a1",1),("dt",1)] [("d",14)]
  "assign d = {dt, a1, a0, we, g2, g1, g0, q2, q1, q0, fl, p2, p1, p0};"
def c_unpackR : TypedTemplate := cell "unpackR" [("st",7),("q1",3)]
  [("p0",1),("p1",1),("p2",1),("em",1),("q20",1),("q21",1),("q22",1),("q10",1),("q11",1),("q12",1)]
  ("assign p0 = st[0];\nassign p1 = st[1];\nassign p2 = st[2];\nassign em = ~st[3];\n" ++
   "assign q20 = st[4];\nassign q21 = st[5];\nassign q22 = st[6];\n" ++
   "assign q10 = q1[0];\nassign q11 = q1[1];\nassign q12 = q1[2];")
def c_packR : TypedTemplate := cell "packR"
  [("p0",1),("p1",1),("p2",1),("em",1),("q0",1),("q1",1),("q2",1),("g0",1),("g1",1),("g2",1),
   ("r1",1),("r2",1),("r3",1)] [("d",10)]
  "assign d = {g2, g1, g0, q2, q1, q0, ~em, p2, p1, p0};"

def nextEnv : IdentMap String TypedTemplate :=
  [("unpack2", c_unpack2), ("pack2", c_pack2), ("g1_not", c_g1_not), ("g2_Bool_and", c_g2_Bool_and), ("g2_Bool_xor", c_g2_Bool_xor), ("g2_xnor", c_g2_xnor), ("fork2", c_fork2), ("fork3", c_fork3), ("fork4", c_fork4)].toAssocList
def next_if2 : VerilogInterface := ifc [("st",7),("inc",1),("data",1),("q1",3)] [("d",14)]
def m_next : Option String := build_unit "next_state" nextEnv GateNext.gateNextExpr next_if2

def nextREnv : IdentMap String TypedTemplate :=
  [("unpackR", c_unpackR), ("packR", c_packR), ("g1_not", c_g1_not), ("g2_Bool_and", c_g2_Bool_and), ("g2_Bool_xor", c_g2_Bool_xor), ("g2_xnor", c_g2_xnor), ("fork2", c_fork2), ("fork3", c_fork3), ("fork4", c_fork4)].toAssocList
def nextr_if : VerilogInterface := ifc [("st",7),("inc",1),("q1",3)] [("d",10)]
def m_nextr : Option String := build_unit "next_state_r" nextREnv GateNextR.gateNextRExpr nextr_if

def muxEnv : IdentMap String TypedTemplate :=
  [("unpRD", c_unpRD), ("cutRD", c_cutRD), ("fork2", c_fork2), ("fork3", c_fork3), ("inv", c_inv), ("and2", c_and2), ("or2", c_or2)].toAssocList
def mux_if : VerilogInterface := ifc [("st",7),("mem",4)] [("q",1)]
def m_mux : Option String := build_unit "read_mux" muxEnv ReadMux.muxLowered mux_if

def stageEnv : IdentMap String TypedTemplate :=
  [("unpB", c_unpB), ("unpO", c_unpO), ("fork3", c_fork3), ("sdff", c_sdff), ("pack3", c_pack3)].toAssocList
def stage_if : VerilogInterface := ifc [("clk",1),("d",3),("orc",6)] [("q",3)]
def m_stage : Option String := build_unit "sync_stage" stageEnv SyncStage.stageLowered stage_if

def s_bank : TypedTemplate := cell "bank" [("clk",1), ("d",14), ("clrn",1)] [("st",7), ("full",1), ("gray",3), ("mem",4)] ""
def s_bankr : TypedTemplate := cell "bankr" [("clk",1), ("d",10), ("clrn",1)] [("st",7), ("empty",1), ("gray",3)] ""
def s_next : TypedTemplate := cell "next_state" [("st",7), ("inc",1), ("data",1), ("q1",3)] [("d",14)] ""
def s_nextr : TypedTemplate := cell "next_state_r" [("st",7), ("inc",1), ("q1",3)] [("d",10)] ""
def s_stage : TypedTemplate := cell "sync_stage" [("clk",1), ("d",3), ("orc",6)] [("q",3)] ""
def s_mux : TypedTemplate := cell "read_mux" [("st",7), ("mem",4)] [("q",1)] ""
def wdomEnv : IdentMap String TypedTemplate :=
  [("clkF", c_fork2), ("regBank", s_bank), ("clearSrc", c_clearSrc), ("nextBlock", s_next), ("syncReg", s_stage)].toAssocList
def wdom_if2 : VerilogInterface :=
  ifc [("clk",1),("inc",1),("data",1),("rgray",3),("orc",6)] [("gray",3),("full",1),("mem",4)]
def m_wdom : Option String := build_unit "wdom" wdomEnv Timed.wdomTimedLowered wdom_if2

def rdomEnv : IdentMap String TypedTemplate :=
  [("clkF", c_fork2), ("rregBank", s_bankr), ("clearSrc", c_clearSrc), ("rnextBlock", s_nextr), ("syncReg", s_stage), ("stF", c_fork2_7), ("rdataBlock", s_mux)].toAssocList
def rdom_if2 : VerilogInterface :=
  ifc [("clk",1),("inc",1),("wgray",3),("orc",6),("mem",4)] [("gray",3),("empty",1),("rdata",1)]
def m_rdom : Option String := build_unit "rdom" rdomEnv Timed.rdomTimedLowered rdom_if2

def s_wdom : TypedTemplate := cell "wdom" [("clk",1), ("inc",1), ("data",1), ("rgray",3), ("orc",6)] [("gray",3), ("full",1), ("mem",4)] ""
def s_rdom : TypedTemplate := cell "rdom" [("clk",1), ("inc",1), ("wgray",3), ("orc",6), ("mem",4)] [("gray",3), ("empty",1), ("rdata",1)] ""
def c_oracle : TypedTemplate := cell "oracle" [] [("bits",6)] "assign bits = 6'd0;"
def topEnv : IdentMap String TypedTemplate :=
  [("wdom", s_wdom), ("rdom", s_rdom), ("oracle_w", c_oracle), ("oracle_r", c_oracle)].toAssocList
def top_if2 : VerilogInterface :=
  ifc [("wclk",1),("winc",1),("wdata",1),("rclk",1),("rinc",1)] [("full",1),("empty",1),("rdata",1)]
def m_top : Option String := build_unit "async_fifo" topEnv asyncFifoLowered top_if2

/-! ### The whole design -/

def primitives : List TypedTemplate :=
  [c_and2, c_or2, c_nand2, c_nand3, c_not1, c_inv, c_g1_not, c_g2_Bool_and, c_g2_Bool_xor,
   c_g2_xnor, c_fork2, c_fork3, c_fork4, c_fork5, c_fork7, c_fork2_7, c_cut3, c_cut4, c_cutRD,
   c_unpack3, c_pack3, c_unpackSt, c_packSt, c_unpack2A, c_packMem, c_unpackNextW,
   c_unpackNextR, c_fullOf, c_emptyOf, c_unpRD, c_unpB, c_unpO, c_unpack2, c_pack2,
   c_unpackR, c_packR, c_sdff, c_clearSrc, c_oracle]

/-- **The whole FIFO as gate-level Verilog**, every module generated from the expression its
refinement theorem is about. -/
def asyncFifoGates : Option String := do
  let units ← [m_dff, m_enreg, m_busreg, m_streg, m_stregr, m_mem, m_bank, m_bankr,
               m_next, m_nextr, m_mux, m_stage, m_wdom, m_rdom, m_top].mapM id
  return "\n\n".intercalate ((primitives.map (·.module)).eraseDups ++ units)

#guard asyncFifoGates.isSome

end Graphiti.AsyncFifo.VerilogGates
