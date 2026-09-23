import Graphiti.Projects.AsyncFifo.ProofWriteOnly.Dff
/- Emits a reference trace of the *Lean* flip-flop for `tb_dff.cpp` to check the exported gate
   netlist against, instant by instant.  Four lines: q, clk, d, clrn.
   Run with `lake env lean .../gen_dff_trace.lean > dff_trace.txt`. -/
open Graphiti.AsyncFifo.Dff
def N : Nat := 300
def crn : List Bool := (List.range N).map (fun t => decide (t ≥ 20))
def clk : List Bool := (List.range N).map (fun t => decide (t % 24 ≥ 12))
def d   : List Bool := (List.range N).map (fun t => decide ((t * 2654435761 / 8192) % 2 = 1))
def bits (l : List Bool) : String := String.intercalate "" (l.map (fun b => if b then "1" else "0"))
#eval IO.println (bits (dffOut clk d crn))
#eval IO.println (bits clk)
#eval IO.println (bits d)
#eval IO.println (bits crn)
