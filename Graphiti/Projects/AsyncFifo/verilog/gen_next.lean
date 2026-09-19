import Graphiti.Projects.AsyncFifo.Verilog
-- Run with `lake env lean Graphiti/Projects/AsyncFifo/verilog/gen_next.lean > next_state.v`.
#eval IO.print <| (Graphiti.AsyncFifo.Verilog.gateNextVerilog).getD "EXPORT FAILED"
