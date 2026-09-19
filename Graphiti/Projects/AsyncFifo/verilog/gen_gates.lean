import Graphiti.Projects.AsyncFifo.VerilogGates
-- Run with `lake env lean Graphiti/Projects/AsyncFifo/verilog/gen_gates.lean > async_fifo_gates.v`.
#eval IO.print <| (Graphiti.AsyncFifo.VerilogGates.asyncFifoGates).getD "EXPORT FAILED"
