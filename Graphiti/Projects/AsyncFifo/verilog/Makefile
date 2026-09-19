# Two exports, both regenerated from Lean:
#   async_fifo_gates.v — the WHOLE FIFO at gate level.  Every module is generated from the very
#                    `ExprLow` a refinement theorem is about, and the module hierarchy is the
#                    proof's hierarchy (dff, enreg, busreg, streg, mem, bank, next_state,
#                    read_mux, sync_stage, wdom, rdom, async_fifo).  Its only non-gate cells are
#                    `settling_dff` (the metastability assumption, six instances) and
#                    `clear_src`/`oracle`, which model the environment rather than hardware.
#   next_state.v   — the gate netlist of the write domain's next-state logic on its own, checked
#                    exhaustively against `wNext` by tb_next.cpp.
# Run from the graphiti root:
#   make -C Graphiti/Projects/AsyncFifo/verilog
# Requires: verilator (and optionally yosys).
ROOT := $(abspath ../../../..)
HERE := $(abspath .)

all: lint sim-next sim-nextr sim-fifo

async_fifo_gates.v: gen_gates.lean ../VerilogGates.lean ../Verilog.lean
	cd $(ROOT) && lake build Graphiti.Projects.AsyncFifo.VerilogGates >/dev/null && \
	  lake env lean $(HERE)/gen_gates.lean > $(HERE)/async_fifo_gates.v

next_state.v: gen_next.lean ../Verilog.lean ../GateNext.lean
	cd $(ROOT) && lake build Graphiti.Projects.AsyncFifo.Verilog >/dev/null && \
	  lake env lean $(HERE)/gen_next.lean > $(HERE)/next_state.v

# UNOPTFLAT is expected: a gate-level flip-flop is a cross-coupled NAND latch, so the
# combinational feedback Verilator reports is the circuit, not a defect of the export.
lint: async_fifo_gates.v next_state.v
	verilator --lint-only -Wall -Wno-DECLFILENAME -Wno-UNUSED -Wno-ASSIGNDLY -Wno-UNOPTFLAT \
	  --top-module async_fifo async_fifo_gates.v
	verilator --lint-only -Wall -Wno-DECLFILENAME -Wno-ASSIGNDLY next_state.v

synth: async_fifo_gates.v next_state.v
	yosys -q -p "read_verilog async_fifo_gates.v; hierarchy -top async_fifo; proc; flatten; synth; tee -q -o async_fifo_gates.stat stat" >/dev/null 2>&1 || true
	@grep -E "cells|wires|^ +[0-9]+ +[$$]" async_fifo_gates.stat
	yosys -q -p "read_verilog next_state.v; hierarchy -top next_state; proc; flatten; synth; tee -q -o next_state.stat stat" >/dev/null
	@grep -E "cells|wires|^ +[0-9]+ +[$$]" next_state.stat

obj_dir_next/tb_next: next_state.v tb_next.cpp
	verilator --cc --exe --build -Wno-DECLFILENAME -Wno-ASSIGNDLY -Wno-fatal --Mdir obj_dir_next \
	  --top-module next_state next_state.v tb_next.cpp -o tb_next >/dev/null

# Exhaustive check of the exported gate netlist against the Lean next-state function.
sim-next: obj_dir_next/tb_next
	./obj_dir_next/tb_next

next_state_r.v: async_fifo_gates.v
	python3 -c "import re; src=open('async_fifo_gates.v').read(); \
	  parts=re.split(r'(?m)^(?=module )',src); \
	  by={m.group(1):p for p in parts for m in [re.match(r'module (\w+)\(',p)] if m}; \
	  keep=['g1_not','g2_Bool_and','g2_Bool_xor','g2_xnor','fork2','fork3','fork4','unpackR','packR','next_state_r']; \
	  open('next_state_r.v','w').write(''.join(by[k] for k in keep if k in by))"

obj_dir_nextr/tb_nextr: next_state_r.v tb_nextr.cpp
	verilator --cc --exe --build -Wno-DECLFILENAME -Wno-ASSIGNDLY -Wno-fatal --Mdir obj_dir_nextr \
	  --top-module next_state_r next_state_r.v tb_nextr.cpp -o tb_nextr >/dev/null

# Exhaustive check of the read domain's next-state netlist against `rNext`.
sim-nextr: obj_dir_nextr/tb_nextr
	./obj_dir_nextr/tb_nextr

# --public-flat-rw is load-bearing, not cosmetic: a gate-level flip-flop is a cross-coupled NAND
# latch, and with its optimiser free to reorder those feedback nets Verilator mis-schedules them
# and the FIFO misbehaves (it accepts past its depth).  Marking every net public forces the
# conservative settle that a delay-aware event simulator would do anyway.
obj_dir_fifo/tb_fifo: async_fifo_gates.v tb_fifo.cpp
	verilator --cc --exe --build --public-flat-rw -Wno-DECLFILENAME -Wno-ASSIGNDLY \
	  -Wno-UNOPTFLAT -Wno-fatal --Mdir obj_dir_fifo --top-module async_fifo \
	  async_fifo_gates.v tb_fifo.cpp -o tb_fifo >/dev/null

# The whole FIFO: four clock-ratio scenarios, checked for FIFO order, depth and liveness.
sim-fifo: obj_dir_fifo/tb_fifo
	./obj_dir_fifo/tb_fifo

clean:
	rm -rf obj_dir_next obj_dir_nextr obj_dir_fifo async_fifo_gates.v next_state.v \
	  next_state_r.v async_fifo_gates.stat next_state.stat

.PHONY: all lint synth sim-next sim-nextr sim-fifo clean
