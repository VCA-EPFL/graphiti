# Verilog exported from Lean, and the tests that say the export is faithful.
#
#   async_fifo_gates.v  the whole FIFO at gate level, every module generated from the ExprLow a
#                       refinement theorem is about (VerilogGates.lean).
#   next_state.v        the write domain's next-state netlist on its own.
#   next_state_r.v      the read domain's, carved out of the same export.
#
# ONE SIMULATION TIME UNIT IS ONE INSTANT of the Lean model.  With that convention `assign #1` is
# exactly Lean's `gateOut`, and `sim-dff` checks the two agree instant for instant on the
# flip-flop -- cross-coupled NAND latch included.  Everything else here depends on that
# convention, and on driving the design inside the regime the theorem is about: the clear pulses
# before the first edge (ClearOK), the clocks are slower than the delay budget (22 <= P), and the
# inputs are stable half a period before an edge (InOK, S = 17).
#
# Run from the graphiti root:  make -C Graphiti/Projects/AsyncFifo/verilog
# Requires verilator 5 (for --timing) and optionally yosys.
VERILATOR ?= verilator
ROOT := $(abspath ../../../..)
HERE := $(abspath .)

# The clear is released at 12 and the clocks start at 24; the settling stage's clock-to-q is stl.
SIMFLAGS := --timing -DCLEAR_RELEASE=12 -DSETTLE_STL=4 -Wno-DECLFILENAME -Wno-fatal

all: lint sim-dff sim-next sim-nextr sim-fifo

async_fifo_gates.v: gen_gates.lean ../VerilogGates.lean ../Verilog.lean
	cd $(ROOT) && lake build Graphiti.Projects.AsyncFifo.VerilogGates >/dev/null && \
	  lake env lean $(HERE)/gen_gates.lean > $(HERE)/async_fifo_gates.v

next_state.v: gen_next.lean ../Verilog.lean ../GateNext.lean
	cd $(ROOT) && lake build Graphiti.Projects.AsyncFifo.Verilog >/dev/null && \
	  lake env lean $(HERE)/gen_next.lean > $(HERE)/next_state.v

next_state_r.v: async_fifo_gates.v
	python3 -c "import re; src=open('async_fifo_gates.v').read(); \
	  parts=re.split(r'(?m)^(?=module )',src); \
	  by={m.group(1):p for p in parts for m in [re.match(r'module (\w+)\(',p)] if m}; \
	  keep=['g1_not','g2_Bool_and','g2_Bool_xor','g2_xnor','fork2','fork3','fork4','unpackR','packR','next_state_r']; \
	  open('next_state_r.v','w').write(''.join(by[k] for k in keep if k in by))"

dff_only.v: async_fifo_gates.v
	python3 -c "import re; src=open('async_fifo_gates.v').read(); \
	  parts=re.split(r'(?m)^(?=module )',src); \
	  by={m.group(1):p for p in parts for m in [re.match(r'module (\w+)\(',p)] if m}; \
	  keep=['and2','nand2','nand3','fork2','fork3','fork5','cut3','dff']; \
	  open('dff_only.v','w').write(''.join(by[k] for k in keep if k in by))"

# The Lean netlist's own trace, for the differential test below.
dff_trace.txt: gen_dff_trace.lean ../Dff.lean
	cd $(ROOT) && lake build Graphiti.Projects.AsyncFifo.Dff >/dev/null && \
	  lake env lean $(HERE)/gen_dff_trace.lean > $(HERE)/dff_trace.txt

# UNOPTFLAT is expected: a gate-level flip-flop is a cross-coupled NAND latch, so the
# combinational feedback is the circuit, not a defect of the export.
lint: async_fifo_gates.v next_state.v
	$(VERILATOR) --lint-only --timing -Wall -Wno-DECLFILENAME -Wno-UNUSED -Wno-ASSIGNDLY \
	  -Wno-UNOPTFLAT -Wno-PROCASSINIT -DCLEAR_RELEASE=12 -DSETTLE_STL=4 \
	  --top-module async_fifo async_fifo_gates.v
	$(VERILATOR) --lint-only --no-timing -Wall -Wno-DECLFILENAME -Wno-ASSIGNDLY next_state.v

synth: async_fifo_gates.v next_state.v
	yosys -q -p "read_verilog -DCLEAR_RELEASE=12 -DSETTLE_STL=4 async_fifo_gates.v; hierarchy -top async_fifo; proc; flatten; synth; tee -q -o async_fifo_gates.stat stat" >/dev/null 2>&1 || true
	@grep -E "cells|wires|^ +[0-9]+ +[$$]" async_fifo_gates.stat
	yosys -q -p "read_verilog next_state.v; hierarchy -top next_state; proc; flatten; synth; tee -q -o next_state.stat stat" >/dev/null
	@grep -E "cells|wires|^ +[0-9]+ +[$$]" next_state.stat

# **The test that says the export is faithful**: the exported flip-flop against Lean's dffOut.
obj_dir_dff/tb_dff: dff_only.v dff_trace.txt tb_dff.cpp
	$(VERILATOR) --cc --exe --build $(SIMFLAGS) --Mdir obj_dir_dff \
	  --top-module dff dff_only.v tb_dff.cpp -o tb_dff >/dev/null
sim-dff: obj_dir_dff/tb_dff
	./obj_dir_dff/tb_dff

obj_dir_next/tb_next: next_state.v tb_next.cpp
	$(VERILATOR) --cc --exe --build --no-timing -Wno-DECLFILENAME -Wno-ASSIGNDLY -Wno-fatal \
	  --Mdir obj_dir_next --top-module next_state next_state.v tb_next.cpp -o tb_next >/dev/null
sim-next: obj_dir_next/tb_next
	./obj_dir_next/tb_next

obj_dir_nextr/tb_nextr: next_state_r.v tb_nextr.cpp
	$(VERILATOR) --cc --exe --build --no-timing -Wno-DECLFILENAME -Wno-ASSIGNDLY -Wno-fatal \
	  --Mdir obj_dir_nextr --top-module next_state_r next_state_r.v tb_nextr.cpp -o tb_nextr >/dev/null
sim-nextr: obj_dir_nextr/tb_nextr
	./obj_dir_nextr/tb_nextr

obj_dir_fifo/tb_fifo: async_fifo_gates.v tb_fifo.cpp
	$(VERILATOR) --cc --exe --build $(SIMFLAGS) --Mdir obj_dir_fifo \
	  --top-module async_fifo async_fifo_gates.v tb_fifo.cpp -o tb_fifo >/dev/null
sim-fifo: obj_dir_fifo/tb_fifo
	./obj_dir_fifo/tb_fifo

clean:
	rm -rf obj_dir_dff obj_dir_next obj_dir_nextr obj_dir_fifo async_fifo_gates.v \
	  next_state.v next_state_r.v dff_only.v dff_trace.txt async_fifo_gates.stat next_state.stat

.PHONY: all lint synth sim-dff sim-next sim-nextr sim-fifo clean
