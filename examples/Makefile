BUILD_DIR := build_dir
BSCFLAGS := -show-schedule -vdir $(BUILD_DIR) -bdir $(BUILD_DIR) -simdir $(BUILD_DIR)

.PHONY: test-static
test-static: testbench-static
	./testbench-static

.PHONY: test-dynamic
test-dynamic: testbench-dynamic
	./testbench-dynamic

testbench-static: $(BUILD_DIR)/mkStaticTestBench.ba
	bsc $(BSCFLAGS) -sim -e mkStaticTestBench -o testbench-static $(BUILD_DIR)/mkStaticTestBench.ba

testbench-dynamic: $(BUILD_DIR)/mkDynamicTestBench.ba
	bsc $(BSCFLAGS) -sim -e mkDynamicTestBench -o testbench-dynamic $(BUILD_DIR)/mkDynamicTestBench.ba

$(BUILD_DIR)/mkStaticTestBench.ba: arbiter-simulation.bsv
	@mkdir -p $(BUILD_DIR)
	bsc $(BSCFLAGS) -u -sim -g mkStaticTestBench arbiter-simulation.bsv

$(BUILD_DIR)/mkDynamicTestBench.ba: arbiter-simulation.bsv
	@mkdir -p $(BUILD_DIR)
	bsc $(BSCFLAGS) -u -sim -g mkDynamicTestBench arbiter-simulation.bsv
