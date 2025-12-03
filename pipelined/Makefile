SIM       = iverilog
SIMFLAGS  = -g2012
TOP_SRCS  = src/template_lab4.v src/tb_v2.v
OUT_DIR   = outputs
EXE       = $(OUT_DIR)/executable_pipelined

# List test names here!
TESTS = lui easy jump immediate shifts alu stores loads forwarding1 forwarding2 compilation_1 compilation_2 compilation_3 basic_raw basic_load_store

all: $(EXE)

$(EXE): $(TOP_SRCS)
	mkdir -p $(OUT_DIR)
	$(SIM) $(SIMFLAGS) -o $@ $^

run: $(EXE)
	@if [ -z "$(TEST)" ]; then \
	  echo "Usage: make run TEST=<name>"; \
	  exit 1; \
	fi
	mkdir -p $(OUT_DIR)
	vvp $(EXE) \
	  +MEM_IN=tests/$(TEST)_mem_in.hex \
	  +REGS_IN=tests/$(TEST)_regs_in.hex \
	  +MEM_OUT=$(OUT_DIR)/$(TEST)_mem_out.hex \
	  +REGS_OUT=$(OUT_DIR)/$(TEST)_regs_out.hex \
	  +DUMP=$(OUT_DIR)/$(TEST).vcd

# make run_all
run_all: $(EXE)
	mkdir -p $(OUT_DIR)
	@for t in $(TESTS); do \
	  echo "Running $$t"; \
	  vvp $(EXE) \
	    +MEM_IN=tests/$${t}_mem_in.hex \
	    +REGS_IN=tests/$${t}_regs_in.hex \
	    +MEM_OUT=$(OUT_DIR)/$${t}_mem_out.hex \
	    +REGS_OUT=$(OUT_DIR)/$${t}_regs_out.hex \
	    +DUMP=$(OUT_DIR)/$${t}.vcd; \
	  echo; \
	done

clean:
	rm -rf $(OUT_DIR)
