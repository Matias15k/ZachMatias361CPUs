#!/usr/bin/env bash

# =======================================================
# 1. Compile the CPU + testbench
# =======================================================
iverilog -g2012 -o executable_pipelined src/template_lab4.v src/tb_v2.v

mkdir -p outputs

# =======================================================
# 2. Put your test names here
# =======================================================
tests=("lui" "easy")

# =======================================================
# 3. Run each test
# =======================================================
for t in "${tests[@]}"; do
    echo "===================================================="
    echo "Running test: $t"
    echo "===================================================="

    mem_in="tests/${t}_mem_in.hex"
    regs_in="tests/${t}_regs_in.hex"

    mem_out="outputs/${t}_mem_out.hex"
    regs_out="outputs/${t}_regs_out.hex"

    vvp executable_pipelined \
        +MEM_IN=$mem_in \
        +REGS_IN=$regs_in \
        +MEM_OUT=$mem_out \
        +REGS_OUT=$regs_out

    echo "Output written to:"
    echo "  $mem_out"
    echo "  $regs_out"
    echo
done