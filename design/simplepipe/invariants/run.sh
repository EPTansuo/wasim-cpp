#!/bin/bash
yosys -s gen_btor.ys > __yosys_exec_result.txt
pono --vcd cex.vcd -e ind  problem.btor2 
