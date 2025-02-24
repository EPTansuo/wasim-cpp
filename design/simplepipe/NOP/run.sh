#!/bin/bash
yosys -s gen_btor.ys > __yosys_exec_result.txt
pono --vcd cex.vcd -e ind  problem.btor2 
yosys -s gen_sanity_prop.ys > __yosys_exec_result.sanity.txt
pono --vcd cex.vcd -e ind  sanity.btor2 
