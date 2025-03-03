#include "Vpipeline_v.h"
#include "Vpipeline_v_pipeline_v.h"
#include "verilated.h"
#include "verilated_vcd_c.h"
#include <iostream>
#include <string>
#include <vector>
#include <cstdint>
#include <sstream>
#include <unordered_map>

TOP_NAME* dut;
VerilatedContext *contextp;
VerilatedVcdC* tfp;

#define  OP_NOP  0
#define  OP_ADD  1
#define  OP_SET  2
#define  OP_NAND 3

static void single_cycle() {
  dut->clk = 0; dut->eval(); contextp->timeInc(1); tfp->dump(contextp->time());
  dut->clk = 1; dut->eval(); contextp->timeInc(1); tfp->dump(contextp->time());
}



static void reset(int n) {
  dut->rst = 1;
  while (n -- > 0) single_cycle();
  dut->rst = 0;
}

// Instructions
/**
 * 
 * nop
 * add rd,rs0,rs2
 * set rd,imm
 * nand rd,rs1,rs2
 * 
 */
std::unordered_map<std::string , uint8_t> inst_op_map = {
  {"nop", OP_NOP},
  {"add", OP_ADD},
  {"set", OP_SET},
  {"nand", OP_NAND}
};

std::unordered_map<std::string , uint8_t> reg_index_map = {
  {"a0", 0},
  {"a1", 1},
  {"a2", 2},
  {"a3", 3}
};


std::string inst_type(const std::string&inst) {
	if(inst.substr(0,3) == "and" ||
		inst.substr(0,3) == "add" ||
		inst.substr(0,3) == "set"){
		return inst.substr(0,3);
	}
	else if(inst.substr(0,4) == "nand"){
		return inst.substr(0,4);
	}else {
		std::cerr << "Error Instruction!" <<std::endl;
	}
	return "";			
}


std::vector<uint8_t> compile(const std::vector<std::string>& insts) {
  std::vector<uint8_t> insts_ret;
  uint8_t opcode, rs1, rs2, rd, imm;
  for(const auto &inst: insts){
    if(inst == "nop" ){
      insts_ret.push_back(inst_op_map[inst]<<6);
      continue;
    } 
    for(size_t i=0; i<inst.size(); i++){
      if(inst[i] == ' '){
        opcode = inst_op_map[inst.substr(0, i)];
        if(inst.substr(0,i) == "add" || inst.substr(0,i) == "nand"){
          rd = reg_index_map[inst.substr(i+1, 2)];
          rs1 = reg_index_map[inst.substr(i+4, 2)];
          rs2 = reg_index_map[inst.substr(i+7, 2)];
          insts_ret.push_back(opcode<<6 | rs1<<4 | rs2<<2 | rd);
        } else if (inst.substr(0,i) == "set"){
          rd = reg_index_map[inst.substr(i+1, 2)];
          imm = std::stoi(inst.substr(i+4));
          if(imm > 15){
            std::cerr << "Syntax ERROR: " << inst << std::endl;
          }
          insts_ret.push_back(opcode<<6 | imm << 2 | rd);
        } else {
          std::cerr << "Syntax ERROR: " << inst << std::endl;
        }
        break;
      }
    }
  }
  return insts_ret;
}


void print_bin(const std::vector<uint8_t>& insts){
  for(const auto &inst: insts){
    for(int i=7; i>=0; i--){
      std::cout << (inst>>i & 1);
    }
    std::cout << std::endl;
  }
}

void print_asm(const std::vector<std::string> insts){
  for(const auto &inst: insts){
    std::cout << inst << std::endl;
  }
}

std::string to_hex(int num) {
  std::stringstream ss;
  ss << std::hex << num; 
	return ss.str();
}

int main(int argc, char**argv) {
	
	contextp = new VerilatedContext;
	tfp = new VerilatedVcdC; 
	dut = new TOP_NAME(contextp);
  contextp->commandArgs(argc,argv);

	contextp->traceEverOn(true);
	dut->trace(tfp, 0);
	tfp->open("wave.vcd");


  std::cout << "Start simulation..." << std::endl;

  std::vector<std::string> insts_str = {
    "set a0,1",
    "set a1,3",
    "add a2,a0,a1",
		"add a2,a2,a1",
		"nop",
		"nop",
		"set a2,10",
		"add a2,a2,a1",
    "nop"    
  };
  std::cout << "------- asm ------" <<std::endl;
  print_asm(insts_str);
  std::vector<uint8_t> insts = compile(insts_str);
  std::cout << "------- bin ------" <<std::endl;
  print_bin(insts);
  
  reset(10);

	for(int i=0; i<insts.size(); i++){
		dut->inst = insts[i];
		dut->inst_valid = 1;
		single_cycle();
		while(!dut->inst_ready){
			single_cycle();
		}
		std::cout << "wb_finish: " << (dut->pipeline_v->wb_finish ? "1" : "0") << " at time = " << contextp->time() <<std::endl; 
		if(dut->pipeline_v->wb_finish){
			std::cout << "At time = " << contextp->time() << std::endl;
			std::cout << "Inst: " << "0x" << to_hex(dut->pipeline_v->wb_out_inst) 
								<< "  " <<std::bitset<8>(dut->pipeline_v->wb_out_inst).to_string() << std::endl;
			std::cout << "a0: " << "0x" << to_hex(dut->pipeline_v->registers0) << std::endl << 
							   "a2: " << "0x" << to_hex(dut->pipeline_v->registers1) << std::endl << 
								 "a3: " << "0x" << to_hex(dut->pipeline_v->registers2) << std::endl << 
								 "a4: " << "0x" << to_hex(dut->pipeline_v->registers3) << std::endl;
			std::cout << "-----------------" <<std::endl;

		}

	}
	
	for(int i=5; i>=0; --i){
		single_cycle();
	}

	std::cout << "Finished at time = " << contextp->time() << std::endl;
	tfp->close();

}
