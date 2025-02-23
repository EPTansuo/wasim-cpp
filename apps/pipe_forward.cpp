// HZ: this is of no use for now.
#include <chrono>
#include "assert.h"
#include "config/testpath.h"
#include "frontend/btor2_encoder.h"
#include "framework/symsim.h"
#include "framework/ts.h"
#include "framework/state_simplify.h"
#include "smt-switch/boolector_factory.h"
#include "smt-switch/utils.h"

using namespace wasim;
using namespace smt;


int main() {


  SmtSolver solver = BoolectorSolverFactory::create(false);

  solver->set_logic("QF_UFBV");
  solver->set_opt("incremental", "true");
  solver->set_opt("produce-models", "true");
  solver->set_opt("produce-unsat-assumptions", "true");

  TransitionSystem sts(solver);
  
  BTOR2Encoder btor_parser("/home/hongcez/mingkai/pipe/simple_pipe_stall_short_reg.btor2", sts);

  
  SymbolicSimulator sim(sts, solver);
  
  sim.init();

  auto s = sim.get_curr_state();

  std::cout << s.print() ;
  std::cout << s.print_assumptions();

  auto inputmap_cycle0 = sim.convert( {{"rst",0}, {"stallex", 0},{"stallwb", 0}, {"inst_valid", 1}, {"inst", "instr"}} );
  auto inputmap = sim.convert( {{"rst",0}, {"stallex", 0},{"stallwb", 0}} );

  sim.set_input(inputmap_cycle0, {});
  sim.sim_one_step();
  sim.print_current_step();
  sim.print_current_step_assumptions();


  // sim.set_input(inputmap, {});
  // sim.sim_one_step();
  // sim.print_current_step();
  // sim.print_current_step_assumptions();


  // sim.set_input(inputmap, {});
  // sim.sim_one_step();
  // sim.print_current_step();
  // sim.print_current_step_assumptions();

  // auto s2 = sim.get_curr_state();
  // std::cout << s2.print();
  // std::cout << s2.print_assumptions();

  return 0;
}


