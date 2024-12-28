#include <chrono>
#include "assert.h"
#include "config/testpath.h"
#include "frontend/btor2_encoder.h"
#include "apps/pipe_bwd/conds.h"


using namespace wasim;
using namespace smt;


void ExamineModel(SmtSolver & sts, const smt::Term & postc, const Conds & prec) {
  UnorderedTermSet prevars;
  UnorderedTermSet postvars;
  for (const auto & c : prec.conds)
    get_free_symbols(c,prevars);

  get_free_symbols(postc, postvars);
  UnorderedTermMap pre_vmap;
  UnorderedTermMap post_vmap;
  for (const auto & v : prevars ) {
    auto val = sts->get_value(v);
    pre_vmap[v] = val;
  }
  for (const auto & v : postvars) {
    if (prevars.find(v) != prevars.end())
      continue;
    auto val = sts->get_value(v);
    post_vmap[v] = val;
  }
  sort_model(pre_vmap);
  std::cout << "-------------------------" << std::endl;
  sort_model(post_vmap);
}

// `out` returns the condition on the pre-state that we need to comply, but actually not...
bool TransCheck(const Conds & c1, const TermVec & transcond, const Conds & c2, TermVec * out) {
  auto & solver = c1.s.get_solver();
  const auto & sts = c1.s;
  bool succ = true;

  
  TermVec c2_simplifed;
  {// first simplify c2
    // collect all assumptions
    TermVec asmpts_all = c1.conds;
    asmpts_all.insert(asmpts_all.end(), transcond.begin(), transcond.end());

    for (const auto & c : c2.conds) {
      // v -> v.next -> v.update_function
      auto next_a = solver->substitute( sts.next(c), sts.next_state_updates() );
      auto next_a_simplified = expr_simplify_ite(next_a, asmpts_all, solver );
      auto next_inputvars = get_semantically_contained_next_input_vars(next_a_simplified, asmpts_all, sts);
      TermVec next_inputvars_vec(next_inputvars.begin(), next_inputvars.end()); // set to vec
      auto quantified_a = UniversalQuantification(next_a_simplified, next_inputvars_vec, solver);
      c2_simplifed.push_back(quantified_a);
    }
  }

  solver->push();
  for (const auto & a : c1.conds)
    solver->assert_formula(a);
  for (const auto & c : transcond)
    solver->assert_formula(c);

  unsigned c2_idx = 0;
  for (const auto & next_a : c2_simplifed) {
    // std::cout << "next a:" << next_a->to_string() << std::endl;
    auto res = solver->check_sat_assuming( {
      solver->make_term(Not, next_a)});
    if (!res.is_unsat()) {
      succ = false;
      if (out)
        out->push_back(next_a);
// ------- DEBUGGING --------
      std::cout << "[TransCheck] Fail idx: " << (c2_idx++) << std::endl;
      ExamineModel(solver, next_a, c1);
// ------- END OF DEBUGGING --------
    } else
      std::cout << "[TransCheck] Ok idx: " << (c2_idx++) << std::endl;
  }
  solver->pop();

  return succ;
}


int main() {


  SmtSolver solver = BoolectorSolverFactory::create(false);

  solver->set_logic("QF_UFBV");
  solver->set_opt("incremental", "true");
  solver->set_opt("produce-models", "true");
  solver->set_opt("produce-unsat-assumptions", "true");

  TransitionSystem sts(solver);
  // BTOR2Encoder btor_parser("/home/hongcez/mingkai/pipe/simple_pipe_stall_short.btor2", sts);
  BTOR2Encoder btor_parser("/home/hongcez/mingkai/pipe/simple_pipe_stall_short_reg.btor2", sts);

  // std::cout << sts.trans()->to_string() << std::endl;
  
  SymbolicSimulator sim(sts, solver);
  
  // ex_wb_inst[7:6] == 2'b01    Eq( Sel(Sv("ex_wb_inst"), 7, 6), 1 )
  // rs1 = ex_wb_inst[5:4]       auto rs1 = Sel(Sv("ex_wb_inst"), 5,4)
  // rs2 = ex_wb_inst[3:2]       auto rs2 = Sel(Sv("ex_wb_inst"), 3,2)
  // rd = ex_wb_inst[1:0]        auto rd  = Sel(Sv("ex_wb_inst"), 1,0)
  // ex_wb_rd == rd              Eq(Sv("ex_wb_rd"), rd)
  // ex_wb_reg_wen == 1          Eq(Sv("ex_wb_reg_wen"), 1)
  //                             registers = Collect("registers")
  // ex_wb_val == register[rs1] + register[rs2]   Eq(Sv("ex_wb_val"), Add(Read(registers,rs1), Read(registers, rs2)) )

  Conds LastState(sts);
  {
    LastState.add( Eq( Sel( Sv("ex_wb_inst"), 7, 6), 1 ) );
    auto rs1 = Sel(Sv("ex_wb_inst"), 5,4);
    auto rs2 = Sel(Sv("ex_wb_inst"), 3,2);
    auto rd  = Sel(Sv("ex_wb_inst"), 1,0);
    LastState.add(Eq(Sv("ex_wb_valid"), 1));
    LastState.add(Eq(Sv("ex_wb_rd"), rd));
    LastState.add(Eq(Sv("ex_wb_reg_wen"), 1));
    auto registers = Collect("registers","","");
    LastState.add( Eq(Sv("ex_wb_val"), Add(Read(registers,rs1), Read(registers, rs2)) ) );
  }
  LastState.print();
  // LastState --> wb_ex == 0 --> LastState (get next state, simplify?)
  //  state union?
  TransCheck(LastState, { Eq(Sv("wb_go"), 0), Eq(Sv("rst"), 0)}, LastState, NULL);

  // SecondLastState --> Eq(Sv("ex_go"), 1) -->  LastState

  std::cout << "--------Back to id_ex_regs ---------------\n" ;
  //    The assumptions here are over the pre-state
  auto IdExState = LastState.backward({Eq(Sv("ex_go"),1), Eq(Sv("rst"), 0)});

  IdExState.add(Eq(Sv("id_ex_valid"), 1));
  IdExState.add(Eq(Sv("id_ex_op"), 1));

  IdExState.simplify_using_mutual_asmpt(); // HZ there are input variables that you cannot avoid...
  IdExState.print();
  // IdExState.add(Eq(Sel(Sv("id_ex_inst"),7,6), 1));

  // std::cout << "Check:"<< IdExState.check( Eq(Sv("id_go"), 0), { Eq(Sv("ex_go"), 0), Eq(Sv("rst"), 0)}  ) << std::endl;

#if 0

  TermVec failed_constraints;
  // check if we start from pre-state with assumptions, are we guaranteed to end in a state satisfiying post-conditon
  TransCheck(IdExState, { Eq(Sv("ex_go"), 0), Eq(Sv("rst"), 0)}, IdExState, &failed_constraints);
  for (const auto & a : failed_constraints) {
    // TODO: remove the old one...
    std::cout << "[TransCheck] Failed to comply with: " << a->to_string() << std::endl;
    auto inputv = get_semantically_contained_next_input_vars(a, IdExState.conds, sts);
    for (const auto & v : inputv)
      std::cout << "Semantically depends on " << v->to_string() << std::endl;
  }
  // TODO : semantically removing independent input vars

  // find the leaf that 
  // TODO: compute fixedpoint under { Eq(Sv("ex_go"), 0), Eq(Sv("rst"), 0)}
  // check that fixed point guarantees { Eq(Sv("ex_go"), 1), Eq(Sv("rst"), 0)}     LastState
  auto IdExStateFixedpoint = IdExState.compute_fixedpoint({ Eq(Sv("ex_go"), 0), Eq(Sv("rst"), 0)});

  TermVec failed_constraints2;
  TransCheck(IdExStateFixedpoint,  { Eq(Sv("ex_go"), 1), Eq(Sv("rst"), 0)}, LastState, &failed_constraints2);
  assert(failed_constraints2.empty());

  exit(1);
#endif

#if 0  
  auto IdExHoldState = IdExState.backward({ Eq(Sv("ex_go"), 0), Eq(Sv("rst"), 0)});
  
  std::cout << "======== IdExHoldState\n" ;
  IdExHoldState.print();
  // IdExState = IdExState.smart_union(IdExHoldState);
  // then check again
  std::cout << "======== IdExState\n" ;
  IdExState.print();
  assert(failed_constraints.empty());


  std::cout << "--------Back to id_ex_regs ---------------\n" ;

  IdExState.backward({Eq(Sv("id_go"),1), Eq(Sv("rst"), 0)});
  IdExState.print();
#endif

  // add the requirement in, and forall quantified input, and check again?

  // SecondLastState --> Eq(Sv("ex_go"), 0) -->  LastState ?


  // std::cout << "-----------------------\n" ;
  // //                                   |->
  // LastState.backward({Eq(Sv("wb_go"), 0), Eq(Sv("ex_go"), 0), Eq(Sv("rst"), 0)});
  // LastState.print();



  // auto varmap = sim.convert( { {"wen_stage2","v"}, {"tag2", 1} } );

  // sim.init();

  // auto s = sim.get_curr_state();

  // std::cout << s.print() ;
  // std::cout << s.print_assumptions();

  // auto inputmap_cycle0 = sim.convert( {{"rst",0}, {"stallex", 0},{"stallwb", 0}, {"inst_valid", "1"}} );
  // auto inputmap = sim.convert( {{"rst",0}, {"stallex", 0},{"stallwb", 0}} );

  // sim.set_input(inputmap_cycle0, {});
  // sim.sim_one_step();
  // sim.print_current_step();
  // sim.print_current_step_assumptions();


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

  // sim.backtrack();
  // sim.undo_set_input();


  return 0;
}


