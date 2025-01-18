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
  BTOR2Encoder btor_parser("/home/hongcez/mingkai/piccolo/piccolo.btor2", sts);

  Conds LastState(sts);
  {
    auto inst = Sv("inst_reg_s3");
    auto rd = Sel( inst , 11, 7);
    auto rs1 = Sel( inst , 19, 15);
    auto rs2 = Sel( inst , 24, 20);
    LastState.add(Eq(Sv("s2_to_s3"), 1));
    LastState.add(Eq(Sv("gpr_regfile.write_rd_rd"), rd));

    LastState.add(Eq(Sv("gpr_regfile.EN_write_rd"), 1));
    auto registers = Collect("gpr_regfile.regfile.arr","[","]");
    LastState.add( Eq(Sv("gpr_regfile.write_rd_rd_val"), Add(Read(registers,rs1), Read(registers, rs2)) ) );
  }
  LastState.print();
  // LastState --> wb_ex == 0 --> LastState (get next state, simplify?)
  //  state union?
  // TransCheck(LastState, { Eq(Sv("s3_deq$EN"), 0), Eq(Sv("RST_N"), 1)}, LastState, NULL);
  // TransCheck(LastState, { Eq(Sv("s3_deq$D_IN"), 0), Eq(Sv("RST_N"), 1)}, LastState, NULL);
  TransCheck(LastState, { Eq(Sv("rg_retiring$EN"), 0), Eq(Sv("RST_N"), 1)}, LastState, NULL);

  // TODO: you may need to add invariant-gen

#if 0
  // SecondLastState --> Eq(Sv("ex_go"), 1) -->  LastState

  std::cout << "--------Back to id_ex_regs ---------------\n" ;
  //    The assumptions here are over the pre-state
  auto IdExState = LastState.backward({Eq(Sv("ex_go"),1), Eq(Sv("rst"), 0)});

  IdExState.add(Eq(Sv("id_ex_valid"), 1));
  IdExState.add(Eq(Sv("id_ex_op"), 1));

  IdExState.simplify_using_mutual_asmpt(); // HZ there are input variables that you cannot avoid...
  IdExState.print();
  IdExState.add(Eq(Sel(Sv("id_ex_inst"),7,6), 1));

  // ex_go ==0 /\ rst == 0 |-> id_go == 0
  std::cout << "Check:"<< IdExState.check( Eq(Sv("id_go"), 0), { Eq(Sv("ex_go"), 0), Eq(Sv("rst"), 0)}  ) << std::endl;


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

  auto IfIdState = IdExState.backward({Eq(Sv("id_go"),1), Eq(Sv("rst"), 0)});
  IfIdState.print();
  failed_constraints.clear();
  auto res = TransCheck(IfIdState, { Eq(Sv("id_go"), 0), Eq(Sv("rst"), 0)}, IfIdState, &failed_constraints);

  // check this property:
  //  (inst_valid && inst_ready) && (inst[7:6] == ADD) |-> (constraints in IfIdState)
  
  // TODO : semantically removing independent input vars

  // find the leaf that 
  // TODO: compute fixedpoint under { Eq(Sv("ex_go"), 0), Eq(Sv("rst"), 0)}
  // check that fixed point guarantees { Eq(Sv("ex_go"), 1), Eq(Sv("rst"), 0)}     LastState
  // auto IdExStateFixedpoint = IdExState.compute_fixedpoint({ Eq(Sv("ex_go"), 0), Eq(Sv("rst"), 0)});

  // TermVec failed_constraints2;
  // TransCheck(IdExStateFixedpoint,  { Eq(Sv("ex_go"), 1), Eq(Sv("rst"), 0)}, LastState, &failed_constraints2);
  // assert(failed_constraints2.empty());

  exit(1);
#endif

  return 0;
}


