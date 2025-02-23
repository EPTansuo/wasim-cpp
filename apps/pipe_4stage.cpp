#include <chrono>
#include "assert.h"
#include "config/testpath.h"
#include "frontend/btor2_encoder.h"
#include "apps/pipe_bwd/conds.h"


using namespace wasim;
using namespace smt;


// WIP: disable for now
#if 0
// a helper function : the rev version
// it goes from the end to the beginning
void remove_and_move_to_next_backward( /* INOUT */ smt::TermList & eqs, /* INOUT */ smt::TermList::iterator & eq_pos,
  const smt::UnorderedTermSet & unsatcore) {

  auto pred_iter = eqs.end(); // pred_pos;
  auto pred_pos_new = eqs.end();

  pred_pos_new--;

  bool reached = false;
  bool next_pos_found = false;

  while( pred_iter != eqs.begin() ) {
    pred_iter--;
    
    if (!reached && pred_iter == eq_pos)
      reached = true;
    
    if (unsatcore.find(*pred_iter) == unsatcore.end()) {
      assert (reached);
      pred_iter = eqs.erase(pred_iter);
    } else {
      if (reached && ! next_pos_found) {
        pred_pos_new = pred_iter;
        pred_pos_new ++;

        next_pos_found = true;
      }
    }
  } // end of while

  assert(reached);
  if (! next_pos_found) {
    assert (pred_iter == eqs.begin());
    pred_pos_new = pred_iter;
  }
  eq_pos = pred_pos_new;
} // remove_and_move_to_next_backward

void reduce_eq_linear_backwards(SmtSolver & sts, smt::TermList & conjs) {
  auto to_remove_pos_prev = conjs.end();
  while(to_remove_pos_prev != conjs.begin()) {
    to_remove_pos_prev--; // firstly, point to the last one
    if (conjs.size() == 1)
      continue;

    smt::Term term_to_remove = *to_remove_pos_prev;
    auto pos_after_conj = conjs.erase(to_remove_pos_prev);
    smt::Result r = sts->check_sat_assuming_list(conjs);
    to_remove_pos_prev = conjs.insert(pos_after_conj, term_to_remove);
    if (r.is_sat())
      continue;
    // else { // if unsat, we can remove
    smt::UnorderedTermSet core_set;
    sts->get_unsat_assumptions(core_set);
    // below function will update assumption_list and to_remove_pos
    remove_and_move_to_next_backward(conjs, to_remove_pos_prev, core_set);
  } // end of while
} // end of 

void ExtractReducedModel(SmtSolver & sts, const smt::Term & postc, const smt::TermVec & transcond) {
  UnorderedTermSet vars;
  get_free_symbols(postc, vars);
  // TODO
  TermVec eqs; // v == val
  for (const auto & v : vars) {
    auto val = sts->get_value(v);
    eqs.push_back(sts->make_term(Equal, v, val));
  }
  // postc /\ transcond /\ ( v == val /\ ... )   should be UNSAT 
  // sort eqs, small width -> large width
  sort(eqs);

  sts->push();
  for (const auto & a : transcond)
    sts->assert_formula(a);
  reduce_eq_linear_backwards(sts, eqs);
  sts->pop();
} // end of ExtractReducedModel
#endif

void ExamineModel(SmtSolver & sts, const smt::Term & postc, const Conds & prec) {
  UnorderedTermSet prevars;
  UnorderedTermSet postvars;
  // collect all variables in pre-cond
  for (const auto & c : prec.conds)
    get_free_symbols(c,prevars);

  // postvars are also over pre-state, because we already
  // substitute it by transition relations
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
  // BTOR2Encoder btor_parser("/home/hongcez/mingkai/pipe/simple_pipe_stall_reg.btor2", sts);
  BTOR2Encoder btor_parser(PROJECT_SOURCE_DIR "/design/bwdsim/simple_pipe_stall_reg_w_envinv.btor2", sts);

  // std::cout << sts.trans()->to_string() << std::endl  

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
  IfIdState.add(Eq(Sv("if_id_valid"), 1));
  IfIdState.print();

  {
    failed_constraints.clear(); // however, this fails!!!
    TermVec asmpts = { Eq(Sv("id_go"), 0), Eq(Sv("rst"), 0)};
    for (const auto & c : sts.constraints()) {
      std::cout << c.first->to_string() << "\n";
      asmpts.push_back(c.first);
    }
    auto res = TransCheck(IfIdState, asmpts, IfIdState, &failed_constraints);
  }

  TermVec asmpts = { Eq(Sv("if_go"), 1), Eq(Sv("rst"), 0)};
  for (const auto & c : sts.constraints()) { // need environment invariant!!!
    asmpts.push_back(c.first);
  }
  auto IfState = IfIdState.backward(asmpts);
  IfState.print();

  return 0;
}


