// HZ: this is checking a 3-stage pipeline
// using backward simulation
// For this checking, no extra environmental invariants are needed
// but for the 4-stage pipe, it is needed
#include <chrono>
#include <unordered_map>
#include "apps/debug.h"
#include "assert.h"
#include "config/testpath.h"
#include "frontend/btor2_encoder.h"
#include "apps/pipe_bwd/conds.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/solver.h"


using namespace wasim;
using namespace smt;


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

Term make_term_tranversed(SmtSolver & target_solver,
                          const Term & source_term,
                          std::unordered_set<std::string>& symbol_names) {
  if (source_term->is_symbol()) {
    const std::string & name = source_term->to_string();
    if (symbol_names.find(name) != symbol_names.end()) {
      return target_solver->get_symbol(name);
    }
    Sort sort = source_term->get_sort();
    Sort target_sort = target_solver->make_sort(sort->get_sort_kind(), sort->get_width());
    Term new_symbol = target_solver->make_symbol(name, target_sort);
    symbol_names.insert(name);
    return new_symbol;
  } else if (source_term->is_value()) {
    Sort sort = source_term->get_sort();
    Sort target_sort = target_solver->make_sort(sort->get_sort_kind(), sort->get_width());
    if (sort->get_sort_kind() == BV) {
      return target_solver->make_term(source_term->to_int(), target_sort);
    }  else {
      throw std::runtime_error("Unsupported sort kind");
    }
  } else {
    TermVec new_children;
    for (auto it = source_term->begin(); it != source_term->end(); ++it) {
      new_children.push_back(make_term_tranversed(target_solver, *it, symbol_names));
    }
    Op op = source_term->get_op();
    return target_solver->make_term(op, new_children);
  }
}

void print_term_type_transerved(const Term & t) {
  LOG_DEBUG("{} is_symbol:         {}", t->to_string(),  t->is_symbol());
  LOG_DEBUG("{} is_value:          {}", t->to_string(),  t->is_value());
  LOG_DEBUG("{} is_symbolic_const: {}", t->to_string(),  t->is_symbolic_const());
  LOG_DEBUG("{} is_param:          {}", t->to_string(), t->is_param());
  for (auto it = t->begin(); it != t->end(); ++it) {
    print_term_type_transerved(*it);
  }
}

int main() {


  SmtSolver solver = BoolectorSolverFactory::create(false);

  solver->set_logic("QF_UFBV");
  solver->set_opt("incremental", "true");
  solver->set_opt("produce-models", "true");
  solver->set_opt("produce-unsat-assumptions", "true");

  TransitionSystem sts(solver);
  // BTOR2Encoder btor_parser("/home/hongcez/mingkai/pipe/simple_pipe_stall_short.btor2", sts);
  BTOR2Encoder btor_parser(PROJECT_SOURCE_DIR "/design/bwdsim/simple_pipe_stall_short_reg.btor2", sts);

  // std::cout << sts.trans()->to_string() << std::endl  
  
  // ex_wb_inst[7:6] == 2'b01    Eq( Sel(Sv("ex_wb_inst"), 7, 6), 1 )
  // rs1 = ex_wb_inst[5:4]       auto rs1 = Sel(Sv("ex_wb_inst"), 5,4)
  // rs2 = ex_wb_inst[3:2]       auto rs2 = Sel(Sv("ex_wb_inst"), 3,2)
  // rd = ex_wb_inst[1:0]        auto rd  = Sel(Sv("ex_wb_inst"), 1,0)
  // ex_wb_rd == rd              Eq(Sv("ex_wb_rd"), rd)
  // ex_wb_reg_wen == 1          Eq(Sv("ex_wb_reg_wen"), 1)
  //                             registers = Collect("registers")
  // ex_wb_val == register[rs1] + register[rs2]   Eq(Sv("ex_wb_val"), Add(Read(registers,rs1), Read(registers, rs2)) )

  Conds LastState(sts); // at WB stage
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
  auto res = TransCheck(LastState, { Eq(Sv("wb_go"), 0), Eq(Sv("rst"), 0)}, LastState, NULL);
  assert(res); // this must succeed

  // SecondLastState --> Eq(Sv("ex_go"), 1) -->  LastState

  std::cout << "--------Back to id_ex_regs ---------------\n" ;
  //    The assumptions here are over the pre-state
  auto IdExState = LastState.backward({Eq(Sv("ex_go"),1), Eq(Sv("rst"), 0)});

  IdExState.add(Eq(Sv("id_ex_valid"), 1));
  IdExState.add(Eq(Sv("id_ex_op"), 1));

  // HZ: although we try to simplify below
  // but there are input variables that you cannot eliminate...
  IdExState.simplify_using_mutual_asmpt();
  IdExState.print();
  IdExState.add(Eq(Sel(Sv("id_ex_inst"),7,6), 1));

  // The following checks if this is valid: ex_go ==0 /\ rst == 0 |-> id_go == 0
  std::cout << "Check:"<< IdExState.check( Eq(Sv("id_go"), 0), { Eq(Sv("ex_go"), 0), Eq(Sv("rst"), 0)}  ) << std::endl;


  TermVec failed_constraints;
  // check if we start from pre-state with assumptions, are we guaranteed to end in a state satisfiying post-conditon
  res = TransCheck(IdExState, { Eq(Sv("ex_go"), 0), Eq(Sv("rst"), 0)}, IdExState, &failed_constraints);
  assert(res); // the next loop should be useless, because there should be no failed_constraints
  for (const auto & a : failed_constraints) {
    // TODO: remove the old one...
    std::cout << "[TransCheck] Failed to comply with: " << a->to_string() << std::endl;
    auto inputv = get_semantically_contained_next_input_vars(a, IdExState.conds, sts);
    for (const auto & v : inputv)
      std::cout << "Semantically depends on " << v->to_string() << std::endl;
  }

  auto IfIdState = IdExState.backward({Eq(Sv("id_go"),1), Eq(Sv("rst"), 0)});
  IfIdState.print();
  // This will print 2 conditions
  //   This first one is: D:= (= #b01 ((_ extract 7 6) inst)) 
  //   This is the decode condition
  //   The other is a long condition (C)
  //   Model checking can easily prove: D |-> C
  ///    See the verilog in design/bwdsim, you can uncomment and check it
  //   TODO 1: integrate model checking!!!
  //   TODO 2: add another check to certify the simulation result
  //   TODO 3: maybe integrate with certifaiger

  auto C = IfIdState.conds[0];
  auto D = IfIdState.conds[1];

  SmtSolver s = BoolectorSolverFactory::create(false);;
  s->set_logic("QF_UFBV");
  s->set_opt("incremental", "true");
  s->set_opt("produce-models", "true");
  s->set_opt("produce-unsat-assumptions", "true");

  LOG_DEBUG("{}", (*D->begin())->to_string());
  LOG_DEBUG("{}", ((*D->begin()))->get_sort()->to_string());
  LOG_DEBUG("{}", ((*D->begin()))->to_int());

  auto sort =  ((*D->begin()))->get_sort();
  auto value =  ((*D->begin()))->to_int();
 
  
  assert(value == 1);
  
  auto sk = sort->get_sort_kind();
  LOG_DEBUG("sk: {}", to_string(sk));
  auto width = sort->get_width();
  LOG_DEBUG("width: {}", width);
  assert(s != nullptr);

  std::unordered_set<std::string> symbol_names;
  auto D_tosolve = make_term_tranversed(s, D, symbol_names);
  

  auto C_tosolve = make_term_tranversed(s, C, symbol_names);
  std::cout << "C_tosolve: " << C_tosolve->to_string() << std::endl;
  std::cout << "D_tosolve: " << D_tosolve->to_string() << std::endl;
  auto tosolve = s->make_term(Implies, D_tosolve, C_tosolve);
  LOG_DEBUG("tosolve:{}", tosolve->to_string())

  s->push();
  s->assert_formula(tosolve);
  std::cout << "Model checking: " << s->check_sat() << std::endl;
  s->pop();



  return 0;

}


