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

Term _Eq(const Term & l, int r, SmtSolver & s) {
  const auto & sort = l->get_sort();
  auto rterm = s->make_term(r, sort);
  return s->make_term(Equal, l, rterm);
}

Term _Eq(const Term & l, const Term & r, SmtSolver & s) {
  return s->make_term(Equal, l, r);
}


Term _Add(const Term & l, int r, SmtSolver & s) {
  const auto & sort = l->get_sort();
  auto rterm = s->make_term(r, sort);
  return s->make_term(BVAdd, l, rterm);
}

Term _Add(const Term & l, const Term & r, SmtSolver & s) {
  return s->make_term(BVAdd, l, r);
}

Term _Ite(const Term & c, const Term & l, const Term & r, SmtSolver & s) {
  return s->make_term(Ite, c, l, r);
}

Term _Sel(const Term & l, unsigned r1, unsigned r2, SmtSolver & s) {
  return s->make_term(Op(Extract, r1, r2),  l);
}

TermVec _Collect(const std::string & name, const std::string & l, const std::string & r, const TransitionSystem & sts) {
  TermVec ret;
  for (unsigned idx = 0; ; ++idx) {
    try {
      auto t = sts.lookup(name + l + std::to_string(idx)+r);
      ret.push_back(t);
    } catch (SimulatorException e) {
      break;
    }
  }
  return ret;
}

Term _Sv(const std::string & name, const TransitionSystem & sts) {
  return sts.lookup(name);
}

Term _Read(const TermVec & vec, const Term & idx, SmtSolver & s) {
  assert(!vec.empty());
  auto e = vec.at(0);
  for (int i = 1; i<vec.size(); ++i) {
    e = _Ite(_Eq(idx, i,s), vec.at(i), e, s);
  }
  return e;
}

#define Eq(l, r)   (_Eq((l),(r),(solver)))
#define Add(l, r)  (_Add((l), (r), (solver)))
#define Read(l, r) (_Read((l), (r), (solver)))
#define Sel(e, l, r)  (_Sel((e),(l), (r), (solver)))
#define Sv(n)   (_Sv((n),sts))
#define Collect(n,l,r) (_Collect((n),(l),(r),sts))

struct Conds{
  TermVec conds;
  TransitionSystem & s;

  Conds(TransitionSystem & sts) : s(sts) {}
  void add(const Term & t) {conds.push_back(t);}
  void backward(const TermVec & assumptions) {
    TermVec nvec;
    const auto & vmap = s.state_updates();
    auto & solver = s.get_solver();
    for (const auto c : conds) {
      auto nexpr = solver->AbsSmtSolver::substitute(c, vmap);
      // TODO: input variables?
      // TODO: think about this :  should be before this state
      nexpr = expr_simplify_ite(nexpr, assumptions, solver);
      // todo: add xxx == 0 --> replace ...
      nvec.push_back(nexpr);
    }
    conds.swap(nvec);    
  }

  bool check(const Term & t, const TermVec & assumptions) {
    auto & solver = s.get_solver();
    solver->push();
    for (const auto & a: conds)
      solver->assert_formula(a);
    for (const auto & a: assumptions)
      solver->assert_formula(a);
    solver->assert_formula(solver->make_term(Not, t));
    auto res = solver->check_sat();
    solver->pop();
    return res.is_unsat();
  }

  void print() const {
    for (const auto & c : conds) {
      std::cout << " #### " << c->to_string() << std::endl;
    }
  }
}; // Conditions

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

bool TransCheck(const Conds & c1, const TermVec & transcond, const Conds & c2, TermVec * out) {
  auto & solver = c1.s.get_solver();
  const auto & sts = c1.s;
  bool succ = true;
  Term tmp1;
  Term temp;
  solver->push();
  for (const auto & a : c1.conds)
    solver->assert_formula(a);
  for (const auto & c : transcond)
    solver->assert_formula(c);
  for (const auto & a : c2.conds) {
    auto next_a = solver->substitute( sts.next(a), sts.next_state_updates() );
    // std::cout << "next a:" << next_a->to_string() << std::endl;
    auto res = solver->check_sat_assuming( {
      solver->make_term(Not, next_a)});
    if (!res.is_unsat()) {
      succ = false;
      if (out)
        out->push_back(next_a);
      std::cout << "Fail" << std::endl;
      ExamineModel(solver, next_a, c1);
      temp = next_a;
      tmp1 = a;
    } else
      std::cout << "Ok" << std::endl;
  }
  solver->pop();
  if (!succ) {
      auto assumptions = transcond;
      for (const auto & a : c1.conds) {
        if (a != tmp1)
          assumptions.push_back(a);
      }
      tmp1 = expr_simplify_ite(tmp1, assumptions, solver);
      std::cout << ">>> " << tmp1->to_string() << std::endl;

      assumptions.push_back(tmp1);
      // for (const auto & a : c1.conds)
      //   assumptions.push_back(a);
      temp = expr_simplify_ite(temp, assumptions, solver);
      std::cout << "!!! " << temp->to_string() << std::endl;
      // todo extract model
  }
  return succ;
}

Term UniversalInputQuantification(const Term & in, const TransitionSystem & sts) {
  UnorderedTermSet vars;
  get_free_symbols(in,vars);

  TermVec nxt_inputvars;
  for (const auto & v : vars) {
    sts.is_next_input_var(v);
    nxt_inputvars.push_back(v);
  }

  std::vector<int> vals;
  for(const auto & v : nxt_inputvars)
    vals.push_back(0);
  
  while(true) {
    #error todo
    // generate one assignment
    // substitution
    // move to next
    //    if you cannot find the next
    //    then break
    bool succ = false;
    for(int i = vals.size() - 1; i >=0; --i) {
      vals.at(i) ++;
      auto s = nxt_inputvars.at(i)->get_sort();
      unsigned width = s->get_sort_kind() == SortKind::BOOL ? 1 : s->get_width();
      auto maxval = 1 << width;
      if (vals.at(i) != maxval) {
        succ = true;
        break;
      } // else
      vals.at(i) = 0; // then move to next
    }
    if (!succ)
      break;
  } // end of while
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

  std::cout << "-----------------------\n" ;
  //                                   |->
  LastState.backward({Eq(Sv("ex_go"),1), Eq(Sv("rst"), 0)});
  LastState.add(Eq(Sv("id_ex_valid"), 1));
  LastState.add(Eq(Sv("id_ex_op"), 1));
  // LastState.add(Eq(Sel(Sv("id_ex_inst"),7,6), 1));
  

  LastState.print();

  std::cout << "Check:"<< LastState.check( Eq(Sv("id_go"), 0), { Eq(Sv("ex_go"), 0), Eq(Sv("rst"), 0)}  ) << std::endl;

  TermVec failed_constraints;
  TransCheck(LastState, { Eq(Sv("ex_go"), 0), Eq(Sv("rst"), 0)}, LastState, &failed_constraints);
  for (const auto & a : failed_constraints) {
    auto new_cond = UniversalInputQuantification(a, sts);
    LastState.add(new_cond);
  }

  TransCheck(LastState, { Eq(Sv("ex_go"), 0), Eq(Sv("rst"), 0)}, LastState, NULL); // ?


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


