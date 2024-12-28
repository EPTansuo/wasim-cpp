#pragma once

#include "apps/pipe_bwd/ops.h"
#include "framework/symsim.h"
#include "framework/state_simplify.h"
#include "framework/sygus_simplify.h"

namespace wasim {


struct Conds{
  smt::TermVec conds;
  TransitionSystem & s;

  smt::Term safe_nxt_substitute(const smt::Term &in) const {
    smt::UnorderedTermSet vars;
    smt::get_free_symbols(in, vars);
    for (const auto & v : vars) {
      if (s.is_next_input_var(v))
        throw SimulatorException("Cannot safely map " + v->to_string() + " to next.");
    }
    return s.next(in);
  } // make sure we don't accidentally substitute xx.nxt -> xx.nxt

  Conds(TransitionSystem & sts) : s(sts) {}
  void add(const smt::Term & t) {conds.push_back(t);}

  Conds backward(const smt::TermVec & assumptions) const {

    std::cout << "[backward] pre-check:" << std::endl;
    check_contains_inputvar();

    Conds ret(s);
    smt::TermVec & nvec = ret.conds;
    const auto & vmap = s.state_updates();
    auto & solver = s.get_solver();
    for (const auto & c : conds) {
      // Do NOT use this: auto nexpr = solver->AbsSmtSolver::substitute(c, vmap);
      // because we want to make sure the inputs are carefully handled
      auto nexpr = solver->AbsSmtSolver::substitute( safe_nxt_substitute(c), s.next_state_updates() );
      
      // TODO: input variables?
      // TODO: think about this :  should be before this state
      nexpr = expr_simplify_ite(nexpr, assumptions, solver);
      // todo: add xxx == 0 --> replace ...
      nvec.push_back(nexpr);
    } // for each cond in 
    
    ret.simplify_inputvar_foreach_constraint(assumptions);

    std::cout << "[backward] post-check:" << std::endl;
    ret.check_contains_inputvar();

    return ret;
  } // end of backwards

  
  // simplify all conds, when processing c, using all conds other than c
  void simplify_using_mutual_asmpt() {
    auto & solver = s.get_solver();
    for (auto it = conds.begin(); it != conds.end();  ++it) {
      smt::TermVec conds_wo_c;
      for (auto copy_it = conds.begin(); copy_it != conds.end();  ++copy_it) {
        if (copy_it != it)
          conds_wo_c.push_back(*copy_it);
      } // end of copy
      *it = expr_simplify_ite(*it, conds_wo_c, solver);
    }
    // remove trivial ones
    for (auto it = conds.begin(); it != conds.end(); ) {
      if ( (*it)->is_value() ) {
        if ((*it)->to_int() == 1) {
          it = conds.erase(it);
          std::cout << "[simplify] remove constant true" << std::endl;
          continue;
        }
        if ((*it)->to_int() == 0)
         throw std::runtime_error("the condition cannot be satisfied!");
      } // end of check
      ++it;
    }
  } // end of simplify_using_mutual_asmpt

  // ----------------------------------------------------------------------------
  // for each constraint, try to simplify its inputs
  void simplify_inputvar_foreach_constraint(const smt::TermVec & asmpt) {

    for (const auto & c : asmpt) {
      std::cout << "C>>> " << c->to_string() << std::endl;
    }

    auto & solver = s.get_solver();
    for (auto & c : conds) {
      smt::TermVec all_asmpt(asmpt);
      for (const auto & c_rest : conds) {
        if (c_rest != c) 
          all_asmpt.push_back(c_rest);
      }
      
      smt::UnorderedTermSet vars;
      get_free_symbols(c,vars);
      
      for (const auto & v : vars)
        if(s.is_input_var(v)) {
          if (e_is_independent_of_v(c, v, all_asmpt)) {
            std::cout << "[simplify_input] try to remove: " << v->to_string() << std::endl;
            std::cout << "[simplify_input] in: " << c->to_string() << std::endl;
            // now we should simplify
            c = remove_independent_var(c, v, all_asmpt, solver);
          }
      } // end of for each var
    } // end of for each c in conds
  } // simplify_inputvar_foreach_constraint

  bool check_contains_inputvar() const {
    auto varset = get_syntactically_contained_input_vars();
    auto actual_varset = get_semantically_contained_input_vars();
    for (const auto & v : varset) {
      bool reduced = (actual_varset.find(v) == actual_varset.end());
      std::cout <<"[check] WARNING! structurally contains inputvar:" << v->to_string() 
                << (reduced ?  " (reducible)." : " *not* reducible")
                << std::endl;
    }
    bool noinputv = varset.empty();

    varset = get_syntactically_contained_next_input_vars();
    actual_varset = get_semantically_contained_next_input_vars();
    for (const auto & v : varset) {
      bool reduced = (actual_varset.find(v) == actual_varset.end());
      std::cout <<"[check] ERROR! structurally contains *next* inputvar:" << v->to_string() 
                << (reduced ?  " (reducible)." : " *not* reducible")
                << std::endl;
    }

    return (noinputv && varset.empty());
  }




  // ----------------------------------------------------------------------------

  bool syntactically_contains_input_vars() const {
    for (const auto & c : conds) {
      smt::UnorderedTermSet vars;
      get_free_symbols(c,vars);
      for (const auto & v : vars)
        if(s.is_input_var(v))
          return true;
    }
    return false;
  }

  smt::UnorderedTermSet get_syntactically_contained_input_vars() const {
    smt::UnorderedTermSet inputvars;
    for (const auto & c : conds) {
      smt::UnorderedTermSet vars;
      get_free_symbols(c,vars);
      for (const auto & v : vars)
        if(s.is_input_var(v))
          inputvars.insert(v);
    }
    return inputvars;
  }

  smt::UnorderedTermSet get_syntactically_contained_next_input_vars() const {
    smt::UnorderedTermSet nxt_inputvars;
    for (const auto & c : conds) {
      smt::UnorderedTermSet vars;
      get_free_symbols(c,vars);
      for (const auto & v : vars)
        if(s.is_next_input_var(v))
          nxt_inputvars.insert(v);
    }
    return nxt_inputvars;
  }

  smt::UnorderedTermSet get_semantically_contained_input_vars() const {
    smt::UnorderedTermSet remaining_vars;
    for (const auto & c : conds) {
      smt::UnorderedTermSet vars;
      get_free_symbols(c,vars);
      
      for (const auto & v : vars)
        if(s.is_input_var(v)) {
          if (!e_is_independent_of_v(c, v, conds))
            remaining_vars.insert(v);
          std::cout << "[syntactically contain input] "<< v->to_string() << std::endl;
        }
    }
    return remaining_vars;
  }

  smt::UnorderedTermSet get_semantically_contained_next_input_vars() const {
    smt::UnorderedTermSet remaining_vars;
    for (const auto & c : conds) {
      smt::UnorderedTermSet vars;
      get_free_symbols(c,vars);
      
      for (const auto & v : vars)
        if(s.is_next_input_var(v)) {
          if (!e_is_independent_of_v(c, v, conds))
            remaining_vars.insert(v);
          std::cout << "[syntactically contain next input] "<< v->to_string() << std::endl;
        }
    }
    return remaining_vars;
  }

  // check if t is valid under conds /\ assumptions
  bool check(const smt::Term & t, const smt::TermVec & assumptions) {
    auto & solver = s.get_solver();
    solver->push();
    for (const auto & a: conds)
      solver->assert_formula(a);
    for (const auto & a: assumptions)
      solver->assert_formula(a);
    solver->assert_formula(solver->make_term(smt::Not, t));
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

} // namespace wasim
