

#include "term_manip.h"
#include "state_simplify.h"
#include "sygus_simplify.h"
#include "config/testpath.h"
#include "utils/exceptions.h"
#include "utils/subprocess.h"
#include "frontend/smt_in.h"
#include "framework/independence_check.h"

#include "smt-switch/smt.h"
#include "smt-switch/utils.h"
#include "smt-switch/boolector_factory.h"
#include "smt-switch/cvc5_factory.h"

#include <fstream>
#include <iostream>
#include <string>


namespace wasim {

using parsed_info = std::tuple<smt::UnorderedTermSet, // vars in expression
                               smt::UnorderedTermSet, // vars in assumption
                               smt::Term,             // conjunction of all assumptions
                               smt::Term,             // the expression to simplify
                               std::string>;          // sort string of the expression

static smt::Term quantify_away(const smt::Term & t, const smt::Term & var, const smt::TermVec & asmpts, smt::SmtSolver & solver) ;

static void get_parent_chains_of_var(const smt::Term & expr, const smt::Term & var, std::vector<smt::TermVec> & parent_chains)
{
  std::vector<std::tuple<smt::Term, int, bool> > stack;
  smt::UnorderedTermSet visited_terms;
  stack.push_back({expr, -1, false}); // <node, parent index, visited>
  
  while(!stack.empty()) {
    auto & [current, parentId, visited] = stack.back();
    if (visited) {
      if (!current->is_symbol()) // should not add symbol to visited
        visited_terms.insert(current); // o.w. will miss the multi occurrence of the same var
      stack.pop_back();
      continue;
    } // else
    if (visited_terms.find(current) != visited_terms.end()) {
      stack.pop_back();
      continue;
    } // else

    visited = true;
    if(current->is_symbolic_const()) {
      if (current == var) {
        // TODO: record the parent chain
        smt::TermVec parent_chain;
        parent_chain.push_back(current);

        int par_id = parentId;
        while(par_id > 0) {
          parent_chain.push_back(std::get<0>(stack.at(par_id)));
          par_id = std::get<1>(stack.at(par_id));
        }
        parent_chains.push_back(std::move(parent_chain));
      }
    } else {
      if (current->is_value()) // this guard is necessary
        continue;              // because a value may still has its child in Boolector
      int idx = stack.size()-1;
      for (auto subterm_ : current) {
        if (subterm_->is_value())
          continue;
        stack.push_back(std::tuple<smt::Term, int, bool>(subterm_, idx, false));
      }
    }
  } // end of while (traverse)
} // end of get_parent_chains_of_var

static smt::Term try_simplify_strategies(const smt::Term & ret_expr, const smt::Term & t, const smt::Term & var, const smt::TermVec & asmpts, smt::SmtSolver & solver)
{
  { // strategy 1 : check if constant
    auto cnst = check_if_constant(t, asmpts, solver);
    if (cnst) { // if it is a constant
      std::cout << "[STRATEGY] tied to constant" << std::endl;
      return replacement_and_constant_propagation(ret_expr, {{t, cnst}}, solver);
    } // if it is not a constant
  } // end of strategy 1
  { // strategy 2 : sygus simplification
    // then we need to invoke SyGuS rewriting
    auto simplified_term = sygus_simplify(t, var, asmpts, solver);
    if (simplified_term) { // sygus succeeded
      return replacement_and_constant_propagation(ret_expr, {{t,simplified_term }}, solver);
    } // else: continue with other methods
  } // end of strategy 2
  { // strategy 3 : enumeration
    if ( (var->get_sort()->get_sort_kind() == smt::BOOL ||
        (var->get_sort()->get_sort_kind() == smt::BV &&
            var->get_sort()->get_width() <= 4  ))  // 2-bit var is also okay
        ) {
      smt::TermVec related_asmpts;
      bool res = get_unsatcore_for_e_is_independent_of_v(t, var, asmpts, related_asmpts);
      assert(res);
      std::cout << "[remove var] try to quantify v: " << var->to_string() << std::endl;
      auto reduced_form = quantify_away(t, var, related_asmpts, solver);
      std::cout << "--- BEFORE: " << t->to_string() << std::endl;
      std::cout << "--- AFTER: " << reduced_form->to_string() << std::endl;
      std::cout << "[STRATEGY] Quantified." << std::endl;
      return replacement_and_constant_propagation(ret_expr, {{t, reduced_form}}, solver);
    }
  } // end strategy 3
  // if we arrive at this place, we are running out of methods...
  // :-( Bad luck
  throw SimulatorException("Cannot eliminate var: " + var->to_string());
  return nullptr;
} // end of try_simplify_strategies


smt::Term remove_independent_var(
    const smt::Term & expr_in, 
    const smt::Term & var,
    const smt::TermVec & asmpts,
    smt::SmtSolver & solver) {
  // traverse the expr from bottom up, for subterm containing var, 
  //  - build a vector of subterm, from v to this parent.
  //  - there could be multiple occurrence of v

  // rewrite from smallest term to largest
  // rewrite immediately, instead of having a map
  auto modified_expr = expr_in;
  do {
    std::vector<smt::TermVec> parent_chains;
    get_parent_chains_of_var(modified_expr, var, parent_chains);
    std::cout << "[DEBUG] #. parent chains: " << parent_chains.size() << "\n";
    if (parent_chains.empty()) {
      // vars have been removed;
      break;
    }

    // for each chain, find its proper parent, to build
    // substition map
    int min_depth = -1;

    smt::Term subterm_of_this_round;
    for (const auto & chain : parent_chains) {
      // for each chain, try to find a term that is independent of 
      bool found = false;
      bool skipped_this_chain = false;
      assert(chain.size());
      for (size_t idx = 0; idx < chain.size(); ++idx) {
        const auto & t = chain.at(idx);

        auto t_depth = term_level(t);
        if (min_depth > 0 && min_depth < t_depth) {
          // this is already larger than what we found, 
          // skipped this chain altogether
          skipped_this_chain = true;
          break;
        }

        if (e_is_independent_of_v(t, var, asmpts)) {
          found = true;
          // maintain min_depth
          if (min_depth == -1)
            min_depth = t_depth;

          if (t->get_op().prim_op == smt::Ite) {
            smt::TermVec children(t->begin(), t->end());
            assert(idx > 0);
            const auto & prev_term = chain.at(idx-1);
            if (children.at(0) != prev_term) {
              auto cnst = check_if_constant(children.at(0), asmpts, solver);
              if (cnst) {
                auto val = cnst->to_string();
                if ( (val == "#b1" || val == "true" || val == "(_ bv1 1)") && (prev_term !=children.at(1) )) {
                  subterm_of_this_round = children.at(0);
                  // std::cout << "[WARNING] usually this should not happen. because simplify_ite is used first.\n";
                  throw SimulatorException("[WARNING] usually this should not happen. because simplify_ite is used first.");
                  break;
                } else if ( (val == "#b0" || val == "false" || val == "(_ bv0 1)") && (prev_term !=children.at(2) )) {
                  subterm_of_this_round = children.at(0);
                  // std::cout << "[WARNING] usually this should not happen. because simplify_ite is used first.\n";
                  throw SimulatorException("[WARNING] usually this should not happen. because simplify_ite is used first.");
                  break;       
                }
              } else {
                std::cout << "ITE is independent, but its COND is not!\n" ;
                std::cout << "[WARNING] very likely SyGuS rewriting will fail!\n";
              }
            }
          }
          subterm_of_this_round = t;
          break;
        }
      } // for each element in chain
      if (skipped_this_chain) {
        assert(parent_chains.size() > 1);
        continue; // go to next chain and see if there are smaller terms
      }

      if (!found)
        throw SimulatorException("Cannot eliminate var: " + var->to_string() );
    } // for each chain

    // at this point, we know the term in subterm_of_this_round is reducible,
    // then we can try different strategies
    modified_expr = try_simplify_strategies(modified_expr, subterm_of_this_round, var, asmpts, solver);

  } while(true);
  return modified_expr; 
} // end of remove_independent_var

static smt::Term smart_and(const smt::TermVec & asmpts, smt::SmtSolver & solver) {
  if (asmpts.empty())
    return solver->make_term(true);
  if (asmpts.size() == 1)
    return asmpts.at(0);
  return solver->make_term(smt::And, asmpts);
} // end of smart_and

static smt::Term build_ite(const smt::TermVec & conds, const smt::TermVec & choices, smt::SmtSolver & solver) {
  assert(choices.size()); // non-empty
  assert(conds.size() == choices.size());

  if (choices.size() == 1)
    return choices.at(0);
  auto ret = choices.back(); // the last element
  for (int ptr = conds.size() - 2; ptr >= 0; --ptr) {
    const auto & if_branch = choices.at(ptr);
    ret = solver->make_term(smt::Ite, conds.at(ptr), if_branch, ret);
  }
  return ret;
}

static smt::Term quantify_away(const smt::Term & t, const smt::Term & var, const smt::TermVec & asmpts, smt::SmtSolver & solver) {
  // ((asmpts | var = 0) : a1 => t1 | var = 0
  // ((asmpts | var = 1) : a2 => t2 | var = 1
  // check if (asmpts /\ not(a1) /\ not(a2) ) is sat?
  std::cout << "[DEBUG] quantify_away " << std::endl;
  for (const auto & a : asmpts) {
    std::cout << "[DEBUG] asmpt: " << a->to_string() << std::endl;
  }
  auto asmpt_all = smart_and(asmpts, solver);
  smt::TermVec asmpt_under_diff_val;
  smt::TermVec t_under_diff_val;
  if (var->get_sort()->get_sort_kind() == smt::BOOL) {
    auto T = solver->make_term(true);
    auto F = solver->make_term(false);
    asmpt_under_diff_val.push_back(replacement_and_constant_propagation(asmpt_all, { {var, T} }, solver));
    asmpt_under_diff_val.push_back(replacement_and_constant_propagation(asmpt_all, { {var, F} }, solver));
    t_under_diff_val.push_back(replacement_and_constant_propagation(t, { {var, T} }, solver));
    t_under_diff_val.push_back(replacement_and_constant_propagation(t, { {var, F} }, solver));
  } else {
    // enum BV values
    auto bvsort = var->get_sort();
    auto width = bvsort->get_width();
    auto uplimit = 1ULL << width;
    for (int val = 0 ; val < uplimit; ++ val) {
      auto term_val = solver->make_term(val, bvsort);
      asmpt_under_diff_val.push_back(replacement_and_constant_propagation(asmpt_all, { {var, term_val} }, solver));
      t_under_diff_val.push_back(replacement_and_constant_propagation(t, { {var, term_val} }, solver));
    }
  }
  // check asmpt_under_diff_val is complete under the assumptions
  solver->push();
  solver->assert_formula(asmpt_all);
  for(const auto & a : asmpt_under_diff_val)
    solver->assert_formula(solver->make_term(smt::Not, a));
  auto res = solver->check_sat();
  solver->pop();
  assert(res.is_unsat());
  auto ret = build_ite(asmpt_under_diff_val, t_under_diff_val, solver);
  return replacement_and_constant_propagation(ret, {}, solver);
} // end of quantify_away

// note: the last element in conds will be ignored
static smt::Term rebuild_ite(const smt::Term & var, const smt::TermVec & conds, const smt::TermVec & choices, smt::SmtSolver & solver) {
  assert(choices.size()); // non-empty
  assert(conds.size() == choices.size());

  if (choices.size() == 1)
    return choices.at(0);
  auto ret = choices.back(); // the last element
  for (int ptr = conds.size() - 2; ptr >= 0; --ptr) {
    const auto & if_branch = choices.at(ptr);
    const auto & val = conds.at(ptr);
    ret = solver->make_term(smt::Ite,
      solver->make_term(smt::Equal, var, val),
      if_branch, ret);
  }
  return ret;
} // end of rebuild_ite

// find the (ite x == 1, ite , ite ...)
static smt::Term try_fullcase_remove_default(const smt::Term & t, smt::SmtSolver & solver) {
#define MISMATCH  { mismatch = true; break;  } 
  if (t->get_op().prim_op != smt::Ite)
    return t;
  // peel the layered ite
  bool mismatch = false;
  smt::Term eq_term;
  smt::TermVec eq_consts;
  smt::TermVec choices;
  auto current = t;
  while(current->get_op().prim_op == smt::Ite) {
    auto child_pos = current->begin();
    auto cond = *child_pos;
    if (cond->get_op().prim_op != smt::Equal) MISMATCH
    // from this point on, it should be equal
    smt::TermVec eq_child(cond->begin(),cond->end());
    if (eq_child.size() != 2) MISMATCH
    if (! (eq_child.at(0)->is_value()) && ! (eq_child.at(1)->is_value())) MISMATCH
    if (eq_child.at(0)->is_value()) {
      auto eq_term_new = eq_child.at(1);
      if (eq_term != nullptr && eq_term != eq_term_new) MISMATCH
      if (eq_term == nullptr)
        eq_term = eq_term_new;
      eq_consts.push_back(eq_child.at(0));
    } else { // eq_child.at(1)->is_value()
      auto eq_term_new = eq_child.at(0);
      if (eq_term != nullptr && eq_term != eq_term_new) MISMATCH
      if (eq_term == nullptr)
        eq_term = eq_term_new;
      eq_consts.push_back(eq_child.at(1));
    }
    ++child_pos; // then-branch
    choices.push_back(*child_pos);

    ++child_pos; // else-branch
    current = *child_pos;
  } // end of peel layered ITE
  if (mismatch)
    return t;
  auto term_sort = eq_term->get_sort();
  if (term_sort->get_sort_kind() != smt::SortKind::BV)
    return t; // not handled
  auto elem = 1ULL << (term_sort->get_width());
  if (eq_consts.size() != elem)
    return t; // not full case
  std::vector<bool> all_value_exists(elem, false);
  for (const auto & c : eq_consts) {
    auto val = c->to_int();
    if (val >= elem)
      return t;
    all_value_exists.at(val) = true;
  }
  for (const auto exists : all_value_exists)
    if (!exists)
      return t; // not fully covered
  // now we are sure, all cases are covered
  // so we can rebuild ITE
  return rebuild_ite(eq_term, eq_consts, choices, solver);
#undef MISMATCH
}

smt::Term sygus_simplify(const smt::Term & t, const smt::Term & var_to_remove,
                         const smt::TermVec & asmpts, smt::SmtSolver & solver) {

  smt::SmtSolver solver_cvc5 = smt::Cvc5SolverFactory::create(false);
  solver_cvc5->set_logic("QF_BV");
  // solver_cvc5->set_opt("produce-models", "false");
  // solver_cvc5->set_opt("incremental", "false");
  smt::TermTranslator btor2cvc(solver_cvc5);
  smt::TermTranslator cvc2btor(solver);

  smt::TermVec assmpt_in_cvc;
  for (const auto & a : asmpts)
    assmpt_in_cvc.push_back(btor2cvc.transfer_term(a, smt::SortKind::BOOL));

  smt::Term t_in_cvc = btor2cvc.transfer_term(t);
  smt::Term var_in_cvc = btor2cvc.transfer_term(var_to_remove);

  { // lets first try some strategies
    if(t_in_cvc->get_op().prim_op == smt::Ite) {
      auto ret = try_fullcase_remove_default(t_in_cvc, solver_cvc5);
      smt::UnorderedTermSet vars;
      smt::get_free_symbols(ret, vars);
      if (vars.find(var_in_cvc) == vars.end() ) {
        std::cout << "[STRATEGY] ITE full case removable" << std::endl;
        // if succcefully removed
        return cvc2btor.transfer_term(ret, false);
      }
    }
  } // end of strategies

  auto time_stamp = GetTimeStamp();
  
  auto template_file = "sygus_template_" + time_stamp + ".sygus";
  auto bash_file = "sygus_" + time_stamp + ".sh";
  auto result_file = "sygus_result_" + time_stamp + ".sygus";
  auto result_temp_file = "sygus_result_temp_" + time_stamp + ".sygus";

  { // collect SyGu-Synth dump
    auto asmpt_and = assmpt_in_cvc.empty() ? solver_cvc5->make_term(true) :
                     assmpt_in_cvc.size() < 2 ? assmpt_in_cvc.at(0) : solver_cvc5->make_term(smt::And, assmpt_in_cvc);
    smt::UnorderedTermSet free_var_asmpt, free_var;
    smt::get_free_symbols(asmpt_and, free_var_asmpt);
    smt::get_free_symbols(t_in_cvc, free_var);
    auto Fun_type = t_in_cvc->get_sort()->to_string();
    const smt::Term & Fun = t_in_cvc;
    // dump all files and run
    { // dump template file
      std::ofstream f(template_file);
      f << "(set-logic BV)\n\n\n(synth-fun FunNew \n   (" << endl;

      for (const auto & v_in_fun : free_var) {
        if (v_in_fun != var_in_cvc) {
          auto vdecl = "    (" + v_in_fun->to_string() + " "
                       + v_in_fun->get_sort()->to_string() + " )";
          f << vdecl << endl;          
        }
      } // end of v_in_fun declaration

      f << "   )\n   " << Fun_type << "\n  )\n\n\n" << endl;

      for (const auto & v_in_asmpt : free_var_asmpt) {
        auto vdecl = "(declare-var " + v_in_asmpt->to_string() + " "
                     + v_in_asmpt->get_sort()->to_string() + ")";
        f << vdecl << endl;
      } // end of v_in_asmpt

      for (const auto & v_in_fun : free_var) {
        if (free_var_asmpt.find(v_in_fun) == free_var_asmpt.end()) {
          auto vdecl = "(declare-var " + v_in_fun->to_string() + " "
                       + v_in_fun->get_sort()->to_string() + ")";
          f << vdecl << endl;
        }
      } // end of remaining declaration

      f << "\n(constraint (=> " << endl;
      f << "    " << asmpt_and->to_string() << " ;\n\n    (=" << endl;
      f << "        " << Fun->to_string() << " ;\n        (FunNew ";

      for (const auto & v_in_fun : free_var) {
        if (v_in_fun != var_in_cvc) {
          auto line8 = v_in_fun->to_string() + " ";
          f << line8;
        }
      }
      f << ") ;\n    )))\n\n\n;\n\n(check-synth)" << endl;
    } // end of template writing
    { // write bash script
      std::ofstream bash_f(bash_file);

      bash_f <<  "#!/bin/bash" << endl;
      auto bash_line2 = (PROJECT_SOURCE_DIR "/deps/smt-switch/deps/cvc5-Linux-static/bin/cvc5 --lang=sygus2 ") 
                        + template_file
                        + " > " + result_temp_file;
      bash_f << bash_line2 << endl;
    } // finish writing bash script

    auto cmd = "chmod +x " + bash_file;
    system(cmd.c_str());
    run_cmd("./" + bash_file, 1000);
  } // end of dump SyGuS templates
  { // load sygus output
    // only move the second line of sygus output file to a new file

    std::string linedata;
    { // read the result file
      std::ifstream infile(result_temp_file);
      getline(infile, linedata);  // get first line, and do nothing
      getline(infile, linedata);  // get second line
    }
    if (linedata.empty()) {
      std::cout << "SyGuS rewriting failed!" << std::endl;
      return nullptr;
    }

    { // dump to the final result file
      std::ofstream outfile(result_file);
      outfile << linedata << endl;
    }
    std::cout << "[STRATEGY] SyGuS rewritable." << std::endl;
    auto new_expr = load_smt_fundef(result_file, solver_cvc5);
    return cvc2btor.transfer_term(new_expr);
  } // end of loading SyGuS result
} // end of sygus_simplify



static parsed_info parse_state(const smt::TermVec & asmpt, const smt::Term & v, const smt::SmtSolver & solver)
{
  auto asmpt_and = solver->make_term(smt::And, asmpt);
  smt::UnorderedTermSet free_var_asmpt;
  smt::get_free_symbols(asmpt_and, free_var_asmpt);
  smt::UnorderedTermSet free_var;
  smt::get_free_symbols(v, free_var);
  auto Fun_type = v->get_sort()->to_string();
  return std::make_tuple(free_var, free_var_asmpt, asmpt_and, v, Fun_type);
}

smt::Term run_sygus(const parsed_info & info,
                    const smt::UnorderedTermSet & set_of_xvar,
                    const smt::SmtSolver & solver)
{
  const smt::UnorderedTermSet & free_var = std::get<0>(info);
  const smt::UnorderedTermSet & free_var_asmpt = std::get<1>(info);
  const smt::Term & asmpt_and = std::get<2>(info);
  const smt::Term & Fun = std::get<3>(info);
  const std::string & Fun_type = std::get<4>(info);
  auto time_stamp = GetTimeStamp();
  auto template_file = "sygus_template_" + time_stamp + ".sygus";
  auto result_file = "sygus_result_" + time_stamp + ".sygus";
  auto result_temp_file = "sygus_result_temp_" + time_stamp + ".sygus";
  auto bash_file = "sygus_" + time_stamp + ".sh";

  std::ofstream f;

  f.open(template_file.c_str(), ios::out | ios::app);
  auto line1 = "(set-logic BV)\n\n\n(synth-fun FunNew \n   (";
  f << line1 << endl;

  for (const auto & var : free_var) {
    if (set_of_xvar.find(var) == set_of_xvar.end()) {
      auto line2 = "    (" + var->to_string() + " "
                   + var->get_sort()->to_string() + " )";
      f << line2 << endl;
    }
  }

  auto line3 = "   )\n   " + Fun_type + "\n  )\n\n\n";
  f << line3 << endl;

  for (const auto & var : free_var_asmpt) {
    auto line4 = "(declare-var " + var->to_string() + " "
                 + var->get_sort()->to_string() + ")";
    f << line4 << endl;
  }

  for (const auto & var : free_var) {
    if (free_var_asmpt.find(var) == free_var_asmpt.end()) {
      auto line4 = "(declare-var " + var->to_string() + " "
                   + var->get_sort()->to_string() + ")";
      f << line4 << endl;
    }
  }

  auto line5 = "\n(constraint (=> ";
  f << line5 << endl;

  auto line6 = "    " + asmpt_and->to_string() + " ;\n\n    (=";
  f << line6 << endl;

  auto line7 = "        " + Fun->to_string() + " ;\n        (FunNew ";
  f << line7;

  for (const auto & var : free_var) {
    if (set_of_xvar.find(var) == set_of_xvar.end()) {
      auto line8 = var->to_string() + " ";
      f << line8;
    }
  }

  auto line9 = ") ;\n    )))\n\n\n;\n\n(check-synth)";
  f << line9 << endl;
  f.close();

  std::ofstream bash_f;

  bash_f.open(bash_file.c_str(), ios::out | ios::app);
  auto bash_line1 = "#!/bin/bash";
  bash_f << bash_line1 << endl;
  auto bash_line2 = (PROJECT_SOURCE_DIR "/deps/smt-switch/deps/cvc5/build/bin/cvc5 --lang=sygus2 ") 
                    + template_file
                    + " > " + result_temp_file;
  bash_f << bash_line2 << endl;
  bash_f.close();

  auto cmd = "chmod 755 " + bash_file;
  system(cmd.c_str());
  auto cmd_string = "./" + bash_file;
  run_cmd(cmd_string, 1000);  // 500 milliseconds -> 0.5s
  // timeout table
  // c1 ->- 100ms
  // c2 ->- 100ms
  // c3 ->- 1s

  // only move the second line of sygus output file to a new file
  std::ifstream infile(result_temp_file.c_str());
  std::string linedata = "";

  getline(infile, linedata);  // get first line, and do nothing
  getline(infile, linedata);  // get second line
  infile.close();

  std::ofstream outfile;
  outfile.open(result_file.c_str(), ios::out | ios::app);
  outfile << linedata << endl;
  outfile.close();

  smt::Term new_expr;
  // determine whether the smtlib_result is empty
  if (linedata.empty()) {
    try {
      new_expr = solver->make_symbol("no_file", solver->make_sort(smt::BV, 1));
    }
    catch (const std::exception & e) {
      new_expr = solver->get_symbol("no_file");
    }
  } else {
    auto solver_copy = solver; // TODO: in the future, change SmtLibReader to use const ref.
    new_expr = load_smt_fundef(result_file, solver_copy);
  }
  int rm;
  // rm = remove(template_file.c_str());
  rm = remove(result_file.c_str());
  rm = remove(result_temp_file.c_str());
  rm = remove(bash_file.c_str());

  return new_expr;
} // end of run_sygus


static smt::Term structure_simplify(
                             const smt::Term & v,
                             const smt::TermVec & assumptions,
                             const smt::UnorderedTermSet & set_of_xvar,
                             smt::TermTranslator & translator);

static smt::TermVec child_vec_simplify(
                                const smt::TermVec & child_vec,
                                const smt::TermVec & asmpt,
                                const smt::UnorderedTermSet & set_of_xvar,
                                smt::TermTranslator & translator)
{
  smt::TermVec child_new_vec;
  for (const auto & child : child_vec) {
    if (expr_contains_X(child, set_of_xvar))
      child_new_vec.push_back(
          structure_simplify(child, asmpt, set_of_xvar, translator));
    else 
      child_new_vec.push_back(child);
    
  }
  return child_new_vec;
}

// attempt to hierarchically simplify
static smt::Term structure_simplify(
                             const smt::Term & v,
                             const smt::TermVec & assumptions,
                             const smt::UnorderedTermSet & set_of_xvar,
                             smt::TermTranslator & translator)
{
  smt::Term new_expr;
  auto expr_info = parse_state(assumptions, v, translator.get_solver());
  auto new_expr_direct = run_sygus(expr_info, set_of_xvar, translator.get_solver());
  if (new_expr_direct->to_string() == "no_file") {
    auto child_vec = args(v);
    auto child_new_vec =
        child_vec_simplify(child_vec, assumptions, set_of_xvar, translator);

    const auto & solver_cvc5 = translator.get_solver();
    if ((v->get_op() == smt::Ite) && (child_vec.size() == 3)) {
      new_expr = solver_cvc5->make_term(smt::Ite, child_new_vec);
    } else if ((v->get_op() == smt::BVNot) && (child_vec.size() == 1)) {
      new_expr = solver_cvc5->make_term(smt::BVNot, child_new_vec);
    } else if ((v->get_op() == smt::Not) && (child_vec.size() == 1)) {
      new_expr = solver_cvc5->make_term(smt::Not, child_new_vec);
    } else if ((v->get_op() == smt::BVAnd) && (child_vec.size() == 2)) {
      new_expr = solver_cvc5->make_term(smt::BVAnd, child_new_vec);
    } else if ((v->get_op() == smt::And) && (child_vec.size() == 2)) {
      new_expr = solver_cvc5->make_term(smt::And, child_new_vec);
    } else if ((v->get_op() == smt::BVMul) && (child_vec.size() == 2)) {
      new_expr = solver_cvc5->make_term(smt::BVMul, child_new_vec);
    } else if ((v->get_op() == smt::BVAdd) && (child_vec.size() == 2)) {
      new_expr = solver_cvc5->make_term(smt::BVAdd, child_new_vec);
    } else if ((v->get_op() == smt::Concat) && (child_vec.size() == 2)) {
      new_expr = solver_cvc5->make_term(smt::Concat, child_new_vec);
    } else if ((v->get_op() == smt::Equal) && (child_vec.size() == 2)) {
      new_expr = solver_cvc5->make_term(smt::Equal, child_new_vec);
    }
    // else if
    else {
      throw SimulatorException("new structure of " + v->to_string() + " is not handled");
    }
  } else {
    new_expr = new_expr_direct;
  }

  return new_expr;
} // end of structure_simplify

void sygus_simplify(StateAsmpt & state_btor,
                    const smt::UnorderedTermSet & set_of_xvar_btor,
                    smt::SmtSolver & solver)
{
  smt::SmtSolver solver_cvc5 = smt::Cvc5SolverFactory::create(false);
  solver_cvc5->set_logic("QF_BV");
  solver_cvc5->set_opt("produce-models", "true");
  solver_cvc5->set_opt("incremental", "true");
  smt::TermTranslator btor2cvc(solver_cvc5);
  smt::TermTranslator cvc2btor(solver);

  smt::UnorderedTermSet set_of_xvar_in_cvc;
  smt::TermVec assmpt_in_cvc;

  for (const auto & x : set_of_xvar_btor)
    set_of_xvar_in_cvc.emplace(btor2cvc.transfer_term(x));
  for (const auto & a : state_btor.get_assumptions())
    assmpt_in_cvc.push_back(btor2cvc.transfer_term(a));


  for (const auto & sv : state_btor.get_sv()) {
    const auto & s_btor = sv.first;
    const auto & v_btor = sv.second;

    if (expr_contains_X(v_btor, set_of_xvar_btor)) {
      auto v_cvc = btor2cvc.transfer_term(v_btor);
      auto new_expr =
          structure_simplify(v_cvc, assmpt_in_cvc, set_of_xvar_in_cvc, btor2cvc);
      // cout << "new_expr: " << new_expr->to_string() << endl;
      auto new_expr_btor = cvc2btor.transfer_term(new_expr);
      state_btor.update_sv().insert_or_assign(s_btor, new_expr_btor);
    } // end of if contains X
  } // end of for each sv
} // end of sygus_simplify

}  // namespace wasim