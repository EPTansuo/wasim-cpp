#include <iostream>
#include <unordered_map>
#include <vector>
#include <memory>
#include <smt-switch/smt.h>
#include "apps/debug.h"
#include "smt-switch/cvc5_factory.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/term.h"
using namespace smt;


class TransitionSystem
{
public:
    TransitionSystem(const std::vector<Term> &variables,
                     const Term &init,
                     const Term &trans)
        : variables_(variables), init_(init), trans_(trans) {}

    const std::vector<Term> &variables() const { return variables_; }
    const Term &init() const { return init_; }
    const Term &trans() const { return trans_; }
    const std::string to_string(){
        std::string s;
        s += "------ Variables --------\n";
        for (auto &v : variables_){
            s += v->to_string() + "\n";
        }
        s += "--------- Init ----------\n";
        s += init_->to_string() + "\n";
        s += "-------- Trans ----------\n";
        s += trans_->to_string() + "\n";
        return s;
    }
private:
    std::vector<Term> variables_;
    Term init_;
    Term trans_;
};


// std::unordered_map<std::string, smt::Term> named_terms_;
std::unordered_set<std::string> term_names;
Term next_var(SmtSolver& solver_, const Term &var){
    auto next_var_name = "next(" + var->to_string() + ")";
    // if(named_terms_.find(next_var_name) != named_terms_.end()){
    //     return named_terms_.at(next_var_name);
    // }
    if(term_names.find(next_var_name) != term_names.end()){
        return solver_->get_symbol(next_var_name);
    }
    auto next_var = solver_->make_symbol(next_var_name, var->get_sort());
    // named_terms_.insert({next_var_name, next_var});
    term_names.insert(next_var_name);
    return next_var;
}

Term at_time(SmtSolver& solver_, const Term &var, int t)
{
    auto at_time_name = var->to_string() + "@" + std::to_string(t);
    // if(named_terms_.find(at_time_name) != named_terms_.end()){
    //     return named_terms_.at(at_time_name);
    // }
    if(term_names.find(at_time_name) != term_names.end()){
        return solver_->get_symbol(at_time_name);
    }
    auto at_time = solver_->make_symbol(at_time_name, var->get_sort());
    // named_terms_.insert({at_time_name, at_time});
    term_names.insert(at_time_name);
    return at_time;
}

class BMC
{
public:
    BMC(const TransitionSystem &system, SmtSolver& solver)
        : system_(system), solver_(solver)
    {
        solver_->set_logic("QF_UFBV");
        solver_->set_opt("incremental", "true");
        solver_->set_opt("produce-models", "true");
        solver_->set_opt("produce-unsat-assumptions", "true");
    }

    bool check_property(const Term &prop, int bound)
    {
        std::cout << "Checking property " << prop << "..." << std::endl;

        for (int k = 0; k < bound; ++k)
        {
            Term bmc_formula = get_bmc(prop, k);
            std::cout << "   [BMC] Checking bound " << k << std::endl;
            if (check_sat(bmc_formula))
            {
                std::cout << "--> Bug found at step " << k << std::endl;
                // named_terms_.clear();
                return true;
            }
        }
        return false;
    }

private:
    Term get_bmc(const Term &prop, int k)
    {
        Term init_0 = substitute_time(system_.init(), 0);
        // LOG_DEBUG("init_0: {}", init_0->to_string());
        Term trans_unroll = unroll_trans(k);
        // LOG_DEBUG("trans_unroll: {}", trans_unroll->to_string());
        Term prop_k = substitute_time(prop, k);
        // LOG_DEBUG("prop_k: {}", prop_k->to_string());
        return solver_->make_term(And, init_0, trans_unroll, solver_->make_term(Not, prop_k));
    }


    Term substitute_time(const Term &term, int t)
    {
        UnorderedTermMap subs;
        // LOG_DEBUG("t={}", t);
        for (const auto &v : system_.variables())
        {
            // LOG_DEBUG("v={}", v->to_string());
            subs[v] = at_time(solver_,v, t);
            subs[next_var(solver_,v)] = at_time(solver_, v, t + 1);
        }
        return solver_->substitute(term, subs);
    }

    Term unroll_trans(int k)
    {
        TermVec conjuncts;
        for (int i = 0; i <= k; ++i)
        {
            conjuncts.push_back(substitute_time(system_.trans(), i));
        }
        if(conjuncts.size() == 0){
            return solver_->make_term(true);
        }
        else if(conjuncts.size() == 1){
            return conjuncts[0];
        }
        return solver_->make_term(And, conjuncts);
    }


    bool check_sat(const Term &formula)
    {
        solver_->push();
        solver_->assert_formula(formula);
        // LOG_DEBUG("formula:{}", formula->to_string());
        Result r = solver_->check_sat();
        solver_->pop();
        return r.is_sat();
    }


    TransitionSystem system_;
    SmtSolver solver_;
    
    
};


std::pair<TransitionSystem, std::vector<Term>> counter_example(SmtSolver &solver)
{
    // SmtSolver solver = Cvc5SolverFactory::create(false);
    Sort bv4 = solver->make_sort(BV, 4);
    Term bits = solver->make_symbol("bits", bv4);
    Term reset = solver->make_symbol("reset", solver->make_sort(BOOL));
    // named_terms_.insert({"bits", bits});
    // named_terms_.insert({"reset", reset});
    term_names.insert("bits");
    term_names.insert("reset");
    // Initial: bits == 0 && !reset
    Term init = solver->make_term(And,
        solver->make_term(Equal, bits, solver->make_term(0, bv4)),
        solver->make_term(Not, reset));

    // Transition: next(bits) = bits + 1, next(reset) -> (next(bits) == 0)

    auto next_reset = solver->make_symbol("next(" + reset->to_string() + ")", reset->get_sort());
    // named_terms_.insert({"next(reset)", next_reset});
    term_names.insert("next(reset)");
    auto next_bits = solver->make_symbol("next(" + bits->to_string() + ")", bits->get_sort());
    // named_terms_.insert({"next(bits)", next_bits});
    term_names.insert("next(bits)");
    Term bits_add = solver->make_term(BVAdd, bits, solver->make_term(1, bv4));
    Term trans = solver->make_term(And,
        solver->make_term(Equal, next_bits, bits_add),
        solver->make_term(Equal, next_reset, solver->make_term(Equal, 
                            next_bits,
                             solver->make_term(
                            0, bv4))));

    // Properties
    Term true_prop = solver->make_term(Implies, reset, solver->make_term(Equal, bits, solver->make_term(0, bv4)));
    Term false_prop = solver->make_term(Not, solver->make_term(Equal, bits, solver->make_term(10, bv4)));

    return {TransitionSystem({bits, reset}, init, trans), {true_prop, false_prop}};
}

int main()
{
    SmtSolver solver = Cvc5SolverFactory::create(false);
    auto example = counter_example(solver);
    BMC bmc(example.first, solver);
    LOG_DEBUG("sts:\n{}", example.first.to_string());
    LOG_DEBUG("true_prop:{}", example.second[0]->to_string());
    LOG_DEBUG("false_prop:{}", example.second[1]->to_string());


    for (const auto &prop : example.second)
    {
        bmc.check_property(prop,20);
        std::cout << std::endl;
    }

    return 0;
}