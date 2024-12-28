#pragma once


#include "smt-switch/boolector_factory.h"
#include "smt-switch/utils.h"

#include "framework/ts.h"
#include "framework/independence_check.h"

namespace wasim {

smt::Term _Eq(const smt::Term & l, int r, smt::SmtSolver & s) {
  const auto & sort = l->get_sort();
  auto rterm = s->make_term(r, sort);
  return s->make_term(smt::Equal, l, rterm);
}

smt::Term _Eq(const smt::Term & l, const smt::Term & r, smt::SmtSolver & s) {
  return s->make_term(smt::Equal, l, r);
}

smt::Term _And(const smt::Term & l, const smt::Term & r, smt::SmtSolver & s) {
  return s->make_term(smt::And, l, r);
}

smt::Term _Add(const smt::Term & l, int r, smt::SmtSolver & s) {
  const auto & sort = l->get_sort();
  auto rterm = s->make_term(r, sort);
  return s->make_term(smt::BVAdd, l, rterm);
}

smt::Term _Add(const smt::Term & l, const smt::Term & r, smt::SmtSolver & s) {
  return s->make_term(smt::BVAdd, l, r);
}

smt::Term _Ite(const smt::Term & c, const smt::Term & l, const smt::Term & r, smt::SmtSolver & s) {
  return s->make_term(smt::Ite, c, l, r);
}

smt::Term _Sel(const smt::Term & l, unsigned r1, unsigned r2, smt::SmtSolver & s) {
  return s->make_term(smt::Op(smt::Extract, r1, r2),  l);
}

smt::TermVec _Collect(const std::string & name, const std::string & l, const std::string & r, const TransitionSystem & sts) {
  smt::TermVec ret;
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

smt::Term _Sv(const std::string & name, const TransitionSystem & sts) {
  return sts.lookup(name);
}

smt::Term _Read(const smt::TermVec & vec, const smt::Term & idx, smt::SmtSolver & s) {
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

smt::UnorderedTermSet get_semantically_contained_input_vars(const smt::Term & t, const smt::TermVec & asmpts, const TransitionSystem & sts) {
  smt::UnorderedTermSet remaining_vars;
  smt::UnorderedTermSet vars;
  smt::get_free_symbols(t,vars);
    
    for (const auto & v : vars)
      if(sts.is_input_var(v))
        if (!e_is_independent_of_v(t, v, asmpts))
          remaining_vars.insert(v);
  return remaining_vars;
}

smt::UnorderedTermSet get_semantically_contained_next_input_vars(const smt::Term & t, const smt::TermVec & asmpts, const TransitionSystem & sts) {
  smt::UnorderedTermSet remaining_vars;
  smt::UnorderedTermSet vars;
  smt::get_free_symbols(t,vars);
    
    for (const auto & v : vars)
      if(sts.is_next_input_var(v))
        if (!e_is_independent_of_v(t, v, asmpts))
          remaining_vars.insert(v);
  return remaining_vars;
}

} // namespace wasim
