/*********************                                                        */
/*! \file
 ** \verbatim
 ** Top contributors (to current version):
 **   Ahmed Irfan, Makai Mann, Florian Lonsing
 ** This file is part of the pono project.
 ** Copyright (c) 2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file LICENSE in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief
 **
 **
 **/

#include "modelchecking/prover.h"

#include <cassert>
#include <climits>
#include <functional>

#include "utils/logger.h"

using namespace smt;
using namespace std;

namespace pono {

Prover::Prover(const smt::Term & p,
               const TransitionSystem & ts,
               const smt::SmtSolver & s)
    : initialized_(false),
      solver_(s),
      property_(p),
      ts_(ts),
      bad_(solver_->make_term(
          smt::PrimOp::Not, p))
{
}

Prover::~Prover() {}

void Prover::initialize()
{
  if (initialized_)
    return;
  reached_k_ = -1;
  if (!ts_.only_curr(bad_))
    throw PonoException("Property should not contain inputs or next state variables");
  initialized_ = true;
}

ProverResult Prover::prove()
{
  return check_until(INT_MAX);
}


size_t Prover::witness_length() const { return reached_k_ + 1; }

Term Prover::invar()
{
  if (!invar_)
  {
    throw WasimException("Failed to return invar. Be sure that the property was proven "
                        "by an engine the supports returning invariants.");
  }
  return invar_;
}

}  // namespace pono
