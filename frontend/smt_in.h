#pragma once
#include "smt-switch/smt.h"

namespace wasim {

smt::Term load_smt_fundef(const std::string & filename, smt::SmtSolver & solver);

} // end of namespace wasim

