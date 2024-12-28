#pragma once

#include "tracemgr.h"
#include "ts.h"


using namespace std;

namespace wasim {

// will attempt to simplify (remove the variable)
// it is better if you can first use independence check to find if it is removable
//   e.g., state_simplify.h / get_xvar_independent

smt::Term remove_independent_var(
    const smt::Term & expr, 
    const smt::Term & var,
    const smt::TermVec & asmpts,
    smt::SmtSolver & solver);

// call sygus to try removing var_to_remove from t
// it is better not to directly use it
// (use remove_independent_var instead)
smt::Term sygus_simplify(const smt::Term & t, const smt::Term & var_to_remove,
                         const smt::TermVec & asmpts, smt::SmtSolver & solver);

// attempt to simplify the variable assigments in state_btor
// assuming all expressions in state_btor are in solver btor
// will create a CVC solver inside and do the translation
void sygus_simplify(StateAsmpt & state_btor,
                    const smt::UnorderedTermSet & set_of_xvar_btor,
                    smt::SmtSolver & solver);

}  // namespace wasim