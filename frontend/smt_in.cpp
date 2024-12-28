#include <frontend/smt_in.h>
#include <utils/exceptions.h>

#include "smt-switch/smtlib_reader.h"

namespace wasim
{
  
class WasimSmtLib2Parser : public smt::SmtLibReader
{
 public:
  WasimSmtLib2Parser(const std::string & filename, smt::SmtSolver & solver);

  typedef SmtLibReader super;

  smt::Term return_defs();

 protected:
  // overloaded function, used when arg list of function is parsed
  // NOTE: | |  pipe quotes are removed.
  virtual smt::Term register_arg(const std::string & name,
                                 const smt::Sort & sort) override;

  std::string filename_;
};

WasimSmtLib2Parser::WasimSmtLib2Parser(const std::string & filename,
                                     smt::SmtSolver & solver)
    : super(solver), filename_(filename)
{
  set_logic_all();
  int res = parse(filename_);
  assert(!res);  // 0 means success
}

smt::Term WasimSmtLib2Parser::register_arg(const std::string & name,
                                          const smt::Sort & sort)
{
  smt::Term tmpvar;
  try {
    tmpvar = solver_->get_symbol(name);
  }
  catch (const std::exception & e) {
    // cout << "ERROR: Could not find " << name << " in solver! Wrong input
    // value."<< endl; cout << sort->get_sort_kind() << endl;
    tmpvar = solver_->make_symbol(name, sort);
  }
  arg_param_map_.add_mapping(name, tmpvar);
  return tmpvar;  // we expect to get the term in the transition system.

  // TODO: symbolic values do not exist in the transition system
}

smt::Term WasimSmtLib2Parser::return_defs()
{
  for (const auto & d : defs_)
    // cout << d.first << " : " << d.second << endl;
    return d.second;
  throw SimulatorException("No function definitions loaded so far");
  return NULL;
}

smt::Term load_smt_fundef(const std::string & filename, smt::SmtSolver & solver) {
  WasimSmtLib2Parser pi(filename, solver);
  return pi.return_defs();
}

} // namespace wasim
