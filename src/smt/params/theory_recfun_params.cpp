/*++
  Copyright (c) 2020 Arie Gurfinkel

  Module Name:

  theory_recfun_params.cpp

  Abstract:

  Parameters for the theory solver for recfun

  Author:

  Hari Govind V K 2020-12-03.

  Revision History:

  --*/
#include "smt/params/theory_recfun_params.h"
#include "smt/params/smt_params_helper.hpp"

void theory_recfun_params::updt_params(params_ref const &_p) {
  smt_params_helper p(_p);
  m_weaken = p.recfun_weak();
  m_max_rounds = p.recfun_max_rounds();
}

#define DISPLAY_PARAM(X) out << #X "=" << X << std::endl;

void theory_recfun_params::display(std::ostream &out) const {
  DISPLAY_PARAM(m_weaken);
}
