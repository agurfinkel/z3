/*++

  Module Name:

    qel.h

Abstract:

    Light weight quantifier elimination based on term graph. Paper: Fast
    Approximations of Quantifier Elimination CAV 2023

Author:

    Hari Govind V K (hgvk94)
    Isabel Garcia (igcontreras)

Revision History:


--*/

#pragma once

#include "ast/ast.h"
#include "ast/ast_util.h"
#include "util/uint_set.h"
#include "util/params.h"

class qel {
    class impl;
    impl * m_impl;
public:

    qel(ast_manager& m, params_ref const & p);

    ~qel();

    /**
       \brief Applies light-weight elimination of `vars` provided as vector
       of expressions to the cube `fml`. Returns the updated formula and updated
       set of variables that were not eliminated.
    */
    void operator()(app_ref_vector& vars, expr_ref& fml);
};
