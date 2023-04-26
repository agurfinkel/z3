/*++

  Module Name:

    qel.h

Abstract:

    Quantifier-elimination using term graphs

Author:

    Isabel Garcia (igcontreras)
    Hari Govind V K (hgvk94)

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
