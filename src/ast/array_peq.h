/*++
Copyright (c) 2023 Microsoft Corporation

Module Name:

    mbp_array_utils.h

Abstract:

   Useful datastructures and functions for array mbp

Author:

    Nikolaj Bjorner (nbjorner) 2015-06-13
    Hari Govind V K

Revision History:

--*/
#pragma once

#include "ast/array_decl_plugin.h"
#include "ast/ast.h"


/**
 * \brief utility class for partial equalities
 *
 * A partial equality (a ==I b), for two arrays a,b and a finite set of indices I holds
 *   iff (Forall i. i \not\in I => a[i] == b[i]); in other words, it is a
 *   restricted form of the extensionality axiom
 *
 * using this class, we denote (a =I b) as f(a,b,i0,i1,...)
 *   where f is an uninterpreted predicate with name PARTIAL_EQ and
 *   I = {i0,i1,...}
 */

// TBD: make work for arrays with multiple arguments.
class peq {
    ast_manager&        m;
    expr_ref            m_lhs;
    expr_ref            m_rhs;
    vector<expr_ref_vector>  m_diff_indices;
    func_decl_ref       m_decl;     // the partial equality declaration
    app_ref             m_peq;      // partial equality application
    app_ref             m_eq;       // equivalent std equality using def. of partial eq
    array_util          m_arr_u;
    symbol              m_name;

    public:

        peq (app* p, ast_manager& m);

        peq (expr* lhs, expr* rhs, vector<expr_ref_vector> const& diff_indices, ast_manager& m);

        expr_ref lhs () { return m_lhs; }

        expr_ref rhs () { return m_rhs; }

        void get_diff_indices (vector<expr_ref_vector>& result) { result.append(m_diff_indices); }

        app_ref mk_peq ();

        app_ref mk_eq (app_ref_vector& aux_consts, bool stores_on_rhs = true);
};

/**
 * mk (e0 ==indices e1)
 *
 * result has stores if either e0 or e1 or an index term has stores
 */
app_ref mk_peq (expr* e0, expr* e1, vector<expr_ref_vector> const& indices, ast_manager& m);

bool is_partial_eq (func_decl* f);

bool is_partial_eq (app* a);
