/**
   Copyright (c) 2019 Microsoft Corporation and Arie Gurfinkel

   Module Name:

   spacer_conjecture.cpp

   Abstract:

   Methods to implement conjecture rule in gspacer

   Author:

   Arie Gurfinkel
   Hari Govind


   Notes:

--*/

#include "ast/for_each_expr.h"

#include "muz/spacer/spacer_context.h"
#include "muz/spacer/spacer_util.h"

namespace spacer {
/// Check whether \p pattern contains a single variable and is in LA or linear
/// fragment of BV
bool is_mono_var(expr *pattern, ast_manager &m, arith_util &a_util) {
    expr *e;
    bv_util bv(m);
    if (m.is_not(pattern, e)) return is_mono_var(e, m, a_util);
    if (a_util.is_arith_expr(to_app(pattern)) || bv.is_bv_ule(pattern) ||
        bv.is_bv_sle(pattern)) {
        return get_num_vars(pattern) == 1 && !has_nonlinear_var_mul(pattern, m);
    }
    return false;
}

/// Syntactic check to test whether the cluster with \p pattern contains a
/// single strongest element.
bool should_conjecture(const expr_ref &pattern, expr_ref &leq_lit) {
    if (get_num_vars(pattern) != 1) return false;
    ast_manager &m = leq_lit.m();
    arith_util a_util(m);
    // if the pattern has multiple literals, check whether exactly one of them
    // is leq
    expr_ref_vector pattern_and(m);
    pattern_and.push_back(pattern);
    flatten_and(pattern_and);
    unsigned count = 0;
    for (auto *lit : pattern_and) {
        if (is_mono_var(lit, m, a_util)) {
            leq_lit = lit;
            count++;
        }
    }
    return count == 1;
}

/// Returns true if range of s is numeric
bool is_numeric_sub(substitution &s) {
    ast_manager &m(s.get_manager());
    arith_util arith(m);
    bv_util bv(m);
    std::pair<unsigned, unsigned> var;
    expr_offset r;
    for (unsigned i = 0; i < s.get_num_bindings(); i++) {
        s.get_binding(i, var, r);
        if (!(bv.is_numeral(r.get_expr()) || arith.is_numeral(r.get_expr())))
            return false;
    }
    return true;
}

/// Drop all literals that numerically match \p lit, from \p fml_vec.
///
/// \p abs_fml holds the result. Returns true if any literal has been dropped
bool drop_lit(expr_ref_vector &fml_vec, expr_ref &lit,
              expr_ref_vector &abs_fml) {
    abs_fml.reset();
    bool is_smaller = false;
    ast_manager &m = fml_vec.get_manager();
    sem_matcher m_matcher(m);
    substitution sub(m);
    sub.reserve(1, get_num_vars(lit.get()));
    bool pos;
    SASSERT(!(m.is_not(lit) && m.is_eq(to_app(lit)->get_arg(0))));
    for (auto &c : fml_vec) {
        m_matcher.reset();
        if (m_matcher(lit, c, sub, pos) && pos) {
            if (is_numeric_sub(sub)) {
                is_smaller = true;
                continue;
            }
        }
        abs_fml.push_back(c);
    }
    return is_smaller;
}
} // namespace spacer
