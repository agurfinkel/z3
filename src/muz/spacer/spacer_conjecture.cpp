/**
   Copyright (c) 2019 Microsoft Corporation and Arie Gurfinkel

   Module Name:

   spacer_abstraction.cpp

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

bool is_mono_var(expr *pattern, ast_manager &m, arith_util &a_util) {
    expr *e;
    bv_util bv(m);
    if (m.is_not(pattern, e)) return is_mono_var(e, m, a_util);
    if (a_util.is_arith_expr(to_app(pattern)) || bv.is_bv_ule(pattern) || bv.is_bv_sle(pattern)) {
        return get_num_vars(pattern) == 1 && !has_nonlinear_var_mul(pattern, m);
    }
    return false;
}

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

bool drop_lit(expr_ref_vector &fml_vec, expr_ref &lit,
              expr_ref_vector &abs_fml) {
    abs_fml.reset();
    bool is_smaller = false;
    ast_manager &m = fml_vec.get_manager();
    sem_matcher m_matcher(m);
    bv_util bv(m);
    substitution sub(m);
    sub.reserve(1, get_num_vars(lit.get()));
    std::pair<unsigned, unsigned> var;
    expr_offset r;
    bool pos;
    SASSERT(!(m.is_not(lit) && m.is_eq(to_app(lit)->get_arg(0))));
    for (auto &c : fml_vec) {
        m_matcher.reset();
        if (m_matcher(lit, c, sub, pos) && pos) {
            bool numeral_match = true;
            for(unsigned i = 0; i < sub.get_num_bindings(); i++) {
                sub.get_binding(i, var, r);
                if (!bv.is_numeral(r.get_expr())) numeral_match = false;
            }
            if (numeral_match) {
                is_smaller = true;
                continue;
            }
        }
        abs_fml.push_back(c);
    }
    return is_smaller;
}
} // namespace spacer
