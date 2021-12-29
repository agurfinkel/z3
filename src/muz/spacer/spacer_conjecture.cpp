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
/// Returns true if \p pat has a single variable and is in LA or LA_BV
bool is_mono_var(expr *pat, ast_manager &m) {
    expr *e;
    bv_util bv(m);
    arith_util a_util(m);
    if (m.is_not(pat, e)) return is_mono_var(e, m);
    if (a_util.is_arith_expr(to_app(pat)) || bv.is_bv_ule(pat) ||
        bv.is_bv_sle(pat)) {
        return get_num_vars(pat) == 1 && !has_nonlinear_var_mul(pat, m);
    }
    return false;
}

/// Returns true if cluster with a patter \p pat has a single strongest
/// element.
bool should_conjecture(const expr_ref &pat, expr_ref &leq_lit) {
    if (get_num_vars(pat) != 1) return false;
    ast_manager &m = leq_lit.m();

    // if the pattern has multiple literals, check whether exactly one of them
    // is leq
    expr_ref_vector conj(m);
    conj.push_back(pat);
    flatten_and(conj);
    unsigned count = 0;
    for (auto *lit : conj) {
        if (is_mono_var(lit, m)) {
            if (count) return false;
            leq_lit = lit;
            count++;
        }
    }
    SASSERT(count <= 1);
    return count == 1;
}

/// Returns true if the range of substitution \p s is numeric
bool is_numeric_sub(substitution &s) {
    ast_manager &m(s.get_manager());
    arith_util arith(m);
    bv_util bv(m);
    std::pair<unsigned, unsigned> var;
    expr_offset r;
    for (unsigned i = 0, sz = s.get_num_bindings(); i < sz; ++i) {
        s.get_binding(i, var, r);
        if (!(bv.is_numeral(r.get_expr()) || arith.is_numeral(r.get_expr())))
            return false;
    }
    return true;
}

/// Drop all literals that numerically match \p lit, from \p fml
///
/// \p out holds the result. Returns true if any literal has been dropped
bool drop_lit(expr_ref_vector &fml, expr_ref &lit, expr_ref_vector &out) {
    ast_manager &m = fml.get_manager();
    bool dirty = false, pos = false;
    sem_matcher m_matcher(m);
    substitution sub(m);

    out.reset();
    sub.reserve(1, get_num_vars(lit.get()));
    SASSERT(!(m.is_not(lit) && m.is_eq(to_app(lit)->get_arg(0))));
    for (auto &c : fml) {
        m_matcher.reset();
        if (m_matcher(lit, c, sub, pos) && pos) {
            if (is_numeric_sub(sub)) {
                dirty = true;
                continue;
            }
        }
        out.push_back(c);
    }
    return dirty;
}
} // namespace spacer
