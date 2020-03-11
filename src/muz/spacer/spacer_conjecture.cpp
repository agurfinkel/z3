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
