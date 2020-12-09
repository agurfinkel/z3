/*++
  Copyright (c) 2020 Arie Gurfinkel

  Module Name:

  spacer_datatype_util.cpp

  Abstract:

  Helper functions for handling datatypes in Spacer

  Author:

  Hari Govind V K
  Arie Gurfinkel


  --*/

#include "muz/spacer/spacer_datatype_util.h"
#include "ast/ast.h"
#include "ast/ast_pp.h"
#include "ast/datatype_decl_plugin.h"
#include "ast/for_each_expr.h"

namespace spacer {

void get_selector_total_axioms(ast_manager &m, const sort_ref_vector &sorts,
                               expr_ref_vector &res) {
    datatype_util u(m);
    for (auto s : sorts) {
        SASSERT(u.is_datatype(s));
        get_selector_total_axioms(m, s, res);
    }
}

void get_selector_total_axioms(ast_manager &m, sort *s, expr_ref_vector &res) {
    datatype_util u(m);
    unsigned sz = u.get_datatype_num_constructors(s);
    // if (u.datatype_params(s).size() > 0) NOT_IMPLEMENTED_YET();
    ptr_vector<func_decl> const *cnstrs = u.get_datatype_constructors(s);
    for (unsigned i = 0; i < sz; i++) {
        func_decl *cnstr = cnstrs->get(i);
        get_selector_total_axioms(m, s, cnstr, res);
    }
}

void get_selector_total_axioms(ast_manager &m, sort *s, func_decl *cnstr,
                               expr_ref_vector &res) {
    datatype_util u(m);
    ptr_vector<func_decl> const *accessors = u.get_constructor_accessors(cnstr);
    ptr_vector<func_decl> const *cnstrs = u.get_datatype_constructors(s);
    unsigned num_sel = cnstr->get_arity();
    unsigned sz = u.get_datatype_num_constructors(s);
    expr_ref sel_app(m), eq(m), rhs(m);
    for (unsigned i = 0; i < num_sel; i++) {
        func_decl *accessor = accessors->get(i);
        for (unsigned j = 0; j < sz; j++) {
            func_decl *cnstr = cnstrs->get(j);
            if (u.get_accessor_constructor(accessor) == cnstr) continue;
            if (cnstr->get_arity() != 0) NOT_IMPLEMENTED_YET();
            sel_app = m.mk_app(accessor, to_expr(m.mk_const(cnstr)));
            sort *r = accessor->get_range();
            rhs = m.get_some_value(r);
            eq = m.mk_eq(sel_app, rhs);
            res.push_back(eq);
        }
    }
}

namespace get_dt_ns {
struct found {};
struct get_dt_proc {
    ast_manager &m;
    datatype_util m_dt;
    sort_ref_vector &m_sorts;
    get_dt_proc(ast_manager &a_m, sort_ref_vector &res)
        : m(a_m), m_dt(m), m_sorts(res) {}
    void operator()(expr *n) const {}
    void operator()(app *n) {
        sort *s = m.get_sort(n);
        if (m_dt.is_datatype(s) && !m_sorts.contains(s)) m_sorts.push_back(s);
    }
};
} // namespace get_dt_ns

void get_datatype_sorts(expr_ref e, sort_ref_vector &s) {
    get_dt_ns::get_dt_proc t(e.get_manager(), s);
    for_each_expr(t, e);
}
} // namespace spacer
