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
#include "ast/expr_abstract.h"
#include "ast/for_each_expr.h"
#include "ast/recfun_decl_plugin.h"

namespace spacer {

// get axioms that make all selectors for all datatypes in \p sorts, total
void get_selector_total_axioms(ast_manager &m, const sort_ref_vector &sorts,
                               expr_ref_vector &res) {
    for (auto s : sorts)
        get_selector_total_axioms(m, s, res);
}

// get axioms that make all selectors for sort \p s total
void get_selector_total_axioms(ast_manager &m, sort *s, expr_ref_vector &res) {
    datatype_util u(m);
    SASSERT(u.is_datatype(s));
    ptr_vector<func_decl> const *cnstrs = u.get_datatype_constructors(s);
    for (auto cnstr : *cnstrs)
        get_selector_total_axioms(m, s, cnstr, res);
}

// get axioms that make all selectors for constructor \p cnstr total
void get_selector_total_axioms(ast_manager &m, sort *s, func_decl *cnstr,
                               expr_ref_vector &res) {
    datatype_util u(m);
    ptr_vector<func_decl> const *accessors = u.get_constructor_accessors(cnstr);
    ptr_vector<func_decl> const *cnstrs = u.get_datatype_constructors(s);
    for (auto accessor : *accessors) {
        for (auto o_cnstr : *cnstrs) {
            if (u.get_accessor_constructor(accessor) == o_cnstr) continue;
            if (o_cnstr->get_arity() == 0) mk_null_axiom(o_cnstr, accessor, m, res);
            else mk_non_null_axiom(o_cnstr, accessor, m, res);
        }
    }
}

//given a nullary constructor \p cnstr and a non matching \p accessor, add
//accessor(cnstr) = fresh_value to \p res
void mk_null_axiom(func_decl* cnstr, func_decl* accessor, ast_manager& m, expr_ref_vector& res) {
    SASSERT(cnstr->get_arity() == 0);
    expr_ref sel_app(m), eq(m), rhs(m);
    sort *r;
    sel_app = m.mk_app(accessor, to_expr(m.mk_const(cnstr)));
    r = accessor->get_range();
    rhs = m.get_some_value(r);
    eq = m.mk_eq(sel_app, rhs);
    res.push_back(eq);
}

// given a non nullary constructor \p cnstr and a non matching \p accessor, add
// \forall \vd. accessor(cnstr(\vd)) = fresh_value to \p res
void mk_non_null_axiom(func_decl *cnstr, func_decl *accessor, ast_manager &m,
                   expr_ref_vector &res) {
    SASSERT(cnstr->get_arity() != 0);
    expr_ref sel_app(m), eq(m), rhs(m), cnstr_app(m), q_body(m), q_app(m), var(m);
    sort* s, *r;
    ptr_buffer<sort> sorts;
    svector<symbol> names;
    expr_ref_vector vars(m);
    unsigned sz = cnstr->get_arity();
    for(unsigned i = 0; i < sz; i++) {
        s = cnstr->get_domain(i);
        sorts.push_back(s);
        var = m.mk_fresh_const(cnstr->get_name(), s);
        vars.push_back(var);
        names.push_back(to_app(var)->get_decl()->get_name());
    }
    cnstr_app = m.mk_app(cnstr, vars);
    sel_app = m.mk_app(accessor, cnstr_app);
    r = accessor->get_range();
    rhs = m.get_some_value(r);
    eq = m.mk_eq(sel_app, rhs);
    q_body = expr_abstract(m, 0, vars.size(), vars.c_ptr(), eq);
    q_app = m.mk_forall(sz, sorts.c_ptr(), names.c_ptr(), q_body);
    res.push_back(q_app);
    TRACE("datatype", tout << "Adding ADT axiom " << q_app << "\n";);
}

// remove all literals rf(t_1) = t_2 in \p res;
// changes order of literals in res. TODO: rewrite
void drop_rf_app(expr_ref_vector &res) {
    if (res.empty()) return;
    ast_manager &m(res.m());
    recfun::util recfun(m);
    expr *arg1, *arg2, *e;
    unsigned i = 0, j = res.size() - 1;
    for (; i <= j;) {
        e = res.get(i);
        if (!((m.is_eq(e, arg1, arg2) && recfun.is_defined(arg1)) || recfun.is_defined(e) || (m.is_not(e, arg1) && recfun.is_defined(arg1))))
            i++;
        else {
            res.set(i, res.get(j));
            j--;
        }
    }
    res.shrink(i);
}

namespace contains_rf_ns {
struct found {};
struct contains_rf_proc {
    ast_manager &m;
    recfun::util m_recfun;
    contains_rf_proc(ast_manager &a_m) : m(a_m), m_recfun(m) {}
    void operator()(expr *n) const {}
    void operator()(app *n) {
        if (m_recfun.has_def(n->get_decl())) throw found();
    }
};
} // namespace contains_rf_ns

// check whether \p e contains a recfun term
bool contains_rf_app(expr *e, ast_manager &m) {
    contains_rf_ns::contains_rf_proc t(m);
    try {
        for_each_expr(t, e);
        return false;
    } catch (const contains_rf_ns::found &) { return true; }
}

// check whether \p cube contains a recfun term
bool contains_rf_app(expr_ref_vector &cube) {
    for (auto a : cube)
        if (contains_rf_app(a, cube.m())) return true;
    return false;
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

bool contains_datatype(expr_ref lit) {
    sort_ref_vector s(lit.get_manager());
    get_datatype_sorts(lit, s);
    return s.size() > 0;
}

} // namespace spacer
