/*++
  Copyright (c) 2020 Arie Gurfinkel

  Module Name:

  spacer_datatype_util.h

  Abstract:

  Helper functions for handling datatypes in Spacer

  Author:

  Hari Govind V K
  Arie Gurfinkel


  --*/
#include "ast/ast.h"

#pragma once
namespace spacer {
// get axioms that make all selectors for all datatypes in \p sorts, total
void get_selector_total_axioms(ast_manager &m, const sort_ref_vector &sorts,
                               expr_ref_vector &res);

// get axioms that make all selectors for sort \p s total
void get_selector_total_axioms(ast_manager &m, sort *s, expr_ref_vector &res);

// get axioms that make all selectors for constructor \p cnstr total
void get_selector_total_axioms(ast_manager &m, sort *s, func_decl *cnstr,
                               expr_ref_vector &res);

// get all datatype sorts that appear in \p exp
void get_datatype_sorts(expr_ref exp, sort_ref_vector &res);

// given a nullary constructor \p cnstr and a non matching \p accessor, add
// accessor(cnstr) = fresh_value to \p res
void mk_null_axiom(func_decl *cnstr, func_decl *accessor, ast_manager &m,
                   expr_ref_vector &res);

// given a non nullary constructor \p cnstr and a non matching \p accessor, add
// \forall \vd. accessor(cnstr(\vd)) = fresh_value to \p res
void mk_non_null_axiom(func_decl *cnstr, func_decl *accessor, ast_manager &m,
                   expr_ref_vector &res);

// check whether \p e contains a recfun term
bool contains_rf_app(expr *e, ast_manager &m);

// check whether \p lit contains a datatype sort
bool contains_datatype(expr_ref lit);

// check whether \p cube contains a recfun term
bool contains_rf_app(expr_ref_vector &cube);

// remove all applications of rf in \p res;
void drop_rf_app(expr_ref_vector &res);

} // namespace spacer
