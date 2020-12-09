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
// get axioms that make all selectors for all constructors for all datatypes in
// \p sorts total
void get_selector_total_axioms(ast_manager &m, const sort_ref_vector &sorts,
                               expr_ref_vector &res);

// get axioms that make all selectors for all constructors of sort \p s total
void get_selector_total_axioms(ast_manager &m, sort *s, expr_ref_vector &res);

// get axioms that make all selectors for constructor \p cnstr total
void get_selector_total_axioms(ast_manager &m, sort *s, func_decl *cnstr,
                               expr_ref_vector &res);

// get all datatype sorts that appear in \p exp
void get_datatype_sorts(expr_ref exp, sort_ref_vector &res);

} // namespace spacer
