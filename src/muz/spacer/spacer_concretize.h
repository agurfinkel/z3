#pragma once
/*++
Copyright (c) 2020 Arie Gurfinkel

Module Name:

  spacer_concretize.h

Abstract:

  Concretize a pob

Author:

  Hari Govind V K
  Arie Gurfinkel


--*/

#include "ast/ast.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "muz/spacer/spacer_context.h"
#include "muz/spacer/spacer_util.h"
#include "tactic/core/ctx_simplify_tactic.h"
#include "util/obj_ref_hashtable.h"
#include "util/rational.h"

typedef obj_ref_map<ast_manager, expr, expr *> expr_expr_map;
typedef obj_ref_map<ast_manager, expr, rational> expr_rat_map;
namespace spacer {
class concretize {
    ast_manager &m;
    arith_util m_arith;
    /// Find the coeff of \p v in \p t
    ///
    /// Assumes that t is in LA and in SOP or -1*SOP form
    void find_coeff(expr_ref t, expr_ref v, rational &k);

    /// Returns whether the value of \p lit increases(1), decreases(-1) or
    /// doesn't change(0) with \p var
    int change_with_var(expr_ref lit, expr_ref var);

    /// Tighten bounds \p lb and \p ub such that
    ///     \forall x \in uninterp_consts(term) (lb[x] <= x <= ub[x]) ==> term
    void concretize_term(model_ref &model, expr_ref term, expr_rat_map &lb,
                        expr_rat_map &ub, expr_expr_map *sub = nullptr);

    /// Find bounds \p lb, \p ub such that
    ///     \Land x \in uninterp_consts(cube) (lb[x] <= x <= ub[x]) ==> cube
    void concretize_cube(const expr_ref_vector &cube, model_ref &model,
                         expr_rat_map &lb, expr_rat_map &ub,
                         expr_expr_map *sub = nullptr);

    /// Partition terms of \p cube using the method partition_terms.
    /// Then find bounds \p lb and \p ub such that
    ///            \Land_{p \in partitions} (lb[t] <= t <= ub[t]) ==> cube
    void partition_and_concretize(const expr_ref_vector &cube, expr_ref pattern,
                        model_ref &model, expr_ref_vector &ua);

    // Check whether \p term is to be treated as a separate partition according to \p pattern
    bool should_partition(expr *pattern, expr *term);

    /// Partition terms in \p formula such that each constant that has a
    /// variable coefficient in \p pattern belongs to a separate partition.
    void partition_terms(expr_ref pattern, expr_ref formula,
                        expr_ref_vector &out, expr_ref_vector &sub_term);

    bool is_constant(expr const *e) {
        return is_uninterp_const(e) || m_arith.is_numeral(e);
    }

    bool not_handled(expr *e) {
        expr *not_chld;
        return is_uninterp_const(e) || m_arith.is_numeral(e) || m.is_eq(e) ||
               contains_mod(expr_ref(e, m)) ||
               (m.is_not(e, not_chld) && not_handled(not_chld));
    }

    /// Check whether each literal in \p e is in Sum Of Products form
    bool is_sop(expr_ref_vector &e) {
        for (expr *a : e) {
            if (!is_sop(a)) return false;
        }
        return true;
    }
    /// SOP: (+ (* a0) ... (*aN))
    bool is_sop(expr *e);

  public:
    concretize(ast_manager &manager) : m(manager), m_arith(m) {}
    /// Concretize formula \p f using literals of dim 1
    /// returns false if \p f is not an arithmetic fml
    bool mk_concr(expr_ref n, model_ref &model, expr_ref_vector &u_a,
                  expr_ref pattern);
};
} // namespace spacer
