/*++
Copyright (c) 2020 Arie Gurfinkel

Module Name:

  spacer_concretize.cpp

Abstract:

  Concretize a pob

Author:

  Hari Govind V K
  Arie Gurfinkel


--*/
#include "spacer_concretize.h"
namespace {

/// checks whether f is a binary operator or a negation of a binary operator
bool is_bin_op(expr *f, expr *&lhs, expr *&rhs, ast_manager &m) {
    expr *e;

    if (!is_app(f)) return false;
    if (m.is_not(f, e)) return is_bin_op(e, lhs, rhs, m);
    app *fapp = to_app(f);
    if (fapp->get_num_args() != 2) return false;

    lhs = fapp->get_arg(0);
    rhs = fapp->get_arg(1);
    return true;
}
} // anonymous namespace

namespace should_grp {
struct found {};
struct proc {
    arith_util m_arith;
    expr *m_uc;
    proc(ast_manager &m, expr *uc) : m_arith(m), m_uc(uc) {}
    void operator()(var *n) const {}
    void operator()(quantifier *q) const {}
    void operator()(app const *n) const {
        expr *e1, *e2;
        if (m_arith.is_mul(n, e1, e2) &&
            ((is_var(e1) && e2 == m_uc) || (is_var(e2) && e1 == m_uc)))
            throw found();
    }
};
} // namespace should_grp

namespace spacer {

/// Checks whether the uninterp_const in term has a var coeff in pattern
bool concretize::should_partition(expr *pattern, expr *term) {
    expr_ref_vector uc(m);
    get_uninterp_consts(term, uc);
    TRACE("concretize_verb", tout << "should group " << mk_pp(term, m)
                                  << " according to pattern "
                                  << mk_pp(pattern, m) << "\n";);
    SASSERT(uc.size() == 1);
    should_grp::proc proc(m, uc.get(0));
    try {
        for_each_expr(proc, pattern);
    } catch (const should_grp::found &) { return true; }
    return false;
}

/// Concretize formula \p f using literals of dim 1
///
/// returns false if \p f is not an arithmetic fml
bool concretize::mk_concr(expr_ref f, model_ref &model, expr_ref_vector &res,
                          expr_ref pattern) {
    SASSERT(is_app(f));
    SASSERT(pattern.get());

    expr_ref_vector u_consts(m);
    get_uninterp_consts(f, u_consts);

    expr_ref_vector conj(m), todo(m);
    flatten_and(f, conj);

    expr *e1;
    for (auto *e : conj) {
        // separate out boolean u_c
        if (not_handled(e))
            res.push_back(e);
        else if (!(m_arith.is_arith_expr(e) ||
                   (m.is_not(e, e1) && m_arith.is_arith_expr(e1)))) {
            TRACE("concretize_verb", tout << "Literal cannot be concretized " << mk_pp(e, m););
            return false;
        } else
            todo.push_back(e);
    }

    partition_and_concretize(todo, pattern, model, res);

    TRACE("concretize",
          tout << "produced a concretization : " << mk_and(res) << "\n";);
    SASSERT(!res.empty());
    return true;
}

/// Partition terms of \p cube using the method partition_terms.
/// Then find bounds \p lb and \p ub such that
///            \Land_{p \in partitions} (lb[t] <= t <= ub[t]) ==> cube
void concretize::partition_and_concretize(const expr_ref_vector &cube,
                                          expr_ref pattern, model_ref &model,
                                          expr_ref_vector &concr_cube) {
    expr_ref_vector groups(m);
    expr_ref_vector sub_term(m);
    expr_ref_vector non_lit_cube(m);
    TRACE("concretize", tout << "grouping an arithmetic pob : ";
          tout << mk_and(cube) << " and pattern " << mk_pp(pattern, m)
               << " \n";);
    for (auto lit : cube) {
        partition_terms(pattern, expr_ref(lit, m), groups, sub_term);
    }
    TRACE("concretize", tout << "groups are : " << groups << "\n";);

    expr_ref sub_fml(m);
    // TODO ensure union of groups has all the variables
    expr_safe_replace s(m);
    expr_ref_vector variables(m);
    expr_expr_map sub(m);
    expr_ref_vector fresh_consts(m);
    for (expr *grp : groups) {
        expr_ref eval_ref = (*model)(&(*grp));
        SASSERT(m_arith.is_numeral(eval_ref));
        fresh_consts.push_back(m.mk_fresh_const("sub_temp", grp->get_sort()));
        s.insert(grp, fresh_consts.back());
        sub.insert(fresh_consts.back(), grp);
    }
    expr_ref c = mk_and(sub_term);
    s(c, sub_fml);
    TRACE("concretize", tout << "substituted formula : " << sub_fml << "\n";);
    expr_rat_map lb(m), ub(m);
    expr_ref_vector sub_fml_vec(m), u_consts(m);
    flatten_and(sub_fml, sub_fml_vec);

    concretize_cube(sub_fml_vec, model, lb, ub, &sub);

    get_uninterp_consts(sub_fml, u_consts);
    for (expr *u_const : u_consts) {
        if (lb.contains(u_const))
            concr_cube.push_back(m_arith.mk_ge(
                sub[u_const],
                m_arith.mk_numeral(lb[u_const], lb[u_const].is_int())));
        if (ub.contains(u_const))
            concr_cube.push_back(m_arith.mk_le(
                sub[u_const],
                m_arith.mk_numeral(ub[u_const], ub[u_const].is_int())));
    }
    fresh_consts.reset();
    TRACE("concretize",
          tout << "concrete pob : " << mk_pp(mk_and(concr_cube), m) << "\n";);
}

/// Partition terms in \p formula such that each constant that has a
/// variable coefficient in \p pattern belongs to a separate partition.
///
/// \p formula is an LA literal in SOP. \p out is the partitioning \p sub_term
/// is a syntactic rewriting of \p formula such that each term in \p out is a
/// term in \p sub_term.
/// If there are n non linear multiplications in pattern, there are n + 1 axis.
void concretize::partition_terms(expr_ref pattern, expr_ref formula,
                                 expr_ref_vector &out,
                                 expr_ref_vector &sub_term) {
    expr *t, *c;
    if (!is_bin_op(formula, t, c, m)) return;

    expr_ref_vector rw_formula(m);
    expr_ref_vector others(m);
    // If the literal cannot be split, just make it a whole group
    if (is_constant(t) || m_arith.is_mul(t)) {
        sub_term.push_back(formula);
        out.push_back(t);
        return;
    }

    SASSERT(is_app(t));
    TRACE("concretize_verb",
          tout << "computing groups in " << formula << "\n";);
    for (auto term : *to_app(t)) {
        if (should_partition(pattern, term)) {
            if (!out.contains(term)) {
                TRACE("concretize_verb",
                      tout << "adding " << mk_pp(term, m) << " to groups\n";);
                out.push_back(term);
            }
            rw_formula.push_back(term);
        } else
            others.push_back(term);
    }
    if (others.size() > 0) {
        expr_ref sum_term(m);
        sum_term = m_arith.mk_add(others.size(), others.c_ptr());
        if (!out.contains(sum_term)) {
            TRACE("concretize_verb",
                  tout << "adding " << sum_term << " to groups\n";);
            out.push_back(sum_term);
        }
        rw_formula.push_back(sum_term);
    }
    expr *e;
    expr_ref t_sub(m);
    // recontruct the formula with the same syntax structure as the substitution
    if (m.is_not(formula, e))
        t_sub = m.mk_not(
            m.mk_app(to_app(e)->get_decl(),
                     m_arith.mk_add(rw_formula.size(), rw_formula.c_ptr()), c));
    else
        t_sub =
            m.mk_app(to_app(formula)->get_decl(),
                     m_arith.mk_add(rw_formula.size(), rw_formula.c_ptr()), c);
    TRACE("concretize_verb", tout << "re-wrote " << formula << " into " << t_sub
                                  << " for substitution\n";);
    sub_term.push_back(t_sub);
}
/// SOP: (+ (* a0) ... (*aN))
bool concretize::is_sop(expr *e) {
    if (is_constant(e)) return true;
    if (!m_arith.is_arith_expr(e)) return false;
    if (!is_app(e)) return false;

    expr *e1, *e2;
    if (m_arith.is_mul(e, e1, e2)) {
        if (is_constant(e1) && is_constant(e2)) return true;
        return false;
    }
    // cannot have a top level operand other than plus
    if (!m_arith.is_add(e)) return false;

    // all terms inside have to be either a constant or a product of
    // constants
    for (expr *term : *to_app(e)) {
        if (is_constant(term))
            continue;
        else if (m_arith.is_mul(term, e1, e2) && is_constant(e1) && is_constant(e2))
            continue;
        else
            return false;
    }
    return true;
}

/// Find the coeff of \p v in term \p t
///
/// Returns false if t is not in LA, does not contain \p v, or not in SOP or
/// -1*SOP form. If \p v appears multiple times, the coefficient in first
/// linear term is returned.
bool concretize::find_coeff(expr_ref t, expr_ref v, rational &k,
                            unsigned depth) {
    if (t == v) {
        k = rational::one();
        return true;
    }
    if (depth == 0) return false;

    expr *e1 = nullptr, *e2 = nullptr;
    rational coeff;
    expr_ref kid(m);
    if (m_arith.is_mul(t, e1, e2)) {
        if (!m_arith.is_numeral(e1, coeff) && !m_arith.is_numeral(e2, coeff))
            return false;
        kid = m_arith.is_numeral(e1) ? e2 : e1;
        if (!find_coeff(kid, v, k, depth - 1)) return false;
        k = k * coeff;
        return true;
    }

    if (m_arith.is_add(t)) {
        for (expr *e : *to_app(t)) {
            kid = e;
            if (find_coeff(kid, v, k, depth - 1)) { return true; }
        }
        return false;
    }

    return false;
}

/// Returns whether the value of \p lit increases(1), decreases(-1) or doesn't
/// change(0) with \p var
///
/// \p l is assumed to be a term in LA
int concretize::change_with_var(expr_ref l, expr_ref var) {
    rational coeff;
    // lhs is in the sum of products form (ax + by)
    bool found = find_coeff(l, var, coeff);

    TRACE("concretize_verb", tout << "coefficient of " << mk_pp(var, m)
                                  << " in term " << mk_pp(l, m) << " is "
                                  << coeff << "\n";);
    if (!found) return 0;
    SASSERT(!coeff.is_zero());
    if (coeff.is_pos())
        return 1;
    else if (coeff.is_neg())
        return -1;
    // to silence the compiler
    else
        return 0;
}

/// Tighten bounds \p lb and \p ub such that
///     \forall x \in uninterp_consts(term) (lb[x] <= x <= ub[x]) ==> term <=
///     model(term)
///
/// NOTE: optimize using bg if we need better bounds. In this
/// case, should update background as bounds are discovered!!!!
void concretize::concretize_term(model_ref &model, expr_ref term,
                                 expr_rat_map &lb, expr_rat_map &ub,
                                 expr_expr_map *sub) {
    expr_ref val(m);

    expr_ref_vector dims(m);
    get_uninterp_consts(term, dims);

    for (expr *var : dims) {
        // compute variation of l along dim d
        int change = change_with_var(term, expr_ref(var, m));
        SASSERT(!sub || sub->contains(var));
        CTRACE("concretize_verb", sub,
               tout << "computing value of " << mk_pp(var, m) << "\n";);
        val = (*model)(sub ? (*sub)[var] : var);
        CTRACE("concretize_verb", sub,
               tout << " value of " << mk_pp(var, m) << " is " << val << "\n";);

        SASSERT(m_arith.is_numeral(val));

        // update bounds
        rational nw_bnd;
        m_arith.is_numeral(val, nw_bnd);
        if (change > 0) {
            if (!ub.contains(var))
                ub.insert(var, nw_bnd);
            else if (nw_bnd < ub[var])
                ub[var] = nw_bnd;
            TRACE("concretize_verb", tout << "upper bounds for "
                                          << mk_pp(var, m) << " is " << ub[var]
                                          << "\n";);
        }

        if (change < 0) {
            if (!lb.contains(var))
                lb.insert(var, nw_bnd);
            else if (nw_bnd > lb[var])
                lb[var] = nw_bnd;
            TRACE("concretize_verb", tout << "lower bounds for "
                                          << mk_pp(var, m) << " is " << lb[var]
                                          << "\n";);
        }
    }
}

/// Find bounds \p lb, \p ub such that
///     \Land x \in uninterp_consts(cube) (lb[x] <= x <= ub[x]) ==> cube
void concretize::concretize_cube(const expr_ref_vector &conj, model_ref &model,
                                 expr_rat_map &lb, expr_rat_map &ub,
                                 expr_expr_map *sub) {
    SASSERT(ub.size() == 0);
    SASSERT(lb.size() == 0);
    expr_ref t(m), c(m);
    for (expr *lit : conj) {
        if (under_approx_using_le(lit, t, c)) {
            TRACE("concretize", tout << "literal is " << mk_pp(lit, m)
                                     << "normalized as: " << mk_pp(t, m)
                                     << " <= " << mk_pp(c, m) << "\n";);

            concretize_term(model, t, lb, ub, sub);
        }
    }
}

} // namespace spacer
