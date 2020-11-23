/*++
  Copyright (c) 2020 Arie Gurfinkel

  Module Name:

  spacer_expand_bnd_generalizer.cpp

  Abstract:

  Strengthen lemmas by changing numeral constants inside arithmetic literals

  Author:

  Hari Govind V K
  Arie Gurfinkel


--*/
#include "muz/spacer/spacer_expand_bnd_generalizer.h"
#include "ast/rewriter/expr_safe_replace.h"
namespace {
/// Checks whether \p fml is an arithmetic inequality with a numeral \p val on
/// the rhs
bool is_ineq(ast_manager &m, const expr *fml, rational &val) {
    expr *term, *num;
    arith_util m_arith(m);
    expr *not_fml;
    if (m.is_not(fml, not_fml)) return is_ineq(m, not_fml, val);
    if ((m_arith.is_le(fml, term, num) || m_arith.is_ge(fml, term, num)) &&
        m_arith.is_numeral(num, val))
        return true;
    return false;
}

/// Replace RHS of \p fml with \p n
void substitute(rational n, const expr *fml, expr_ref &res) {
    SASSERT(is_app(fml));
    ast_manager &m = res.get_manager();
    rational val;
    (void)val;
    SASSERT(is_ineq(m, fml, val));
    arith_util m_arith(m);
    expr *not_fml;
    if (m.is_not(fml, not_fml)) {
        substitute(n, not_fml, res);
        ::push_not(res);
        return;
    }
    expr *lhs = to_app(fml)->get_arg(0);
    res = m.mk_app(to_app(fml)->get_decl(), lhs,
                   m_arith.mk_numeral(n, n.is_int()));
}

/// Substitute \p lit in \p fml with \p sub
void substitute(expr_ref lit, expr_ref sub, expr_ref_vector &fml) {
    fml.erase(lit.get());
    fml.push_back(sub);
}

} // namespace
namespace spacer {
lemma_expand_bnd_generalizer::lemma_expand_bnd_generalizer(context &ctx)
    : lemma_generalizer(ctx), m(ctx.get_ast_manager()), m_arith(m) {
    for (auto &kv : ctx.get_pred_transformers()) {
        kv.m_value->extract_nums(m_values);
    }
}

void lemma_expand_bnd_generalizer::operator()(lemma_ref &lemma) {
    scoped_watch _w_(m_st.watch);
    if (lemma->get_pob()->expand_bnd()) {
        // try expanding bounds
        const expr_ref_vector &conj = lemma->get_cube();
        expr_ref_vector updt_conj(conj);
        expr_ref bnd(m), new_bnd(m);
        rational val;
        for (unsigned i = 0; i < conj.size(); i++) {
            bnd = conj.get(i);
            if (!is_ineq(m, bnd, val)) continue;
            if (!updt_conj.contains(bnd)) continue;
            TRACE("expand_bnd", tout << "Attempting to expand " << bnd
                                     << " inside " << conj << "\n";);
            for (rational n : m_values) {
                /// It could be the case that bnd has already been removed
                if (!updt_conj.contains(bnd)) break;
                if (!should_apply(bnd, n)) continue;
                TRACE("expand_bnd", tout << "Attempting to expand " << bnd
                                         << " with numeral " << n << "\n";);
                substitute(n, bnd, new_bnd);
                SASSERT(new_bnd.get() != nullptr);
                substitute(bnd, new_bnd, updt_conj);
                m_st.atmpts++;
                if (check_ind_and_update(lemma, updt_conj)) { bnd = new_bnd; }
            }
        }
        lemma->get_pob()->stop_expand_bnd();
    }
}

/// Check whether \p conj is a possible generalization for \p lemma.
/// update \p lemma if it is.
bool lemma_expand_bnd_generalizer::check_ind_and_update(lemma_ref &lemma,
                                                        expr_ref_vector &conj) {
    unsigned uses_level = 0;
    TRACE("expand_bnd_verb",
          tout << "Attempting to update lemma with " << conj << "\n";);
    bool is_ind = (lemma->get_pob())
                      ->pt()
                      .check_inductive(lemma->level(), conj, uses_level,
                                       lemma->weakness());

    if (is_ind) {
        m_st.success++;
        lemma->update_cube(lemma->get_pob(), conj);
        lemma->set_level(uses_level);
        TRACE("expand_bnd", tout << "expand_bnd succeeded with " << mk_and(conj)
                                 << " at level " << uses_level << "\n";);
        return true;
    }
    return false;
}
/// Check whether \p n can be used to weaken lit
bool lemma_expand_bnd_generalizer::should_apply(const expr *lit, rational n) {
    rational val;
    if (!is_ineq(m, lit, val)) return false;
    return should_apply(lit, val, n);
}

/// Check whether lit ==> lit[val |--> n] (barring special cases). That is,
/// whether \p lit becomes weaker if \p val is replaced with \p n
///
/// \p lit has to be of the form t <= v where v is a numeral.
/// Special cases:
/// In the trivial case in which \p val == \p n, return false.
/// if lit is an equality or the negation of an equality, return true.
bool lemma_expand_bnd_generalizer::should_apply(const expr *lit, rational val,
                                                rational n) {
    // the only case in which negation and non negation agree
    if (val == n) return false;

    // negation is the actual negation modulo val == n
    expr *neg_lit;
    if (m.is_not(lit, neg_lit)) { return !should_apply(neg_lit, val, n); }

    SASSERT(val != n);
    if (m.is_eq(lit)) return true;
    switch (to_app(lit)->get_decl_kind()) {
    case OP_LE:
        return n > val;
    case OP_LT:
        return n > val;
    case OP_GT:
        return n < val;
    case OP_GE:
        return n < val;
    default:
        return false;
    }
}

void lemma_expand_bnd_generalizer::collect_statistics(statistics &st) const {
    st.update("time.spacer.solve.reach.gen.expand", m_st.watch.get_seconds());
    st.update("SPACER expand_bnd attmpts", m_st.atmpts);
    st.update("SPACER expand_bnd success", m_st.success);
}
} // namespace spacer
