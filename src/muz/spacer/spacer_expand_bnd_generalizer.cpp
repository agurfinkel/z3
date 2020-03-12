#include "ast/rewriter/expr_safe_replace.h"
#include "muz/spacer/spacer_generalizers.h"
namespace spacer {
lemma_expand_bnd_generalizer::lemma_expand_bnd_generalizer(context &ctx)
    : lemma_generalizer(ctx), m(ctx.get_ast_manager()), m_arith(m) {
    for (auto &kv : ctx.get_pred_transformers()) {
        kv.m_value->extract_nums(m_consts);
    }
}

void lemma_expand_bnd_generalizer::operator()(lemma_ref &lemma) {
    scoped_watch _w_(m_st.watch);
    if (lemma->get_pob()->expand_bnd()) {
        // try expanding cvx bounds
        expr_ref_vector conj = lemma->get_cube();
        expr_ref_vector expand_expr(m), updt_conj(conj);
        expr *num, *term;
        expr_ref nw_bnd(m);
        for (unsigned i = 0; i < conj.size(); i++) {
            expr_ref bnd(conj.get(i), m);
            if ((m_arith.is_le(bnd, term, num) ||
                 m_arith.is_ge(bnd, term, num)) &&
                m_arith.is_numeral(num)) {
                TRACE("expand_bnd_verb",
                      tout << "bnd is " << mk_pp(bnd, m) << "\n";);
                expand_expr.reset();
                for (expr *t : updt_conj)
                    if (t != bnd.get()) expand_expr.push_back(t);
                if (expand_bnd(lemma, bnd, expand_expr, nw_bnd)) {
                    updt_conj.erase(bnd.get());
                    // It is possible that the bnd was not required at all
                    if (nw_bnd.get() != nullptr) updt_conj.push_back(nw_bnd);
                }
            }
        }
        lemma->get_pob()->stop_expand_bnd();
    }
}
void lemma_expand_bnd_generalizer::substitute(expr_ref var, rational n,
                                              expr_ref fml, expr_ref &sub) {
    expr_safe_replace s(m);
    sub.reset();
    s.insert(var, m_arith.mk_numeral(n, n.is_int()));
    s(fml, sub);
}

bool lemma_expand_bnd_generalizer::expand_bnd(lemma_ref &lemma, expr_ref lit,
                                              expr_ref_vector &conj,
                                              expr_ref &nw_bnd) {
    SASSERT(!conj.contains(lit));
    TRACE("expand_bnd", tout << "Expanding bounds of " << conj
                             << " with literal " << mk_pp(lit, m) << "\n";);
    SASSERT(to_app(lit)->get_num_args() == 2);
    expr_ref num = expr_ref(to_app(lit)->get_arg(1), m);
    rational val;
    bool is_int = false;
    SASSERT(m_arith.is_numeral(num));
    m_arith.is_numeral(num, val, is_int);
    expr_ref n_lit(m);
    if (!is_int) return false;
    bool success = false;
    for (rational n : m_consts) {
        if (should_apply(lit, val, n)) {
            m_st.atmpts++;
            substitute(num, n, lit, n_lit);
            conj.push_back(n_lit);
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
                val = n;
                TRACE("expand_bnd", tout << "expand_bnd succeeded with " << n
                                         << " at level " << uses_level
                                         << "\n";);
                success = true;
                nw_bnd = n_lit;
                if (!conj.contains(n_lit.get())) {
                    // The bnd was dropped entirely
                    nw_bnd.reset();
                    return true;
                }
            }
            conj.pop_back();
        }
    }
    return success;
}

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
