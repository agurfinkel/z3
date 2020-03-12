/*

  Suite of global guidance strategies.

*/
#include "ast/arith_decl_plugin.h"
#include "ast/ast_util.h"
#include "ast/for_each_expr.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "model/model2expr.h"
#include "muz/spacer/spacer_context.h"
#include "muz/spacer/spacer_generalizers.h"
#include "muz/spacer/spacer_manager.h"
#include "muz/spacer/spacer_matrix.h"
#include "muz/spacer/spacer_util.h"
#include "smt/smt_solver.h"

namespace spacer {
lemma_global_generalizer::lemma_global_generalizer(context &ctx)
    : lemma_generalizer(ctx), m(ctx.get_ast_manager()), m_arith(m),
      m_cvx_cls(m, ctx.use_sage()), m_dim_frsh_cnsts(m), m_dim_vars(m) {
    m_solver = mk_smt_solver(m, params_ref::get_empty(), symbol::null);
}

void lemma_global_generalizer::operator()(lemma_ref &lemma) {
    scoped_watch _w_(m_st.watch);
    core(lemma);
}

void lemma_global_generalizer::reset(unsigned n_vars) {
    // start convex closure computation
    m_cvx_cls.reset(n_vars);
    m_dim_vars.reset();
    m_dim_frsh_cnsts.reset();
    m_dim_frsh_cnsts.reserve(n_vars);
    m_dim_vars.reserve(n_vars);
    m_exact = true;
}

bool lemma_global_generalizer::core(lemma_ref &lemma) {
    lemma_cluster *pt_cls = (&*lemma->get_pob())->pt().clstr_match(lemma);
    if (pt_cls == nullptr) return false;

    // the lemma has not been added to the cluster yet since the lemma has not
    // been added to spacer yet. So we create a new, local, cluster and add the
    // lemma to it.
    lemma_cluster lc(*pt_cls);

    lc.add_lemma(lemma, true);

    const expr_ref &pattern = lc.get_pattern();

    TRACE(
        "global",
        tout << "Start global generalization of lemma : " << lemma->get_cube()
             << "\n Discovered cluster: " << pattern << "\n and lemmas ";
        for (const lemma_info &lemma
             : lc.get_lemmas()) {
            tout << "\n \t" << lemma.get_lemma()->get_cube();
        });
    if (has_nonlinear_var_mul(pattern, m)) {
        m_st.m_num_non_lin++;
        if (pt_cls->get_gas() == 0) {
            m_st.m_num_cls_ofg++;
            return false;
        }
        TRACE("global",
              tout << "Found non linear pattern. Marked to concretize \n";);
        lemma->get_pob()->set_concr_pat(pattern);
        lemma->get_pob()->set_concretize();
        lemma->get_pob()->set_gas(lc.get_pob_gas());
        pt_cls->dec_gas();
        return false;
    }

    expr_ref lit(m);
    if (should_conjecture(pattern, lit)) {
        // Create a conjecture by dropping literal from pob.
        pob_ref n = lemma->get_pob();
        TRACE("global", tout << "Conjecture with pattern " << mk_pp(pattern, m)
                             << " with gas " << pt_cls->get_gas() << "\n";);

        expr_ref_vector conj(m);
        expr_ref n_pob = expr_ref(n->post(), m);
        expr_ref_vector fml_vec(m);
        fml_vec.push_back(n_pob);
        flatten_and(fml_vec);
        bool is_smaller = drop_lit(fml_vec, lit, conj);

        if (pt_cls->get_gas() == 0) m_st.m_num_cls_ofg++;

        if (conj.size() == 0 || pt_cls->get_gas() == 0) {
            // If the pob cannot be abstracted, stop using generalization on
            // it
            TRACE("global", tout << "stop local generalization on pob " << n_pob
                                 << " id is " << n_pob->get_id() << "\n";);

            n->stop_local_gen();
        } else if (!is_smaller) {
            // The literal to be abstracted is not in the pob
            TRACE("global", tout << "cannot conjecture on " << n_pob
                                 << " with lit " << lit << "\n";);
            // TODO: Should we stop local generalization at this point ?
            m_st.m_num_cant_abs++;
        } else {
            // There is enough gas to conjecture on pob
            n->set_conj_pattern(conj);
            n->set_may_pob_lvl(pt_cls->get_min_lvl() + 1);
            n->set_gas(pt_cls->get_pob_gas());
            pt_cls->dec_gas();
            TRACE("global", tout << "set conjecture " << conj << " at level "
                                 << n->get_may_pob_lvl() << "\n";);
        }
    }
    // TODO add subsume
    return false;
}

void lemma_global_generalizer::collect_statistics(statistics &st) const {
    st.update("time.spacer.solve.reach.gen.global", m_st.watch.get_seconds());
    st.update("SPACER cluster out of gas", m_st.m_num_cls_ofg);
    st.update("SPACER num sync cvx cls", m_st.m_num_syn_cls);
    st.update("SPACER num mbp failed", m_st.m_num_mbp_failed);
    st.update("SPACER num non lin", m_st.m_num_non_lin);
    st.update("SPACER num no over approximate", m_st.m_num_no_ovr_approx);
    st.update("SPACER num cant abstract", m_st.m_num_cant_abs);
    m_cvx_cls.collect_statistics(st);
}

} // namespace spacer
