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
    // TODO add actions
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
