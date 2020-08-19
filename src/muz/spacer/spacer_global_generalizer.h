#pragma once
/*++
Copyright (c) 2020 Arie Gurfinkel

Module Name:

  spacer_global_generalizer.h

Abstract:

  Global Guidance for Spacer

Author:

  Hari Govind V K
  Arie Gurfinkel


--*/

#include "muz/spacer/spacer_context.h"
#include "muz/spacer/spacer_convex_closure.h"

namespace spacer {

class lemma_global_generalizer : public lemma_generalizer {
    struct stats {
        unsigned m_num_cls_ofg;
        unsigned m_num_syn_cls;
        unsigned m_num_mbp_failed;
        unsigned m_num_non_lin;
        unsigned m_num_no_ovr_approx;
        unsigned m_num_cant_abs;

        stopwatch watch;
        stats() { reset(); }
        void reset() {
            watch.reset();
            m_num_cls_ofg = 0;
            m_num_non_lin = 0;
            m_num_syn_cls = 0;
            m_num_mbp_failed = 0;
            m_num_no_ovr_approx = 0;
            m_num_cant_abs = 0;
        }
    };
    stats m_st;

    ast_manager &m;
    arith_util m_arith;
    array_util m_array;
    bv_util m_bv;

    // convex closure interface
    convex_closure m_cvx_cls;
    // save fresh constants for mbp
    app_ref_vector m_dim_frsh_cnsts;
    // save vars from cluster pattern
    var_ref_vector m_dim_vars;

    // solver to get model for computing mbp and to check whether
    // cvx_cls  ==> mbp
    ref<solver> m_solver;

    /// Compute a cube \p res that subsumes lemmas in \p lc
    /// lemma \p l is required in case lemma bindings are to be updated
    bool subsume(lemma_cluster lc, lemma_ref &l, expr_ref_vector &res);

    /// Skolemize fresh variables that appear under array select
    ///
    /// If all \p m_dim_frsh_cnsts appear inside array selects in \p f,
    /// skolemize them Newly created skolem constants are added to \p cnsts
    bool skolemize_sel_vars(expr_ref &f, app_ref_vector &cnsts);

    /// Decide global guidance based on lemma
    bool core(lemma_ref &lemma);

    /// Create new vars to compute convex cls
    void add_dim_vars(const lemma_cluster &lc);

    /// Coerce LIA constants in \p m_dim_frsh_cnsts to LRA constants
    /// AG: needs better name
    void rewrite_fresh_cnsts();

    /// Populate \p m_cvx_cls
    ///
    /// 1. Collect all substitutions in the cluster \p lc
    /// 2. Convert all substitutions to integer numerals
    void populate_cvx_cls(const lemma_cluster &lc);

    void reset(unsigned n_vars);

    /// Replace bound vars in \p fml with uninterpreted constants
    /// AG: isn't this just ground?
    void var_to_const(expr *fml, expr_ref &rw_fml);

  public:
    lemma_global_generalizer(context &ctx);
    ~lemma_global_generalizer() override {}
    void operator()(lemma_ref &lemma) override;
    void collect_statistics(statistics &st) const override;
    void reset_statistics() override { m_st.reset(); }
};
} // namespace spacer
