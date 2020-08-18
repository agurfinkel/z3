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

#pragma once
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
    expr_ref_vector m_dim_vars;

    // solver to get model for computing mbp and to check whether cvx_cls ==>
    // mbp
    ref<solver> m_solver;

    // compute a lemma that subsumes lemmas in lc
    bool subsume(lemma_cluster lc, lemma_ref &l, expr_ref_vector &res);

    // if all m_dim_frsh_cnsts appear inside array selects in f, skolemize them
    // append new constants to cnsts
    bool skolemize_sel_vars(expr_ref &f, app_ref_vector &cnsts);

    // decide global guidance based on lemma
    bool core(lemma_ref &lemma);

    // create new vars to compute convex cls
    void add_dim_vars(const lemma_cluster &lc);

    // convert all LIA constants in m_dim_frsh_cnsts to LRA constants using
    // to_real
    void rewrite_frsh_cnsts();

    // populate m_cvx_cls by 1) collecting all substitutions in the cluster lc
    // 2) converting them to integer numerals
    void populate_cvx_cls(const lemma_cluster &lc);

    // reset state
    void reset(unsigned n_vars);

    // replace vars with uninterpreted constants in fml
    void var_to_const(expr *fml, expr_ref &rw_fml);

    // rewrite all uninterpreted constants in e to real
    void to_real(const expr_ref_vector &e, expr_ref &rw_e);

    // rewrite all uninterpreted constants in fml to real
    void to_real(expr_ref &fml);

    // convert reals to ints in fml by multiplying with lcm of denominators
    void normalize(expr_ref &fml);

    // get lcm of all the denominators of all the rational values in e
    rational get_lcm(expr *e);

    // converts all numerals and uninterpreted constants in fml to int
    // assumes that fml is in sop
    void to_int(expr_ref &fml);

  public:
    lemma_global_generalizer(context &ctx);
    ~lemma_global_generalizer() override {}
    void operator()(lemma_ref &lemma) override;
    void collect_statistics(statistics &st) const override;
    void reset_statistics() override { m_st.reset(); }
};
} // namespace spacer
