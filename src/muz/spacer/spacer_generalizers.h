/*++
Copyright (c) 2017 Microsoft Corporation and Arie Gurfinkel

Module Name:

    spacer_generalizers.h

Abstract:

    Generalizer plugins.

Author:

    Nikolaj Bjorner (nbjorner) 2011-11-22.
    Arie Gurfinkel
Revision History:

--*/

#pragma once

#include "ast/arith_decl_plugin.h"
#include "muz/spacer/spacer_context.h"
#include "muz/spacer/spacer_convex_closure.h"

namespace spacer {

// can be used to check whether produced core is really implied by
// frame and therefore valid TODO: or negation?
class lemma_sanity_checker : public lemma_generalizer {
  public:
    lemma_sanity_checker(context &ctx) : lemma_generalizer(ctx) {}
    ~lemma_sanity_checker() override {}
    void operator()(lemma_ref &lemma) override;
};

/**
 * Boolean inductive generalization by dropping literals
 */
class lemma_bool_inductive_generalizer : public lemma_generalizer {

    struct stats {
        unsigned count;
        unsigned num_failures;
        stopwatch watch;
        stats() { reset(); }
        void reset() {
            count = 0;
            num_failures = 0;
            watch.reset();
        }
    };

    unsigned m_failure_limit;
    bool m_array_only;
    stats m_st;

  public:
    lemma_bool_inductive_generalizer(context &ctx, unsigned failure_limit,
                                     bool array_only = false)
        : lemma_generalizer(ctx), m_failure_limit(failure_limit),
          m_array_only(array_only) {}
    ~lemma_bool_inductive_generalizer() override {}
    void operator()(lemma_ref &lemma) override;

    void collect_statistics(statistics &st) const override;
    void reset_statistics() override { m_st.reset(); }
};

class unsat_core_generalizer : public lemma_generalizer {
    struct stats {
        unsigned count;
        unsigned num_failures;
        stopwatch watch;
        stats() { reset(); }
        void reset() {
            count = 0;
            num_failures = 0;
            watch.reset();
        }
    };

    stats m_st;

  public:
    unsat_core_generalizer(context &ctx) : lemma_generalizer(ctx) {}
    ~unsat_core_generalizer() override {}
    void operator()(lemma_ref &lemma) override;

    void collect_statistics(statistics &st) const override;
    void reset_statistics() override { m_st.reset(); }
};

class lemma_array_eq_generalizer : public lemma_generalizer {
  private:
    bool is_array_eq(ast_manager &m, expr *e);

  public:
    lemma_array_eq_generalizer(context &ctx) : lemma_generalizer(ctx) {}
    ~lemma_array_eq_generalizer() override {}
    void operator()(lemma_ref &lemma) override;
};

class lemma_eq_generalizer : public lemma_generalizer {
  public:
    lemma_eq_generalizer(context &ctx) : lemma_generalizer(ctx) {}
    ~lemma_eq_generalizer() override {}
    void operator()(lemma_ref &lemma) override;
};

class lemma_quantifier_generalizer : public lemma_generalizer {
    struct stats {
        unsigned count;
        unsigned num_failures;
        stopwatch watch;
        stats() { reset(); }
        void reset() {
            count = 0;
            num_failures = 0;
            watch.reset();
        }
    };

    ast_manager &m;
    arith_util m_arith;
    stats m_st;
    expr_ref_vector m_cube;

    bool m_normalize_cube;
    int m_offset;

  public:
    lemma_quantifier_generalizer(context &ctx, bool normalize_cube = true);
    ~lemma_quantifier_generalizer() override {}
    void operator()(lemma_ref &lemma) override;

    void collect_statistics(statistics &st) const override;
    void reset_statistics() override { m_st.reset(); }

  private:
    bool generalize(lemma_ref &lemma, app *term);

    void find_candidates(expr *e, app_ref_vector &candidate);
    bool is_ub(var *var, expr *e);
    bool is_lb(var *var, expr *e);
    void mk_abs_cube(lemma_ref &lemma, app *term, var *var,
                     expr_ref_vector &gnd_cube, expr_ref_vector &abs_cube,
                     expr *&lb, expr *&ub, unsigned &stride);

    bool match_sk_idx(expr *e, app_ref_vector const &zks, expr *&idx, app *&sk);
    void cleanup(expr_ref_vector &cube, app_ref_vector const &zks,
                 expr_ref &bind);

    bool find_stride(expr_ref_vector &c, expr_ref &pattern, unsigned &stride);
};

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

    ast_manager &m;
    arith_util m_arith;
    stats m_st;
    convex_closure m_cvx_cls;
    // save fresh constants for mbp
    app_ref_vector m_dim_frsh_cnsts;
    expr_ref_vector m_dim_vars;
    bool m_exact;
    // solver to get model for computing mbp and to check whether cvx_cls ==>
    // mbp
    ref<solver> m_solver;
    bool subsume(lemma_cluster lc, lemma_ref &l, expr_ref_vector &res);

  public:
    lemma_global_generalizer(context &ctx);
    ~lemma_global_generalizer() override {}
    void operator()(lemma_ref &lemma) override;
    void collect_statistics(statistics &st) const override;
    void reset_statistics() override { m_st.reset(); }

  private:
    // TODO: define state independent functions somewhere else
    bool core(lemma_ref &lemma);

    // create new vars to compute convex cls
    void add_dim_vars(const lemma_cluster &lc);

    // mark frsh constants as to_real
    void rewrite_frsh_cnsts();

    // collect substituted numerals from cluster and add to m_cvx_cls
    void add_int_points(const lemma_cluster &lc);

    // reset state
    void reset(unsigned n_vars);

    // replaces vars with uninterpreted constants in fml
    void var_to_const(expr *fml, expr_ref &rw_fml);

    // rewrite all uninterpreted constants in e to real
    void to_real(const expr_ref_vector &e, expr_ref &rw_e);

    // rewrite all uninterpreted constants in e to real
    void to_real(expr_ref &fml);

    // convert reals to ints by multiplying with lcm of denominators
    void normalize(expr_ref &fml);

    // get lcm of all the denominators of all the rational values in e
    rational get_lcm(expr *e);

    // converts all numerals and uninterpreted constants in fml to int
    // assumes that fml is in sop
    void to_int(expr_ref &fml);
};

class limit_num_generalizer : public lemma_generalizer {

    struct stats {
        unsigned count;
        unsigned num_failures;
        stopwatch watch;
        stats() { reset(); }
        void reset() {
            count = 0;
            num_failures = 0;
            watch.reset();
        }
    };

    unsigned m_failure_limit;
    stats m_st;

    bool limit_denominators(expr_ref_vector &lits, rational &limit);

  public:
    limit_num_generalizer(context &ctx, unsigned failure_limit);
    ~limit_num_generalizer() override {}

    void operator()(lemma_ref &lemma) override;

    void collect_statistics(statistics &st) const override;
    void reset_statistics() override { m_st.reset(); }
};
} // namespace spacer

