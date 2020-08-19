#pragma once
/**++
Copyright (c) 2020 Arie Gurfinkel

Module Name:

    spacer_convex_closure.h

Abstract:

   Compute convex closure of polyhedra

Author:

    Hari Govind
    Arie Gurfinkel

Notes:

--*/

#include "ast/arith_decl_plugin.h"
#include "ast/ast.h"
#include "ast/ast_util.h"
#include "muz/spacer/spacer_arith_kernel.h"
#include "muz/spacer/spacer_matrix.h"
#include "muz/spacer/spacer_util.h"
#include "util/statistics.h"

namespace spacer {

class convex_closure {
    struct stats {
        unsigned m_num_reductions;
        unsigned m_max_dim;
        stopwatch watch;
        stats() { reset(); }
        void reset() {
            m_num_reductions = 0;
            m_max_dim = 0;
            watch.reset();
        }
    };
    stats m_st;

    ast_manager &m;
    arith_util m_arith;
    bv_util m_bv;

    // size of bit vectors in m_dim_vars are bv
    unsigned m_bv_sz;
    // true if m_dim_vars are int or real
    bool m_is_arith;

    // size of m_dim_vars
    unsigned m_dim;
    // vector of points
    spacer_matrix m_data;
    // dimension of m_data. Can be in LIA/LRA/BV
    var_ref_vector m_dim_vars;
    // stores kernel of m_data
    spacer_arith_kernel m_kernel;
    // vector of cnsts introduced by syntactic convex closure
    // always in LRA
    var_ref_vector m_nw_vars;

    /// least value such that m_lcm*m_data is an integer matrix
    rational m_lcm;

    // call m_kernel to reduce dimensions of m_data
    // return the rank of m_data
    unsigned reduce_dim();
    // construct linear equalities implied by m_data
    // the linear equalities are m_kernel * m_dim_vars = 0
    void generate_lin_deps(expr_ref_vector &res);

    /** Compute syntactic convex closure of m_data
        \Exists m_nw_vars s.t \Land_j Col_j \cdot m_nw_vars = m_dim_vars[j]
       \land \Sum j m_nw_vars[j] = 1 \land \forall j m_nw_vars[j] >= 0
    */
    void syn_cls(expr_ref_vector &res_vec);

    /// add (Col_j . m_nw_vars = m_dim_vars[j]) to res_vec
    void add_sum_cnstr(unsigned j, expr_ref_vector &res_vec);

    /// Compute one dimensional convex closure
    void do_one_dim_cls(expr_ref var, expr_ref_vector &res);

    // check whether \exists m, d s.t data[i] mod m = d. Returns the largest m
    // and corresponding d
    bool compute_div_constraint(const vector<rational> &data, rational &m,
                                rational &d);

    // construct the formula result_var <= bnd or result_var >= bnd
    expr *mk_ineq(expr_ref var, rational bnd, bool is_le);

  public:
    convex_closure(ast_manager &man, bool use_sage)
        : m(man), m_arith(m), m_bv(m), m_bv_sz(0), m_is_arith(true), m_dim(0),
          m_data(0, 0), m_dim_vars(m), m_kernel(m_data), m_nw_vars(m) {

        if (use_sage) m_kernel.set_plugin(mk_sage_plugin());
    }

    void reset(unsigned n_cols);

    /// turn on bv mod. set bv size
    void set_bv(unsigned sz) {
        SASSERT(sz > 0);
        m_is_arith = false;
        m_bv_sz = sz;
    }

    /// \brief Name a dimension by an expression
    void set_dimension(unsigned i, var *v) {
        SASSERT(i < dims());
        SASSERT(m_dim_vars[i] == nullptr);
        m_dim_vars[i] = v;
    }

    /// \brief Return number of dimensions of each point
    unsigned dims() const { return m_dim; }

    /// get consts introduced by syntactic convex closure
    const var_ref_vector &get_nw_vars() const { return m_nw_vars; }

    /// \brief add one-dimensional point
    void push_back(rational x) {
        SASSERT(dims() == 1);
        vector<rational> row;
        row.push_back(x);
        m_data.add_row(row);
    }

    /// \brief add two-dimensional point
    void push_back(rational x, rational y) {
        SASSERT(dims() == 2);
        vector<rational> row;
        row.push_back(x);
        row.push_back(y);
        m_data.add_row(row);
    }

    /// \brief add n-dimensional point
    void push_back(vector<rational> &point) {
        SASSERT(point.size() == dims());
        m_data.add_row(point);
    };

    /// \brief compute convex closure of current set of points
    /// return true if it was possible to compute the closure
    bool closure(expr_ref_vector &res);
    void collect_statistics(statistics &st) const;
    void reset_statistics() { m_st.reset(); }

    /// AG: COMMENT
    void set_lcm(rational l) { m_lcm = l; }
};
} // namespace spacer
