#include "muz/spacer/spacer_convex_closure.h"

namespace spacer {
bool convex_closure::is_int_points() const {
    rational val;
    for (unsigned i = 0; i < m_data.num_rows(); i++) {
        for (unsigned j = 0; j < m_data.num_cols(); j++)
            if (!m_data.get(i, j).is_int()) return false;
    }
    return true;
}
void convex_closure::collect_statistics(statistics &st) const {
    st.update("time.spacer.solve.reach.gen.global.cvx_cls",
              m_st.watch.get_seconds());
    st.update("SPACER num dim reduction success", m_st.m_num_reductions);
    st.update("SPACER max cvx reduced dim", m_st.m_max_dim);
    m_kernel->collect_statistics(st);
}
unsigned convex_closure::reduce_dim() {
    if (m_dim <= 1) return m_dim;
    SASSERT(m_kernel != nullptr);
    bool non_null_ker = m_kernel->compute_kernel();
    if (!non_null_ker) {
        TRACE("cvx_dbg",
              tout << "No linear dependencies between pattern vars\n";);
        return m_dim;
    }
    const spacer_matrix &ker = m_kernel->get_kernel();

    SASSERT(ker.num_rows() > 0);
    SASSERT(ker.num_rows() <= m_dim);
    SASSERT(ker.num_cols() == m_dim + 1);
    // m_dim - ker.num_rows() is the number of variables that have no linear
    // dependencies
    return m_dim - ker.num_rows();
}

// for each row [0, 1, 0, 1 , 1], rewrite m_lcm*v1 = -1*m_lcm*v3 + -1*1
void convex_closure::rewrite_lin_deps() {
    const spacer_matrix &ker = m_kernel->get_kernel();
    unsigned n_rows = ker.num_rows();
    SASSERT(n_rows > 0);
    // index of the variable we are going to rewrite
    int pv = -1;
    // contains the right hand side of equality
    expr_ref_vector rw(m);
    // are we constructing rhs or lhs
    bool rhs = false;
    expr_ref_vector temp(m_dim_vars);
    // start generating equalities from bottom row
    for (unsigned i = n_rows; i > 0; i--) {

        const vector<rational> &row = ker.get_row(i - 1);
        // reset everything
        rw.reset();
        pv = -1;
        rhs = false;
        rational coeff(1);
        for (unsigned j = 0; j < row.size(); j++) {
            rational val = row.get(j);
            SASSERT(j >= i - 1 || val.is_zero());
            SASSERT(val.is_int());
            if (!val.is_zero()) {
                if (!rhs) {
                    // Cannot re-write the last dim
                    if (j == row.size() - 1) continue;
                    SASSERT(pv == -1);
                    pv = j;
                    rhs = true;
                    // In integer echelon form, the pivot need not be 1
                    if (val != 1) coeff = val;
                } else {
                    expr_ref prod(m);
                    if (j != row.size() - 1)
                        mul_if_not_one(-1 * val * m_lcm, m_dim_vars[j].get(),
                                       prod);
                    else if (m_is_arith)
                        prod = m_arith.mk_int(-1 * val);
                    else
                        prod = m_bv.mk_numeral(-1*val, m_bv_sz);
                    rw.push_back(prod);
                }
            }
        }

        // make sure that there is a non-zero entry
        SASSERT(pv != -1);

        if (rw.size() == 0) {
            if (m_is_arith)
                temp[pv] = m_arith.mk_eq(m_dim_vars[pv].get(),
                                     m_arith.mk_int(rational::zero()));
            else
                temp[pv] = m.mk_eq(m_dim_vars[pv].get(), m_bv.mk_numeral(rational::zero(), m_bv_sz));
            continue;
        }

        expr_ref rw_term(m);
        rw_term = m_is_arith ? m_arith.mk_add(rw.size(), rw.c_ptr()):  m.mk_app(m_bv.get_fid(), OP_BADD, rw.size(), rw.c_ptr());
        expr_ref pv_var(m);
        mul_if_not_one(coeff * m_lcm, m_dim_vars[pv].get(), pv_var);

        rw_term = m.mk_eq(pv_var, rw_term);
        TRACE("cvx_dbg", tout << "rewrote " << mk_pp(m_dim_vars[pv].get(), m)
                              << " into " << rw_term << "\n";);
        temp[pv] = rw_term;
    }

    // copy temp back to m_dim_vars
    m_dim_vars.reset();
    for (auto t : temp) m_dim_vars.push_back(t);
}

void convex_closure::add_lin_deps(expr_ref_vector &res_vec) {
    expr *lhs, *rhs;
    for (auto v : m_dim_vars) {
        if (m.is_eq(v, lhs, rhs)) {
            SASSERT(lhs != rhs);
            res_vec.push_back(expr_ref(v, m));
        }
    }
    TRACE("cvx_dbg", tout << "Linear equalities true of the matrix "
                          << mk_and(res_vec) << "\n";);
}

void convex_closure::add_sum_cnstr(unsigned i, expr_ref_vector &res_vec) {
    expr_ref_vector add(m);
    expr_ref mul(m), result_var(m), exp(m);
    for (unsigned j = 0; j < m_nw_vars.size(); j++) {
        exp = to_expr(m_nw_vars.get(j));
        mul_if_not_one(m_data.get(j, i), exp.get(), mul);
        add.push_back(mul);
    }
    mul_if_not_one(m_lcm, m_dim_vars[i].get(), result_var);
    if (m_is_arith)
        res_vec.push_back(
            m.mk_eq(m_arith.mk_add(add.size(), add.c_ptr()), result_var));
    else
        res_vec.push_back(m.mk_eq(m.mk_app(m_bv.get_fid(), OP_BADD, add.size(), add.c_ptr()), result_var));
}

void convex_closure::syn_cls(expr_ref_vector &res_vec) {
    for (unsigned i = 0; i < m_data.num_rows(); i++) {
        var_ref v(m.mk_var(i + dims(), m_arith.mk_real()), m);
        m_nw_vars.push_back(v);
    }

    expr_ref_vector exprs(m);
    expr_ref e(m);

    //\forall j . m_nw_vars[j] >= 0
    for (auto v : m_nw_vars) {
        e = expr_ref(to_expr(v), m);
        exprs.push_back(e);
        res_vec.push_back(m_arith.mk_ge(e, m_arith.mk_int(rational::zero())));
    }

    for (unsigned i = 0; i < m_dim_vars.size(); i++) {
        e = m_dim_vars[i].get();
        if (is_var(e)) add_sum_cnstr(i, res_vec);
    }

    //(\Sum j . m_nw_vars[j]) = 1
    res_vec.push_back(m.mk_eq(m_arith.mk_add(m_nw_vars.size(), exprs.c_ptr()),
                              m_arith.mk_int(rational::one())));
}

namespace {
bool is_sorted(const vector<rational> &data) {
    for (unsigned i = 0; i < data.size() - 1; i++) {
        if (data[i] < data[i + 1]) return false;
    }
    return true;
}
//check whether elements are congruent modulo m
bool congruent_mod(const vector<rational> &data, rational m) {
    rational p = data[0] % m;
    for(auto k : data)
        if (k % m != p) return false;
    return true;
}
} // namespace
// check whether \exists m, d s.t data[i] mod m = d. Returns the largest m and
// corresponding d
// TODO: find the largest divisor, not the smallest.
// TODO: improve efficiency
bool convex_closure::compute_div_constraint(const vector<rational> &data,
                                            rational &m, rational &d) {
    TRACE("cvx_dbg_verb", tout << "computing div constraints for ";
          for (rational r
               : data) tout
          << r << " ";
          tout << "\n";);
    SASSERT(data.size() > 1);
    SASSERT(is_sorted(data));
    m = rational(2);
    // hard cut off to save time
    rational bnd(100);
    for (; m < data[data.size() - 1] && m < bnd; m++) {
        if (congruent_mod(data, m)) break;
    }
    if (m >= data[data.size() - 1]) return false;
    d = data[0] % m;
    // work around for z3::rational::rem returning negative numbers.
    d = (m + d) % m;
    SASSERT(d >= rational::zero());

    TRACE("cvx_dbg_verb", tout << "div constraint generated. cf " << m << " and off " << d << "\n";);
    return true;
}

// returns whether the closure is exact or not (i.e syntactic)
bool convex_closure::closure(expr_ref_vector &res_vec) {
    scoped_watch _w_(m_st.watch);
    SASSERT(is_int_points());
    unsigned red_dim = reduce_dim();
    // store dim var before rewrite
    expr_ref var(m);
    var = m_dim_vars[0].get();
    if (red_dim < dims()) {
        m_st.m_num_reductions++;
        rewrite_lin_deps();
        add_lin_deps(res_vec);
    }

    if (red_dim > m_st.m_max_dim) m_st.m_max_dim = red_dim;
    if (red_dim > 1) {
        SASSERT(m_nw_vars.size() == 0);
        TRACE("subsume", tout << "Computing syntactic convex closure\n";);
        // syn_cls(res_vec);
        return false;
    }

    // zero dimensional convex closure
    if (red_dim == 0) { return true; }

    SASSERT(red_dim == 1);
    do_one_dim_cls(var, res_vec);
    return true;
}

expr* convex_closure::mk_ineq(expr_ref result_var, rational bnd, bool is_le) {
    if (m_is_arith) {
        if (is_le)
            return m_arith.mk_le(result_var, m_arith.mk_int(bnd));
        return m_arith.mk_ge(result_var, m_arith.mk_int(bnd));
    }
    //TODO figure out whether we need signed versions or unsigned versions.
    if (is_le)
        return m_bv.mk_ule(result_var, m_bv.mk_numeral(bnd, m_bv_sz));
    return m_bv.mk_ule(m_bv.mk_numeral(bnd, m_bv_sz), result_var);
}
void convex_closure::do_one_dim_cls(expr_ref var, expr_ref_vector &res_vec) {
    // The convex closure over one dimension is just a bound
    vector<rational> data;
    m_data.get_col(0, data);
    std::sort(
        data.begin(), data.end(),
        [](rational const &x, rational const &y) -> bool { return x > y; });

    expr_ref ub_expr(m), lb_expr(m), result_var(m);
    mul_if_not_one(m_lcm, var, result_var);
    ub_expr = mk_ineq(result_var, data[0], true);
    lb_expr = mk_ineq(result_var, data[data.size() - 1], false);

    rational cr, off;
    expr_ref v(m);
    // add div constraints for all variables.
    for (unsigned j = 0; j < m_data.num_cols(); j++) {
        v = m_dim_vars.get(j);
        if (is_var(v) && (m_arith.is_int(v) || m_bv.is_bv(v))) {
            data.reset();
            m_data.get_col(j, data);
            std::sort(data.begin(), data.end(),
                      [](rational const &x, rational const &y) -> bool {
                          return x > y;
                      });
            if (compute_div_constraint(data, cr, off)) {
                mul_if_not_one(m_lcm, v, result_var);
                if (m_is_arith)
                    res_vec.push_back(m_arith.mk_eq(
                                          m_arith.mk_mod(result_var, m_arith.mk_int(cr)),
                                          m_arith.mk_int(off)));
                else
                    res_vec.push_back(m.mk_eq(m_bv.mk_bv_urem(result_var, m_bv.mk_numeral(cr, m_bv_sz)), m_bv.mk_numeral(off, m_bv_sz)));
            }
        }
    }
    res_vec.push_back(ub_expr);
    res_vec.push_back(lb_expr);
}

} // namespace spacer
