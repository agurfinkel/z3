#include "ast/arith_decl_plugin.h"
#include "ast/ast.h"
#include "ast/ast_pp.h"
#include "ast/for_each_expr.h"
#include "ast/rewriter/rewriter.h"
#include "ast/rewriter/rewriter_def.h"
#include "ast/rewriter/th_rewriter.h"
#include "muz/spacer/spacer_util.h"

namespace spacer {
// 2 non-mul terms are compared according to their ids
// non-mul term < mul term
// if both are mul, the ids of second arguments are compared
struct arith_add_less_proc {
    arith_util &m_arith;

    arith_add_less_proc(arith_util &arith) : m_arith(arith) {}

    bool operator()(expr *e1, expr *e2) const {
        ast_lt_proc ast_lt;

        expr *k1 = nullptr, *t1 = nullptr, *k2 = nullptr, *t2 = nullptr;
        if (!m_arith.is_mul(e1, k1, t1)) { t1 = e1; }
        if (!m_arith.is_mul(e2, k2, t2)) { t2 = e2; }

        if (t1 == t2) {
            // null < anything
            if (!k1) return k1 != k2;
            // k2 == null, k1 is not less than k2
            else if (!k2)
                return false;
            // fall back
            else
                return ast_lt(k1, k2);
        } else {
            return ast_lt(t1, t2);
        }
    }
};

struct bool_and_less_proc {
    ast_manager &m;
    arith_util m_arith;
    bool_and_less_proc(ast_manager &mgr, arith_util &arith)
        : m(mgr), m_arith(arith) {}

    // if e1 == e2, e1 < e2
    // 2 non arithmetic terms are compared according to id
    // non arithmetic term < arithmetic term
    // negation is ignored when comparing 2 arithmetic terms
    // compare lhs:
    // if both are vars, compare id
    // vars < non vars
    // two apps are compared using their leading uninterpreted constant
    // no uninterpreted constant < uninterpreted constant
    // if they are the same, id of lhs is used
    // a < not a
    bool operator()(expr *e1, expr *e2) const {
        expr *a1 = nullptr, *a2 = nullptr;
        bool is_not1, is_not2;
        is_not1 = m.is_not(e1, a1);
        a1 = is_not1 ? a1 : e1;
        is_not2 = m.is_not(e2, a2);
        a2 = is_not2 ? a2 : e2;

        if (a1 == a2) return is_not1 < is_not2;
        return arith_lt(a1, a2);
    }

    bool arith_lt(expr *e1, expr *e2) const {
        ast_lt_proc ast_lt;
        expr *t1, *k1, *t2, *k2;

        if (e1 == e2) return false;

        if (!(m_arith.is_le(e1, t1, k1) || m_arith.is_lt(e1, t1, k1) ||
              m_arith.is_ge(e1, t1, k1) || m_arith.is_gt(e1, t1, k1))) {
            t1 = e1;
            k1 = nullptr;
        }
        if (!(m_arith.is_le(e2, t2, k2) || m_arith.is_lt(e2, t2, k2) ||
              m_arith.is_ge(e2, t2, k2) || m_arith.is_gt(e2, t2, k2))) {
            t2 = e2;
            k2 = nullptr;
        }

        if (!k1 || !k2) {
            if (k1 == k2) return ast_lt(t1, t2);
            // either k1 or k2 are nullptr
            return k1 < k2;
        }

        if (t1 == t2) return ast_lt(k1, k2);

        if (!(is_app(t1) && is_app(t2))) {
            if (is_app(t1) == is_app(t2)) return ast_lt(t1, t2);
            return is_app(t1) < is_app(t2);
        }

        unsigned d1 = to_app(t1)->get_depth();
        unsigned d2 = to_app(t2)->get_depth();
        if (d1 != d2) return d1 < d2;

        // AG: order by the leading uninterpreted constant
        expr *u1 = nullptr, *u2 = nullptr;

        u1 = get_first_uc(t1);
        u2 = get_first_uc(t2);
        if (!u1 || !u2) {
            if (u1 == u2) return ast_lt(t1, t2);
            return u1 < u2;
        }

        return u1 == u2 ? ast_lt(t1, t2) : ast_lt(u1, u2);
    }

    /// intends to extract the first uninterpreted constant of an arithmetic
    /// expression return nullptr when no constant is found assumes input
    /// expression e is shallow and uses recursion depth of recursion is the
    /// depth of leftmost branch of ast
    expr *get_first_uc(expr *e) const {
        expr *t, *k;
        if (is_uninterp_const(e))
            return e;
        else if (m_arith.is_add(e)) {
            /// HG: never going to happen ?
            if (to_app(e)->get_num_args() == 0) return nullptr;
            expr *a1 = to_app(e)->get_arg(0);
            // HG: for 3 + a, returns nullptr
            return get_first_uc(a1);
        } else if (m_arith.is_mul(e, k, t)) {
            return get_first_uc(t);
        }
        return nullptr;
    }
};
// Rewriting arithmetic expressions based on term order
struct term_ordered_rpp : public default_rewriter_cfg {
    ast_manager &m;
    arith_util m_arith;
    arith_add_less_proc m_add_less;
    bool_and_less_proc m_and_less;

    term_ordered_rpp(ast_manager &man)
        : m(man), m_arith(m), m_add_less(m_arith), m_and_less(m, m_arith) {}

    bool is_add(func_decl const *n) const {
        return is_decl_of(n, m_arith.get_family_id(), OP_ADD);
    }

    br_status reduce_app(func_decl *f, unsigned num, expr *const *args,
                         expr_ref &result, proof_ref &result_pr) {
        br_status st = BR_FAILED;

        if (is_add(f)) {
            ptr_buffer<expr> v;
            v.append(num, args);
            std::stable_sort(v.c_ptr(), v.c_ptr() + v.size(), m_add_less);
            result = m_arith.mk_add(num, v.c_ptr());
            return BR_DONE;
        }

        if (m.is_and(f)) {
            ptr_buffer<expr> v;
            v.append(num, args);
            std::stable_sort(v.c_ptr(), v.c_ptr() + v.size(), m_and_less);
            result = m.mk_and(num, v.c_ptr());
            return BR_DONE;
        }
        return st;
    }
};

void normalize_order(expr *e, expr_ref &out) {
    params_ref params;
    // arith_rewriter
    params.set_bool("sort_sums", true);
    // params.set_bool("gcd_rounding", true);
    // params.set_bool("arith_lhs", true);
    // poly_rewriter
    // params.set_bool("som", true);
    // params.set_bool("flat", true);

    // apply rewriter
    th_rewriter rw(out.m(), params);
    rw(e, out);

    STRACE("spacer_normalize_order'",
           tout << "OUT Before:" << mk_pp(out, out.m()) << "\n";);
    term_ordered_rpp t_ordered(out.m());
    rewriter_tpl<term_ordered_rpp> t_ordered_rw(out.m(), false, t_ordered);
    t_ordered_rw(out.get(), out);
    STRACE("spacer_normalize_order'",
           tout << "OUT After :" << mk_pp(out, out.m()) << "\n";);
}
// TODO: this is broken for real expressions. Fix it as needed.
bool normalize_to_le(expr *lit, expr_ref &t, expr_ref &c) {
    expr *e0 = nullptr, *e1 = nullptr, *e2 = nullptr;
    rational n;
    bool is_int = true;
    ast_manager &m = t.get_manager();
    arith_util m_arith(m);
    if (m_arith.is_le(lit, e1, e2) ||
        (m.is_not(lit, e0) && m_arith.is_gt(e0, e1, e2))) {
        t = e1;
        c = e2;
        if (m_arith.is_numeral(e2, n))
            return true;
        else
            return false;
    } else if (m_arith.is_lt(lit, e1, e2) ||
               (m.is_not(lit, e0) && m_arith.is_ge(e0, e1, e2))) {
        // x < k  ==> x <= (k-1)
        t = e1;
        if (m_arith.is_numeral(e2, n, is_int)) {
            c = m_arith.mk_numeral(n - 1, is_int);
            return true;
        } else {
            c = m_arith.mk_add(e2, m_arith.mk_int(-1));
            return false;
        }
    } else if (m_arith.is_gt(lit, e1, e2) ||
               (m.is_not(lit, e0) && m_arith.is_le(e0, e1, e2))) {
        // x > k ==> -x < -k ==> -x <= -k - 1
        t = e1;
        mul_and_simp(t, rational::minus_one());
        if (m_arith.is_numeral(e2, n, is_int)) {
            c = m_arith.mk_numeral(-n - 1, is_int);
            return true;
        } else {
            expr_ref temp(m);
            temp = e2;
            mul_and_simp(temp, rational::minus_one());
            expr_ref minus_one(m);
            minus_one = m_arith.mk_numeral(rational(-1), is_int);
            c = m_arith.mk_add(temp, minus_one);
            return false;
        }
    } else if (m_arith.is_ge(lit, e1, e2) ||
               (m.is_not(lit, e0) && m_arith.is_lt(e0, e1, e2))) {
        // x >= k ==> -x <= -k
        t = e1;
        mul_and_simp(t, rational::minus_one());
        if (m_arith.is_numeral(e2, n, is_int)) {
            c = m_arith.mk_numeral(-n, is_int);
            return true;
        } else {
            c = e2;
            mul_and_simp(c, rational::minus_one());
            return false;
        }
    }
    return false;
}
void mul_and_simp(expr_ref &fml, rational num) {
    ast_manager &m = fml.get_manager();
    array_util m_array(m);
    arith_util m_arith(m);
    TRACE("global", tout << fml << "\n";);
    SASSERT(m_arith.is_arith_expr(fml) || is_var(fml) ||
            is_uninterp_const(fml) || m_array.is_select(fml));
    if (num.is_one()) return;

    if (is_uninterp_const(fml) || is_var(fml) || m_array.is_select(fml)) {
        fml = m_arith.mk_mul(m_arith.mk_numeral(num, num.is_int()), fml);
        return;
    }
    rational val;
    if (m_arith.is_numeral(fml, val)) {
        val = val * num;
        fml = m_arith.mk_numeral(val, val.is_int());
        return;
    }
    app *fml_app = to_app(fml);
    unsigned N = fml_app->get_num_args();
    expr_ref_vector nw_args(m);
    for (unsigned i = 0; i < N; i++) {
        expr *chld = fml_app->get_arg(i);
        if (m_arith.is_mul(chld)) {
            expr_ref numeral(to_app(chld)->get_arg(0), m);
            rational val;
            SASSERT(m_arith.is_numeral(numeral));
            m_arith.is_numeral(numeral, val);
            rational nw_coeff = val * num;
            expr_ref nw_prd(m);
            mul_if_not_one(nw_coeff, to_app(chld)->get_arg(1), nw_prd);
            nw_args.push_back(nw_prd);
        } else {
            nw_args.push_back(
                m_arith.mk_mul(m_arith.mk_numeral(num, num.is_int()), chld));
        }
    }
    fml = m.mk_app(fml_app->get_family_id(), fml_app->get_decl_kind(),
                   nw_args.size(), nw_args.c_ptr());
}

void mul_if_not_one(rational coeff, expr *e, expr_ref &res) {
    ast_manager &m = res.get_manager();
    arith_util m_arith(m);
    if (coeff == rational::one())
        res = expr_ref(e, m);
    else
        res = m_arith.mk_mul(m_arith.mk_numeral(coeff, coeff.is_int()), e);
}
namespace extract_nums_ns {
struct extract_nums_proc {
    ast_manager &m;
    arith_util m_arith;
    vector<rational> &m_res;
    extract_nums_proc(ast_manager &a_m, vector<rational> &res)
        : m(a_m), m_arith(m), m_res(res) {}
    void operator()(expr *n) const {}
    void operator()(app *n) {
        rational val;
        if (m_arith.is_numeral(n, val) && !m_res.contains(val))
            m_res.push_back(val);
    }
};
} // namespace extract_nums_ns

// WARNING: run time is number of nodes in e * res.size !!!
// TODO: use sets to speed things up ?
void extract_nums(expr_ref e, vector<rational> &res) {
    extract_nums_ns::extract_nums_proc t(e.get_manager(), res);
    for_each_expr(t, e);
}
} // namespace spacer
template class rewriter_tpl<spacer::term_ordered_rpp>;
