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
} // namespace spacer
template class rewriter_tpl<spacer::term_ordered_rpp>;