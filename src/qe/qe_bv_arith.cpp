/*++
Copyright (c) 2020

Module Name:

    qe_bv_arith.cpp

Abstract:

    Simple projection function for integer linear arithmetic

Author:

    Arie Gurfinkel
    Grigory Fedyukovich
    Hari Govind V K
Revision History:

--*/

#include "qe/qe_bv_arith.h"
#include "ast/ast_pp.h"
#include "ast/ast_util.h"
#include "ast/bv_decl_plugin.h"
#include "ast/expr_abstract.h"
#include "ast/for_each_expr.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "ast/rewriter/rewriter.h"
#include "ast/rewriter/rewriter_def.h"
#include "ast/rewriter/th_rewriter.h"
#include "cmd_context/cmd_context.h"
#include "qe/qe_mbp.h"
#include "smt/smt_solver.h"

namespace qe {
typedef std::pair<unsigned, unsigned> bnd;
namespace extrt_bnds_ns {
struct extrt_bnds {
    ast_manager &m;
    bv_util m_bv;
    expr_ref m_var;
    vector<bnd> &m_bnds;
    extrt_bnds(ast_manager &a_m, expr *var, vector<bnd> &bnds)
        : m(a_m), m_bv(m), m_var(var, m), m_bnds(bnds) {
        m_bnds.reset();
    }
    void operator()(expr *n) const {}
    void operator()(app *n) {
        expr *b;
        unsigned lw, hh;
        if (m_bv.is_extract(n, lw, hh, b) && m_var == b) {
            bnd nw_bnd(lw, hh);
            if (!m_bnds.contains(nw_bnd)) m_bnds.push_back(nw_bnd);
        }
    }
};
} // namespace extrt_bnds_ns

void get_extrt_bnds(expr *var, expr_ref e, vector<bnd> &bnds) {
    bnds.reset();
    extrt_bnds_ns::extrt_bnds t(e.get_manager(), var, bnds);
    for_each_expr(t, e);
    if (bnds.size() == 0) return;
    bv_util m_bv(e.get_manager());
    unsigned sz = m_bv.get_bv_size(var);
    bnd full(0, sz - 1);
    bnds.push_back(full);
    CTRACE("bv_tmp", bnds.size() > 0,
           tout << "extracted bnds " << e << " for var "
                << mk_pp(var, e.get_manager()) << " " << bnds.size() << "\n";);
}
// check whether r overlaps with any bnd in bnds
bool does_overlap(vector<bnd> &bnds, bnd r) {
    for (bnd t : bnds) {
        if (r.second > t.second && t.first <= r.first && r.first <= t.second)
            return true;
        if (r.first < t.first && t.first <= r.second && r.second <= t.second)
            return true;
    }
    return false;
}

unsigned get_lw_point(vector<bnd> &bnds) {
    unsigned min = bnds[0].first;
    for (auto b : bnds) {
        if (b.first < min) { min = b.first; }
    }
    return min;
}

unsigned get_hg_point(vector<bnd> &bnds) {
    unsigned max = bnds[0].second;
    for (auto b : bnds) {
        if (b.second > max) { max = b.second; }
    }
    return max;
}
// ip: a vector of overlapping bounds some of which could be subsets of others
// op: the smallest vector of disjoint bounds whose union is the same range as
// bnds and each range in bnds can be expressed as union of ranges in nw_bnds
void collapse_bnds(vector<bnd> &bnds, vector<bnd> &nw_bnds) {
    unsigned lw = get_lw_point(bnds);
    unsigned hg = get_hg_point(bnds);
    unsigned i = lw, j = lw;
    nw_bnds.reset();
    while (i <= hg) {
        bnd b(i, j);
        if (does_overlap(bnds, b)) {
            b.second = j - 1;
            nw_bnds.push_back(b);
            i = j;
        } else
            j++;
    }
    TRACE("bv_tmp", for (auto b
                         : bnds) tout
                        << b << " ";
          tout << "\n new bnd"; for (auto b
                                     : nw_bnds) tout
                                << b << " ";);
}

bool contains(expr *e, expr *v) {
    if (e == v) return true;
    for (expr *arg : *to_app(e))
        if (contains(arg, v)) return true;
    return false;
}

void mk_mul(expr *a, expr *b, expr_ref &c) {
    ast_manager &m(c.get_manager());
    bv_util m_bv(m);
    rational av, bv;
    if (m_bv.is_numeral(a, av) && m_bv.is_numeral(b, bv)) {
        rational cv = av * bv;
        unsigned sz = m_bv.get_bv_size(a);
        c = m_bv.mk_numeral(cv, sz);
        return;
    }
    c = m_bv.mk_bv_mul(a, b);
}
void mk_add(expr_ref_vector &f, expr_ref &res) {
    ast_manager &m = res.get_manager();
    bv_util m_bv(m);
    if (f.size() == 0) return;
    expr_ref_vector nw_args(m);
    rational sm = rational::zero(), val;
    unsigned sz = 0;
    for (auto a : f) {
        if (m_bv.is_numeral(a, val)) {
            sz = m_bv.get_bv_size(a);
            sm = sm + val;
        } else
            nw_args.push_back(a);
    }
    if (!sm.is_zero()) {
        expr_ref sm_bv(m);
        sm_bv = m_bv.mk_numeral(sm, sz);
        nw_args.push_back(sm_bv);
    }
    if (nw_args.size() == 1)
        res = nw_args.get(0);
    else
        res =
            m.mk_app(m_bv.get_fid(), OP_BADD, nw_args.size(), nw_args.c_ptr());
    th_rewriter rw(m);
    rw(res);
}
void mk_neg(expr *f, expr_ref &res) {
    ast_manager &m = res.get_manager();
    bv_util m_bv(m);
    rational val;
    expr *t1, *t2 = nullptr;
    const unsigned sz = m_bv.get_bv_size(f);
    rational bnd = rational::power_of_two(sz) - 1;

    if (m_bv.is_numeral(f, val)) {
        if (val == rational::zero())
            res = f;
        else {
            rational neg = rational::power_of_two(sz) - val;
            res = m_bv.mk_numeral(neg, sz);
        }
    } else if (m_bv.is_bv_neg(f))
        res = (to_app(f)->get_arg(0));
    else if (m_bv.is_bv_mul(f, t1, t2)) {
        if (m_bv.is_numeral(t1, val) && val == bnd)
            res = t2;
        else if (m_bv.is_numeral(t2, val) && val == bnd)
            res = t1;
        else
            res = m_bv.mk_bv_neg(f);
    } else if (m_bv.is_bv_add(f)) {
        expr_ref_vector tmp(m);
        expr_ref tmp1(m);
        for (auto arg : *(to_app(f))) {
            mk_neg(arg, tmp1);
            tmp.push_back(tmp1);
        }
        mk_add(tmp, res);
    } else
        res = m_bv.mk_bv_mul(m_bv.mk_numeral(bnd, sz), f);
}
void flatten_term(expr *t, expr_ref &res) {
    ast_manager &m = res.get_manager();
    bv_util m_bv(m);
    expr *neg;
    if (m_bv.is_bv_neg(t)) {
        neg = to_app(t)->get_arg(0);
        if (m_bv.is_bv_neg(neg)) {
            res = to_app(neg)->get_arg(0);
            return;
        }
        if (m_bv.is_numeral(neg)) {
            mk_neg(neg, res);
            return;
        }
    }
    res = t;
    return;
}
void flatten_add(expr *t1, expr_ref_vector &res) {
    ast_manager &m = res.get_manager();
    bv_util m_bv(m);
    if (t1 == nullptr) return;
    if (!m_bv.is_bv_add(t1)) {
        res.push_back(t1);
        return;
    }
    rational val, sum = rational::zero();
    unsigned sz = m_bv.get_bv_size(t1);
    expr_ref flt(m);
    for (auto arg : *(to_app(t1))) {
        flatten_term(arg, flt);
        if (m_bv.is_numeral(flt, val))
            sum = sum + val;
        else
            res.push_back(flt);
    }
    if (!sum.is_zero()) res.push_back(m_bv.mk_numeral(sum, sz));
}

void mk_add(expr *t1, expr *t2, expr_ref &res) {
    expr_ref_vector f(res.get_manager());
    flatten_add(t1, f);
    flatten_add(t2, f);
    mk_add(f, res);
}

bool unhandled(expr *f, expr *var, ast_manager &m) {
    bv_util u(m);
    SASSERT(contains(f, var));
    if (is_uninterp(f)) return false;
    if (u.is_bv_sdiv(f) || u.is_bv_udiv(f)) return true;
    if (u.is_bv_smod(f) || u.is_bv_smodi(f) || u.is_bv_smod0(f)) return true;
    if (u.is_bv_urem(f) || u.is_bv_urem0(f) || u.is_bv_uremi(f)) return true;
    if (u.is_extract(f) || u.is_concat(f)) return true;
    for (auto a : *(to_app(f))) {
        if (!contains(a, var)) continue;
        return unhandled(a, var, m);
    }
    return false;
}
bool split(expr *e, expr *var, expr_ref &t1, expr_ref &t2) {
    ast_manager &m(t2.get_manager());
    bv_util m_bv(m);
    if (!m_bv.is_bv_add(e) || !contains(e, var)) return false;
    expr_ref_vector nw_args(m);
    for (expr *arg : *to_app(e)) {
        if (contains(arg, var))
            t1 = arg;
        else
            nw_args.push_back(arg);
    }
    if (nw_args.size() == 0) return false;
    mk_add(nw_args, t2);
    return true;
}
bool split_exl(expr *e, expr *var, expr_ref &t1, expr_ref &t2) {
    ast_manager &m(t2.get_manager());
    bv_util m_bv(m);
    if (!m_bv.is_bv_add(e) || !contains(e, var)) return false;
    expr_ref_vector nw_args(m);
    for (expr *arg : *to_app(e)) {
        if (contains(arg, var))
            t2 = arg;
        else
            nw_args.push_back(arg);
    }
    if (nw_args.size() == 0) return false;
    mk_add(nw_args, t1);
    return true;
}

class rw_rule {
  protected:
    ast_manager &m;
    model_ref m_mdl;
    expr_ref m_var;
    bv_util m_bv;
    bool is_ule_one_side(expr *e, expr_ref &lhs, expr_ref &rhs) {
        if (!m_bv.is_bv_ule(e)) return false;
        lhs = to_app(e)->get_arg(0);
        rhs = to_app(e)->get_arg(1);
        if (contains(lhs, m_var) == contains(rhs, m_var)) return false;
        return true;
    }
    bool is_ule(expr *e, expr_ref &lhs, expr_ref &rhs) {
        if (!m_bv.is_bv_ule(e)) return false;
        lhs = to_app(e)->get_arg(0);
        rhs = to_app(e)->get_arg(1);
        if (!contains(lhs, m_var) && !contains(rhs, m_var)) return false;
        return true;
    }
    bool is_sle(expr *e, expr_ref &lhs, expr_ref &rhs) {
        if (!m_bv.is_bv_sle(e)) return false;
        lhs = to_app(e)->get_arg(0);
        rhs = to_app(e)->get_arg(1);
        if (contains(lhs, m_var) == contains(rhs, m_var)) return false;
        return true;
    }

  public:
    rw_rule(ast_manager &m) : m(m), m_var(m), m_bv(m) {}
    void reset(model *mdl, expr *x) {
        m_var = x;
        m_mdl = mdl;
    }
    virtual bool apply(expr *exp, expr_ref_vector &out) = 0;
};

class sle1 : public rw_rule {
    // a <= 2^(n - 1) - 1 && b <= 2^(n - 1) - 1 && a <= b ==> a <=_s b
  public:
    sle1(ast_manager &m) : rw_rule(m) {}
    bool apply(expr *e, expr_ref_vector &out) override {
        expr_ref lhs(m), rhs(m);
        if (!is_sle(e, lhs, rhs)) return false;
        unsigned sz = m_bv.get_bv_size(m_var);
        expr_ref bnd(m), b1(m), b2(m), rw(m);
        bnd = m_bv.mk_numeral(rational::power_of_two(sz - 1) - 1, sz);
        b1 = m_bv.mk_ule(lhs, bnd);
        b2 = m_bv.mk_ule(rhs, bnd);
        rw = m_bv.mk_ule(lhs, rhs);
        if (m_mdl->is_true(b1) && m_mdl->is_true(b2) && m_mdl->is_true(rw)) {
            out.push_back(b1);
            out.push_back(b2);
            out.push_back(rw);
            return true;
        }
        return false;
    }
};

class sle2 : public rw_rule {
    // a >= 2^(n - 1) && b >= 2^(n - 1) && a <= b ==> a <=_s b
  public:
    sle2(ast_manager &m) : rw_rule(m) {}
    bool apply(expr *e, expr_ref_vector &out) override {
        expr_ref lhs(m), rhs(m);
        if (!is_sle(e, lhs, rhs)) return false;
        unsigned sz = m_bv.get_bv_size(m_var);
        expr_ref bnd(m), b1(m), b2(m), rw(m);
        bnd = m_bv.mk_numeral(rational::power_of_two(sz - 1), sz);
        b1 = m_bv.mk_ule(bnd, lhs);
        b2 = m_bv.mk_ule(bnd, rhs);
        rw = m_bv.mk_ule(lhs, rhs);
        if (m_mdl->is_true(b1) && m_mdl->is_true(b2) && m_mdl->is_true(rw)) {
            out.push_back(b1);
            out.push_back(b2);
            out.push_back(rw);
            return true;
        }
        return false;
    }
};

class sle3 : public rw_rule {
    // a >= 2^(n - 1) && b <= 2^(n - 1) - 1 ==> a <=_s b
  public:
    sle3(ast_manager &m) : rw_rule(m) {}
    bool apply(expr *e, expr_ref_vector &out) override {
        expr_ref lhs(m), rhs(m);
        if (!is_sle(e, lhs, rhs)) return false;
        unsigned sz = m_bv.get_bv_size(m_var);
        expr_ref bnd1(m), b1(m), b2(m), bnd2(m);
        bnd1 = m_bv.mk_numeral(rational::power_of_two(sz - 1) - 1, sz);
        bnd2 = m_bv.mk_numeral(rational::power_of_two(sz - 1), sz);
        b1 = m_bv.mk_ule(bnd2, lhs);
        b2 = m_bv.mk_ule(rhs, bnd1);
        if (m_mdl->is_true(b1) && m_mdl->is_true(b2)) {
            out.push_back(b1);
            out.push_back(b2);
            return true;
        }
        return false;
    }
};

class eq : public rw_rule {
    // a <= b && b <= a ==> a = b
  public:
    eq(ast_manager &m) : rw_rule(m) {}
    bool apply(expr *e, expr_ref_vector &out) override {
        expr *lhs, *rhs;
        expr_ref b1(m), b2(m);
        if (!(m.is_eq(e, lhs, rhs) &&
              (contains(lhs, m_var) || contains(rhs, m_var))))
            return false;
        b1 = m_bv.mk_ule(rhs, lhs);
        b2 = m_bv.mk_ule(lhs, rhs);
        if (m_mdl->is_true(b1) && m_mdl->is_true(b2)) {
            out.push_back(b1);
            out.push_back(b2);
            return true;
        }
        return false;
    }
};

class neq1 : public rw_rule {
    // a < b ==> a != b
  public:
    neq1(ast_manager &m) : rw_rule(m) {}
    bool apply(expr *e, expr_ref_vector &out) override {
        expr *f, *lhs, *rhs;
        if (!(m.is_not(e, f) && m.is_eq(f, lhs, rhs) &&
              (contains(lhs, m_var) || contains(rhs, m_var))))
            return false;
        expr_ref b1(m);
        b1 = m.mk_not(m_bv.mk_ule(rhs, lhs));
        if (m_mdl->is_true(b1)) {
            out.push_back(b1);
            return true;
        }
        return false;
    }
};

class neq2 : public rw_rule {
    // a > b ==> a != b
  public:
    neq2(ast_manager &m) : rw_rule(m) {}
    bool apply(expr *e, expr_ref_vector &out) override {
        expr *f, *lhs, *rhs;
        if (!((m.is_not(e, f)) && m.is_eq(f, lhs, rhs) &&
              (contains(lhs, m_var) || contains(rhs, m_var))))
            return false;
        expr_ref b1(m), nt(m);
        nt = m_bv.mk_ule(lhs, rhs);
        b1 = m.mk_not(nt);
        if (m_mdl->is_true(b1)) {
            out.push_back(b1);
            return true;
        }
        return false;
    }
};

class nule : public rw_rule {
    // b <= a - 1 /\ 1 <= a ==> not(a <= b)
  public:
    nule(ast_manager &m) : rw_rule(m) {}
    bool apply(expr *e, expr_ref_vector &out) override {
        expr *f, *lhs, *rhs;
        if (!((m.is_not(e, f)) && m_bv.is_bv_ule(f, lhs, rhs) &&
              (contains(lhs, m_var) || contains(rhs, m_var))))
            return false;
        unsigned sz = m_bv.get_bv_size(m_var);
        expr_ref mone(m), dff(m), one(m);
        one = m_bv.mk_numeral(rational::one(), sz);
        mk_neg(one, mone);
        mk_add(lhs, mone, dff);
        expr *b1 = m_bv.mk_ule(rhs, dff);
        expr *b2 = m_bv.mk_ule(one, lhs);
        if (m_mdl->is_true(b1) && m_mdl->is_true(b2)) {
            out.push_back(b1);
            out.push_back(b2);
            return true;
        }
        return false;
    }
};

class nsle : public rw_rule {
    // b <=_s a - 1 /\ -2^(n - 1) + 1 <=_s a ==> not(a <=_s b)
  public:
    nsle(ast_manager &m) : rw_rule(m) {}
    bool apply(expr *e, expr_ref_vector &out) override {
        expr *f, *lhs, *rhs;
        if (!((m.is_not(e, f)) && m_bv.is_bv_sle(f, lhs, rhs) &&
              (contains(lhs, m_var) || contains(rhs, m_var))))
            return false;
        unsigned sz = m_bv.get_bv_size(m_var);
        expr_ref bnd(m);
        bnd = m_bv.mk_numeral((-1 * rational::power_of_two(sz - 1)) + 1, sz);
        expr_ref mone(m), dff(m), b1(m), b2(m);
        mone = m_bv.mk_numeral(rational::minus_one(), sz);
        mk_add(lhs, mone, dff);
        b1 = m_bv.mk_sle(bnd, lhs);
        b2 = m_bv.mk_sle(rhs, dff);
        if (m_mdl->is_true(b1) && m_mdl->is_true(b2)) {
            out.push_back(b1);
            out.push_back(b2);
            return true;
        }
        return false;
    }
};

class mul_mone1 : public rw_rule {
    //-1*b <= a ==> -1*a <= b
  public:
    mul_mone1(ast_manager &m) : rw_rule(m) {}
    bool apply(expr *e, expr_ref_vector &out) override {
        expr_ref lhs(m), rhs(m), nw_lhs(m);
        expr *l1, *l2;
        rational val;
        if (!is_ule_one_side(e, lhs, rhs)) return false;
        if (!(contains(lhs, m_var) && m_bv.is_bv_mul(lhs, l1, l2) &&
              l2 == m_var))
            return false;
        unsigned sz = m_bv.get_bv_size(m_var);
        if (!(m_bv.is_numeral(l1, val) &&
              (val.is_minus_one() || (val == rational::power_of_two(sz) - 1))))
            return false;
        mk_mul(l1, rhs, nw_lhs);
        expr_ref b1(m);
        b1 = m_bv.mk_ule(nw_lhs, l2);
        if (m_mdl->is_true(b1)) {
            out.push_back(b1);
            return true;
        }
        return false;
    }
};

class mul_mone2 : public rw_rule {
    // a <= -1*b ==> b <= -1*a
  public:
    mul_mone2(ast_manager &m) : rw_rule(m) {}
    bool apply(expr *e, expr_ref_vector &out) override {
        expr_ref lhs(m), rhs(m), nw_rhs(m);
        expr *l1, *l2;
        rational val;
        if (!is_ule_one_side(e, lhs, rhs)) return false;
        if (!(contains(rhs, m_var) && m_bv.is_bv_mul(rhs, l1, l2) &&
              l2 == m_var))
            return false;
        unsigned sz = m_bv.get_bv_size(m_var);
        if (!(m_bv.is_numeral(l1, val) &&
              (val.is_minus_one() || (val == rational::power_of_two(sz) - 1))))
            return false;
        mk_mul(l1, lhs, nw_rhs);
        expr_ref b1(m);
        b1 = m_bv.mk_ule(l2, nw_rhs);
        if (m_mdl->is_true(b1)) {
            out.push_back(b1);
            return true;
        }
        return false;
    }
};

class ule_zro : public rw_rule {
    // b = 0 ==> b <= x
  public:
    ule_zro(ast_manager &m) : rw_rule(m) {}
    bool apply(expr *e, expr_ref_vector &out) override {
        expr_ref lhs(m);
        rational val;
        if (!m_bv.is_bv_ule(e)) return false;
        lhs = to_app(e)->get_arg(0);

        if (m_bv.is_numeral(lhs, val) && val.is_zero()) return true;
        return false;
    }
};

class addl1 : public rw_rule {
    // if {y <= z /\ f(x) <= z - y} then {f(x) + y <= z}
  public:
    addl1(ast_manager &m) : rw_rule(m) {}
    bool apply(expr *e, expr_ref_vector &out) override {
        expr_ref lhs(m), rhs(m), oth(m), rw(m);
        if (!is_ule_one_side(e, lhs, rhs)) return false;
        expr_ref t1(m), t2(m), t2_neg(m), add_t(m);
        if (!split(lhs, m_var, t1, t2)) return false;
        mk_neg(t2, t2_neg);
        oth = m_bv.mk_ule(t2, rhs);
        mk_add(rhs, t2_neg, add_t);
        rw = m_bv.mk_ule(t1, add_t);
        if (m_mdl->is_true(oth) && m_mdl->is_true(rw)) {
            out.push_back(oth);
            out.push_back(rw);
            return true;
        }
        return false;
    };
};

class addl2 : public rw_rule {
    // if {-y <= f(x) /\ f(x) <= z - y} then {f(x) + y <= z}
  public:
    addl2(ast_manager &m) : rw_rule(m) {}
    bool apply(expr *e, expr_ref_vector &out) override {
        expr_ref lhs(m), rhs(m), oth(m), rw(m);
        if (!is_ule_one_side(e, lhs, rhs)) return false;
        expr_ref t1(m), t2(m), t2_neg(m), add_t(m);
        if (!split(lhs, m_var, t1, t2)) return false;
        mk_neg(t2, t2_neg);
        oth = m_bv.mk_ule(t2_neg, t1);
        mk_add(rhs, t2_neg, add_t);
        rw = m_bv.mk_ule(t1, add_t);
        if (m_mdl->is_true(oth) && m_mdl->is_true(rw)) {
            out.push_back(oth);
            out.push_back(rw);
            return true;
        }
        return false;
    };
};

class addl3 : public rw_rule {
    // if {-y <= f(x) /\ y <= z /\ y != 0} then {f(x) + y <= z}
  public:
    addl3(ast_manager &m) : rw_rule(m) {}
    bool apply(expr *e, expr_ref_vector &out) override {
        expr_ref lhs(m), rhs(m), sc1(m), sc2(m), zro(m), sc3(m);
        if (!is_ule_one_side(e, lhs, rhs)) return false;
        expr_ref t1(m), t2(m), t2_neg(m), add_t(m);
        if (!split(lhs, m_var, t1, t2)) return false;
        mk_neg(t2, t2_neg);
        sc1 = m_bv.mk_ule(t2_neg, t1);
        sc2 = m_bv.mk_ule(t2, rhs);
        unsigned sz = m_bv.get_bv_size(m_var);
        zro = m_bv.mk_numeral(rational::zero(), sz);
        sc3 = m.mk_not(m.mk_eq(t2, zro));
        if (m_mdl->is_true(sc1) && m_mdl->is_true(sc2) && m_mdl->is_true(sc3)) {
            out.push_back(sc1);
            out.push_back(sc2);
            out.push_back(sc3);
            return true;
        }
        return false;
    };
};

class addbx4 : public rw_rule {
    // if {x <= 2^n/k2/k1} then {k1*x <= k2*x}
    // TODO: handle other cases as well
  public:
    addbx4(ast_manager &m) : rw_rule(m) {}
    bool apply(expr *e, expr_ref_vector &out) override {
        expr_ref lhs(m), rhs(m), nw_rhs(m), bnd_e(m), sc1(m);
        if (!is_ule(e, lhs, rhs)) return false;
        expr *k1_e, *k2_e, *var;
        rational k1, k2;
        if (!m_bv.is_bv_mul(lhs, k1_e, var)) return false;
        if (var != m_var) return false;
        if (!m_bv.is_numeral(k1_e, k1)) return false;

        if (!m_bv.is_bv_mul(rhs, k2_e, var)) return false;
        if (var != m_var) return false;
        if (!m_bv.is_numeral(k2_e, k2)) return false;
        if (k1 == k2) return true;
        rational k3 = k2 / k1;
        unsigned sz = m_bv.get_bv_size(m_var);
        rational bnd = rational::power_of_two(sz) / k3;
        bnd_e = m_bv.mk_numeral(bnd, sz);
        sc1 = m_bv.mk_ule(m_var, bnd_e);
        if (m_mdl->is_true(sc1)) {
            out.push_back(sc1);
            return true;
        }
        TRACE("bv_tmp", tout << "model not good enough for bx4 "
                             << mk_pp(sc1, m) << "\n";);
        return false;
    };
};

class addbx1 : public rw_rule {
    // if {f1(x) <= f2(x) /\ y <= f2(x) - f1(x)} then {f1(x) + y <= f2(x)}
  public:
    addbx1(ast_manager &m) : rw_rule(m) {}
    bool apply(expr *e, expr_ref_vector &out) override {
        expr_ref lhs(m), rhs(m), nw_rhs(m), sc1(m), rw(m);
        if (!is_ule(e, lhs, rhs)) return false;
        expr_ref t1(m), t2(m), t2_neg(m), add_t(m);
        if (!split_exl(lhs, m_var, t1, t2)) return false;
        mk_neg(t2, t2_neg);
        sc1 = m_bv.mk_ule(t2, rhs);
        mk_add(rhs, t2_neg, nw_rhs);
        rw = m_bv.mk_ule(t1, nw_rhs);
        TRACE("bv_tmp", tout << "checking mdl bx1 with " << mk_pp(sc1, m)
                             << " and " << mk_pp(rw, m) << "\n";);
        if (m_mdl->is_true(sc1) && m_mdl->is_true(rw)) {
            out.push_back(sc1);
            out.push_back(rw);
            return true;
        }
        TRACE("bv_tmp", tout << "checking mdl bx1 with " << mk_pp(sc1, m)
                             << " and " << mk_pp(rw, m) << "\n";);
        return false;
    };
};

class addbx2 : public rw_rule {
    // if {-f1(x) <= y /\ y <= f2(x) - f1(x)} then {f1(x) + y <= f2(x)}
  public:
    addbx2(ast_manager &m) : rw_rule(m) {}
    bool apply(expr *e, expr_ref_vector &out) override {
        expr_ref lhs(m), rhs(m), nw_rhs(m), rw(m), sc1(m);
        if (!is_ule(e, lhs, rhs)) return false;
        expr_ref t1(m), t2(m), t2_neg(m), add_t(m);
        if (!split_exl(lhs, m_var, t1, t2)) return false;
        mk_neg(t2, t2_neg);
        sc1 = m_bv.mk_ule(t2_neg, t1);
        mk_add(rhs, t2_neg, nw_rhs);
        rw = m_bv.mk_ule(t1, nw_rhs);
        TRACE("bv_tmp", tout << "checking mdl bx2 with " << mk_pp(sc1, m)
                             << " and " << mk_pp(rw, m) << "\n";);
        if (m_mdl->is_true(sc1) && m_mdl->is_true(rw)) {
            out.push_back(sc1);
            out.push_back(rw);
            return true;
        }
        return false;
    };
};

class addbx3 : public rw_rule {
    // if {-f1(x) <= y /\ f1(x) <= f2(x) /\ f1(x) != 0} then {f1(x) + y <=
    // f2(x)}
  public:
    addbx3(ast_manager &m) : rw_rule(m) {}
    bool apply(expr *e, expr_ref_vector &out) override {
        expr_ref lhs(m), rhs(m), nw_rhs(m), sc1(m), sc2(m), sc3(m), zro(m);
        if (!is_ule(e, lhs, rhs)) return false;
        expr_ref t1(m), t2(m), t2_neg(m), add_t(m);
        if (!split_exl(lhs, m_var, t1, t2)) return false;
        mk_neg(t2, t2_neg);
        sc1 = m_bv.mk_ule(t2_neg, t1);
        sc2 = m_bv.mk_ule(t2, rhs);
        unsigned sz = m_bv.get_bv_size(m_var);
        zro = m_bv.mk_numeral(rational::zero(), sz);
        sc3 = m.mk_not(m.mk_eq(t2, zro));

        TRACE("bv_tmp", tout << "checking mdl bx3 with " << mk_pp(sc1, m)
                             << " and " << mk_pp(sc2, m) << "\n";);
        if (m_mdl->is_true(sc1) && m_mdl->is_true(sc2) && m_mdl->is_true(sc3)) {
            out.push_back(sc1);
            out.push_back(sc2);
            out.push_back(sc3);
            return true;
        }
        return false;
    };
};

class addr1 : public rw_rule {
    // if {z <= y - 1 /\ y != 0 /\ z - y <= f(x)} then {z <= f(x) + y}
  public:
    addr1(ast_manager &m) : rw_rule(m) {}
    bool apply(expr *e, expr_ref_vector &out) override {
        expr_ref lhs(m), rhs(m);
        if (!is_ule(e, lhs, rhs)) return false;
        expr_ref t1(m), t2(m), t2_neg(m);
        if (!split(rhs, m_var, t1, t2)) return false;
        mk_neg(t2, t2_neg);
        unsigned sz = m_bv.get_bv_size(m_var);
        expr_ref one(m), minus_one(m), zro(m), add_t1(m), add_mo(m), oth(m),
            no_zro(m);
        one = m_bv.mk_numeral(rational::one(), sz);
        zro = m_bv.mk_numeral(rational::zero(), sz);
        mk_neg(one, minus_one);
        mk_add(t2, minus_one, add_mo);
        oth = m_bv.mk_ule(lhs, add_mo);
        no_zro = m.mk_not(m.mk_eq(t2, zro));
        mk_add(lhs, t2_neg, add_t1);
        expr *rw = m_bv.mk_ule(add_t1, t1);
        if (m_mdl->is_true(oth) && m_mdl->is_true(rw) &&
            m_mdl->is_true(no_zro)) {
            out.push_back(oth);
            out.push_back(no_zro);
            out.push_back(rw);
            return true;
        }
        return false;
    };
};

class addr2 : public rw_rule {
    // if { f(x) <= -y - 1 /\ y != 0  /\ z - y <= f(x)} then { z <= f(x) + y}
  public:
    addr2(ast_manager &m) : rw_rule(m) {}
    bool apply(expr *e, expr_ref_vector &out) override {
        expr_ref lhs(m), rhs(m);
        if (!is_ule(e, lhs, rhs)) return false;
        expr_ref t1(m), t2(m), t2_neg(m);
        if (!split(rhs, m_var, t1, t2)) return false;
        mk_neg(t2, t2_neg);
        unsigned sz = m_bv.get_bv_size(m_var);
        expr_ref one(m), minus_one(m), zro(m), add_t2(m), add_lhs(m), rw(m),
            oth(m), no_zro(m);
        one = m_bv.mk_numeral(rational::one(), sz);
        zro = m_bv.mk_numeral(rational::zero(), sz);
        mk_neg(one, minus_one);
        mk_add(t2_neg, minus_one, add_t2);
        oth = m_bv.mk_ule(t1, add_t2);
        no_zro = m.mk_not(m.mk_eq(t2, zro));
        mk_add(lhs, t2_neg, add_lhs);
        rw = m_bv.mk_ule(add_lhs, t1);
        if (m_mdl->is_true(oth) && m_mdl->is_true(rw) &&
            m_mdl->is_true(no_zro)) {
            out.push_back(oth);
            out.push_back(no_zro);
            out.push_back(rw);
            return true;
        }
        return false;
    };
};

class addr3 : public rw_rule {
    // if { y == 0  /\ z <= f(x)} then { z <= f(x) + y}
  public:
    addr3(ast_manager &m) : rw_rule(m) {}
    bool apply(expr *e, expr_ref_vector &out) override {
        expr_ref lhs(m), rhs(m);
        if (!is_ule(e, lhs, rhs)) return false;
        expr_ref t1(m), t2(m);
        if (!split(rhs, m_var, t1, t2)) return false;
        unsigned sz = m_bv.get_bv_size(m_var);
        expr_ref zro(m), oth(m), t2_zro(m);
        zro = m_bv.mk_numeral(rational::zero(), sz);
        oth = m_bv.mk_ule(lhs, t1);
        t2_zro = m.mk_eq(t2, zro);
        if (m_mdl->is_true(t2_zro) && m_mdl->is_true(oth)) {
            out.push_back(oth);
            out.push_back(t2_zro);
            return true;
        }
        return false;
    };
};

class addr4 : public rw_rule {
    // if { y != 0  /\ z <= y - 1 && x <= -y - 1 } then { z <= f(x) + y}
  public:
    addr4(ast_manager &m) : rw_rule(m) {}
    bool apply(expr *e, expr_ref_vector &out) override {
        expr_ref lhs(m), rhs(m);
        if (!is_ule(e, lhs, rhs)) return false;
        expr_ref t1(m), t2(m), t2_neg(m);
        if (!split(rhs, m_var, t1, t2)) return false;
        mk_neg(t2, t2_neg);
        unsigned sz = m_bv.get_bv_size(m_var);
        expr_ref one(m), zro(m), mone(m), add_t2(m), add_negt2(m), t2_zro(m),
            oth(m), oth2(m);
        zro = m_bv.mk_numeral(rational::zero(), sz);
        mone = m_bv.mk_numeral(rational::minus_one(), sz);
        mk_add(t2, mone, add_t2);
        mk_add(t2_neg, mone, add_negt2);
        t2_zro = m.mk_not(m.mk_eq(t2, zro));
        oth = m_bv.mk_ule(lhs, add_t2);
        oth2 = m_bv.mk_ule(t1, add_negt2);
        if (m_mdl->is_true(t2_zro) && m_mdl->is_true(oth) &&
            m_mdl->is_true(oth2)) {
            out.push_back(oth);
            out.push_back(oth2);
            out.push_back(t2_zro);
            return true;
        }
        return false;
    };
};

struct bv_ext_rw_cfg : public default_rewriter_cfg {
    ast_manager &m;
    bv_util m_bv;
    expr_ref m_var;
    app_ref_vector m_nw_vars;
    vector<bnd> m_bnds;
    bv_ext_rw_cfg(ast_manager &m, expr *v)
        : m(m), m_bv(m), m_var(v, m), m_nw_vars(m) {}
    void add_bnds(vector<bnd> &bnds, app_ref_vector &vars) {
        // creates a new variable for each [lb, ub] in bnds
        app_ref nw_var(m);
        for (unsigned i = 0; i < bnds.size(); i++) {
            unsigned sz = bnds[i].second - bnds[i].first + 1;
            nw_var = m.mk_fresh_const("extrt_elim", m_bv.mk_sort(sz));
            vars.push_back(nw_var);
            m_nw_vars.push_back(nw_var);
        }
        m_bnds.reset();
        m_bnds.append(bnds);
    }
    void register_nw_vars(model &mdl) {
        expr_ref rhs(m), lhs(m);
        for (unsigned i = 0; i < m_bnds.size(); i++) {
            rhs = m_bv.mk_extract(m_bnds[i].second, m_bnds[i].first, m_var);
            lhs = m_nw_vars.get(i);
            expr_ref val(m);
            val = mdl(rhs);
            mdl.register_decl(to_app(lhs)->get_decl(), val);
        }
        mdl.reset_eval_cache();
        return;
    }
    br_status reduce_app(func_decl *f, unsigned num, expr *const *args,
                         expr_ref &result, proof_ref &result_pr) {
        expr_ref_vector nw_args(m), rwt_args(m);
        if (m_bv.is_extract(f) && args[0] == m_var) {
            unsigned lw = m_bv.get_extract_low(f);
            unsigned hg = m_bv.get_extract_high(f);
            for (unsigned i = m_bnds.size(); i-- != 0;) {
                if (lw <= m_bnds[i].first && m_bnds[i].second <= hg)
                    nw_args.push_back(to_expr(m_nw_vars.get(i)));
            }
            if (nw_args.size() == 1) {
                result = nw_args.get(0);
                return BR_DONE;
            }
            result = m_bv.mk_concat(nw_args.size(), nw_args.c_ptr());
            return BR_DONE;
        }
        for (unsigned i = m_nw_vars.size(); i-- != 0;)
            rwt_args.push_back(to_expr(m_nw_vars.get(i)));
        expr_ref rwt(m);
        rwt = m_bv.mk_concat(rwt_args.size(), rwt_args.c_ptr());
        // rewrite all occurrences of m_var with nw_arg
        for (unsigned i = 0; i < num; i++) {
            if (args[i] == m_var)
                nw_args.push_back(rwt);
            else
                nw_args.push_back(args[i]);
        }
        result = m.mk_app(f, num, nw_args.c_ptr());
        return BR_DONE;
    }
};

struct bv_mbp_rw_cfg : public default_rewriter_cfg {
    model *m_mdl;
    ast_manager &m;
    expr_ref_vector &m_sc;
    bv_util m_bv;
    void add_model(model *model) { m_mdl = model; }
    bv_mbp_rw_cfg(ast_manager &m, expr_ref_vector &sc)
        : m(m), m_sc(sc), m_bv(m) {}

    bool rewrite_concat(expr *a, expr_ref &res, expr_ref &sc) {
        if (m_bv.is_bv_add(a)) {
            expr_ref a1(m), a1_neg(m), a2(m);
            a1 = to_app(a)->get_arg(0);
            a2 = to_app(a)->get_arg(1);
            rational n;
            expr_ref_vector nw_args(m);
            if (m_bv.is_concat(a2) && m_bv.is_numeral(a1, n)) {
                expr_ref a21(m), a22(m);
                for (unsigned i = 0; i < to_app(a2)->get_num_args() - 1; i++) {
                    nw_args.push_back(to_app(a2)->get_arg(i));
                }
                a22 = to_app(a2)->get_arg(to_app(a2)->get_num_args() - 1);
                unsigned dff = m_bv.get_bv_size(a22);
                if (n > rational::power_of_two(dff - 1) - 1 ||
                    n < -rational::power_of_two(dff - 1)) {
                    return false;
                }
                expr_ref t(m), t_res(m);
                t = m_bv.mk_numeral(n, dff);
                TRACE("bv_tmp",
                      tout << "a22 is " << a22 << " and " << t << "\n";);
                mk_add(a22, t, t_res);
                mk_neg(t, a1_neg);
                nw_args.push_back(t_res);
                sc = m_bv.mk_ule(a22, a1_neg);
                if (!m_mdl->is_true(sc)) {
                    res = m_bv.mk_concat(nw_args.size(), nw_args.c_ptr());
                    return true;
                }
            }
        }
        return false;
    }

    bool rewrite_bvneg(expr *a, expr_ref &res) {
        if (!m_bv.is_bv_neg(a)) return false;
        expr *b = to_app(a)->get_arg(0);
        mk_neg(b, res);
        return true;
    }
    br_status reduce_app(func_decl *f, unsigned num, expr *const *args,
                         expr_ref &result, proof_ref &result_pr) {
        expr_ref sc(m);
        expr_ref e(m);
        e = m.mk_app(f, num, args);
        if (rewrite_concat(e, result, sc)) {
            m_sc.push_back(sc);
            TRACE("bv_tmp", tout << "concat rewritten " << result << " and sc "
                                 << sc << "\n";);
            return BR_DONE;
        }
        if (rewrite_bvneg(e, result)) { return BR_DONE; }
        return BR_FAILED;
    }
};

struct bv_project_plugin::imp {
    ast_manager &m;
    bv_util bv;
    ptr_buffer<rw_rule> m_rw_rules;
    imp(ast_manager &_m) : m(_m), bv(m) {
        m_rw_rules.push_back(alloc(addl1, m));
        m_rw_rules.push_back(alloc(addl2, m));
        m_rw_rules.push_back(alloc(addl3, m));
        m_rw_rules.push_back(alloc(addr1, m));
        m_rw_rules.push_back(alloc(addr2, m));
        m_rw_rules.push_back(alloc(addr3, m));
        m_rw_rules.push_back(alloc(addr4, m));
        m_rw_rules.push_back(alloc(addbx1, m));
        m_rw_rules.push_back(alloc(addbx2, m));
        m_rw_rules.push_back(alloc(addbx3, m));
        m_rw_rules.push_back(alloc(addbx4, m));
        m_rw_rules.push_back(alloc(sle1, m));
        m_rw_rules.push_back(alloc(sle2, m));
        m_rw_rules.push_back(alloc(sle3, m));
        m_rw_rules.push_back(alloc(eq, m));
        m_rw_rules.push_back(alloc(neq1, m));
        m_rw_rules.push_back(alloc(neq2, m));
        m_rw_rules.push_back(alloc(nule, m));
        m_rw_rules.push_back(alloc(nsle, m));
        m_rw_rules.push_back(alloc(mul_mone1, m));
        m_rw_rules.push_back(alloc(mul_mone2, m));
        m_rw_rules.push_back(alloc(ule_zro, m));
    }
    ~imp() {
        for (auto *r : m_rw_rules) { dealloc(r); }
    }

    void reset_rw_rules(model &mdl, expr *var) {
        for (auto r : m_rw_rules) { r->reset(&mdl, var); }
    }
    // var is the only uninterpreted constant on one side of literal
    bool is_normalized(expr *b, expr *var) {
        if (!contains(b, var)) return true;
        if (unhandled(b, var, m)) return false;
        if (!bv.is_bv_ule(b)) return false;
        expr *chd = to_app(b)->get_arg(0);
        expr *o_chd = to_app(b)->get_arg(1);
        if (!contains(chd, var)) {
            chd = to_app(b)->get_arg(1);
            o_chd = to_app(b)->get_arg(0);
            if (!contains(chd, var)) return false;
        }
        if (contains(o_chd, var)) return false;
        // Coefficient should be one
        // TODO: handle cases when coefficient is not one
        if (chd == var) return true;
        return false;
    }

    bool normalize(expr *var, expr *f, model &mdl, expr_ref_vector &res) {
        expr_ref_vector todo(m);
        todo.push_back(f);
        reset_rw_rules(mdl, var);
        expr_ref_vector out(m);
        expr_ref t(m);
        while (!todo.empty()) {
            t = todo.back();
            bool normalized = false;
            if (is_normalized(t, var)) {
                res.push_back(t);
                todo.pop_back();
                continue;
            } else if (unhandled(t, var, m))
                return false;
            for (auto r : m_rw_rules) {
                out.reset();
                if (r->apply(t, out)) {
                    normalized = true;
                    todo.pop_back();
                    todo.append(out);
                    break;
                }
            }
            // t cannot be normalized
            if (!normalized) return false;
        }
        return true;
    }

    // MAIN PROJECTION FUNCTION
    // if compute_def is true, return witnessing definitions
    vector<def> project(model &model, app_ref_vector &vars,
                        expr_ref_vector &fmls, bool compute_def) {
        bool has_bv = false;
        for (expr *v : vars) { has_bv |= bv.is_bv(v); }
        if (!has_bv) { return vector<def>(); }
        expr_ref_vector res(m);
        res.append(fmls);
        for (unsigned var_num = 0; var_num < vars.size(); var_num++) {
            expr_ref v(vars.get(var_num), m);
            TRACE("bv_tmp", tout << "eliminate " << mk_pp(v, m) << "\n";);

            expr_ref_vector new_fmls(m), norm(m), backg_fmls(m), norm_fmls(m);
            expr_ref_vector pi(m), sig(m);

            for (unsigned f_num = 0; f_num < res.size(); f_num++) {
                expr_ref f(res.get(f_num), m);

                // background fmls
                if (!contains(f, v)) {
                    backg_fmls.push_back(f);
                    continue;
                }
                norm.reset();
                // normalize and add to sig
                if (normalize(v, f, model, norm)) {
                    TRACE("bv_tmp", tout << "Normalized " << f << " into "
                                         << mk_and(norm) << "\n";);
                    sig.push_back(f);
                    TRACE("qe", tout << "normalized from " << mk_pp(f, m)
                                     << " to " << mk_pp(mk_and(norm), m)
                                     << "\n";);
                    for (auto a : norm) {
                        // normalization can create side conditions not
                        // involving v
                        if (contains(a, v))
                            norm_fmls.push_back(a);
                        else
                            backg_fmls.push_back(a);
                    }
                    // sanity check. normalization should be an under
                    // approximation
                    SASSERT(is_sat((mk_and(norm), m.mk_not(f))));
                    // sanity check. model satisfies normalized formula
                    SASSERT(model.is_true(mk_and(norm)));
                } else {
                    TRACE("bv_tmp", tout << "Could not normalize " << f
                                         << " at var " << v << "\n";);
                    pi.push_back(f);
                }
            }
            expr_ref_vector bd_fmls(m);
            resolve(v, norm_fmls, model, new_fmls, bd_fmls);
            TRACE("bv_tmp",
                  tout << "Resolve produced " << mk_and(new_fmls) << "\n";);
            if (bd_fmls.size() > 0) {
                pi.append(bd_fmls);
                CTRACE("bv_tmp", bd_fmls.size() > 0,
                       tout << " could not resolve out " << mk_and(bd_fmls)
                            << " for var " << v << "\n";);
            }
            if (!pi.empty()) {
                TRACE("bv_tmp", tout << "calling lazy mbp with pi "
                                     << mk_and(pi) << " and sig " << mk_and(sig)
                                     << "\n";);
                lazy_mbp(backg_fmls, sig, pi, v, new_fmls, model);
            }
            res.reset();
            res.append(new_fmls);
            res.append(backg_fmls);
            TRACE("bv_tmp", tout << "eliminated " << mk_pp(v, m)
                                 << " result is " << mk_and(res) << "\n";);
            SASSERT(model.is_true(res));
        }
        return vector<def>();
    }

    void get_lbs(expr *var, expr_ref_vector &f, expr_ref_vector &lbs) {
        expr *lhs, *rhs;
        for (auto a : f) {
            if (contains(a, var)) {
                if (bv.is_bv_ule(a, lhs, rhs) && !contains(lhs, var) &&
                    contains(rhs, var))
                    lbs.push_back(a);
            }
        }
    }

    void get_ubs(expr *var, expr_ref_vector &f, expr_ref_vector &ubs) {
        expr *lhs, *rhs;
        for (auto a : f) {
            if (contains(a, var)) {
                if (bv.is_bv_ule(a, lhs, rhs) && contains(lhs, var) &&
                    !contains(rhs, var))
                    ubs.push_back(a);
            }
        }
    }

    rational get_coeff(expr *a, expr *var) {
        if (!contains(a, var)) return rational::zero();
        if (a == var) return rational::one();
        expr *t1, *t2;
        if (bv.is_bv_mul(a, t1, t2)) {
            rational o_coeff;
            SASSERT(bv.is_numeral(t1));
            bv.is_numeral(t1, o_coeff);
            return o_coeff * get_coeff(t2, var);
        }
        for (auto t : *to_app(a)) {
            if (contains(t, var)) return get_coeff(t, var);
        }
        return rational::zero();
    }

    // lcm of coefficients of var in f
    rational get_lcm(expr_ref_vector &f, expr *var) {
        rational l = rational::one();
        for (auto a : f) {
            rational c = get_coeff(a, var);
            l = lcm(l, c);
        }
        return l;
    }

    expr *find_glb(model &mdl, expr_ref_vector &lbs) {
        expr_ref res(m);
        expr *r = lbs.get(0);
        rational val, glb(0);
        mdl.eval_expr(to_app(lbs[0].get())->get_arg(0), res);
        if (!bv.is_numeral(res, glb)) return nullptr;
        for (auto a : lbs) {
            mdl.eval_expr(to_app(a)->get_arg(0), res);
            SASSERT(bv.is_numeral(res));
            if (bv.is_numeral(res, val) && glb < val) {
                r = a;
                glb = val;
            }
        }
        return r;
    }

    expr *find_lub(model &mdl, expr_ref_vector &ubs) {
        expr_ref res(m);
        expr *r = ubs.get(0);
        rational val, lub;
        mdl.eval_expr(to_app(ubs[0].get())->get_arg(1), res);
        if (!bv.is_numeral(res, lub)) return nullptr;
        for (auto a : ubs) {
            mdl.eval_expr(to_app(a)->get_arg(1), res);
            SASSERT(bv.is_numeral(res));
            if (bv.is_numeral(res, val) && lub > val) {
                r = a;
                lub = val;
            }
        }
        return r;
    }

    void mk_mul(expr *a, rational b, expr_ref &o) {
        rational val;
        if (b.is_one()) {
            o = a;
            return;
        }
        unsigned sz = bv.get_bv_size(a);
        if (bv.is_numeral(a, val)) {
            o = bv.mk_numeral(val * b, sz);
            return;
        }
        o = bv.mk_bv_mul(bv.mk_numeral(b, sz), a);
    }

    // resolve a1 <= var with var <= b1 to get a1 <= b1
    void resolve(expr *a, expr *b, rational lcm, expr *var, expr_ref &res) {
        SASSERT(bv.is_bv_ule(a));
        SASSERT(bv.is_bv_ule(b));
        rational b_c = get_coeff(b, var);
        rational a_c = get_coeff(a, var);
        SASSERT(!b_c.is_zero() && !a_c.is_zero());
        if (lcm.is_one()) {
            SASSERT(a_c.is_one());
            SASSERT(b_c.is_one());
            res = bv.mk_ule(to_app(a)->get_arg(0), to_app(b)->get_arg(1));
        } else {
            NOT_IMPLEMENTED_YET();
        }
    }

    // generates an under-approximation for some literals in f
    // modifies f, res and bd_fmls
    void resolve(expr *var, expr_ref_vector &f, model &mdl,
                 expr_ref_vector &res, expr_ref_vector &bd_fmls) {
        if (f.empty()) return;
        expr_ref_vector lbs(m), ubs(m);
        get_lbs(var, f, lbs);
        get_ubs(var, f, ubs);
        if (ubs.size() == f.size() || lbs.size() == f.size()) {
            bd_fmls.reset();
            res.push_back(m.mk_true());
            return;
        }
        TRACE("bv_tmp", tout << "trying to resolve " << mk_and(ubs) << " and "
                             << mk_and(lbs) << "\n";);
        SASSERT(ubs.size() + lbs.size() == f.size());
        expr *ub, *lb;
        expr_ref nw_lhs(m), nw_rhs(m), r(m);
        rational lcm = get_lcm(f, var);
        lb = find_glb(mdl, lbs);
        ub = find_lub(mdl, ubs);
        TRACE("bv_tmp", tout << "the upper bound is " << mk_pp(ub, m)
                             << " and the lower bound is " << mk_pp(lb, m)
                             << "\n";);
        rational ub_c = get_coeff(ub, var);
        rational lb_c = get_coeff(lb, var);
        expr_ref_vector sc(m);
        if (!lcm.is_one()) {
            NOT_IMPLEMENTED_YET();
            return;
        }

        // compare all lbs against lb
        nw_rhs = to_app(lb)->get_arg(0);
        for (auto a : lbs) {
            if (a == lb) continue;
            r = bv.mk_ule(to_app(a)->get_arg(0), nw_rhs);
            res.push_back(r);
            TRACE("bv_tmp", tout << "lb comparison produced " << r << "\n";);
        }

        // resolve all ubs against lb
        for (auto a : ubs) {
            resolve(lb, a, lcm, var, r);
            res.push_back(r);
            TRACE("qe", tout << "resolve produced " << r << "\n";);
        }

        // check if any side conditions failed
        if (!mdl.is_true(mk_and(sc))) {
            bd_fmls.append(f);
            f.reset();
            res.reset();
        }
        return;
    }

    void mk_exists(expr *f, app_ref_vector &vars, expr_ref &res) {
        svector<symbol> names;
        expr_ref_vector fv(m);
        ptr_vector<sort> sorts;

        for (unsigned i = 0; i < vars.size(); ++i) {
            fv.push_back(vars.get(i));
            sorts.push_back(m.get_sort(vars.get(i)));
            names.push_back(vars.get(i)->get_decl()->get_name());
        }

        expr_ref tmp(m);
        expr_abstract(m, 0, fv.size(), fv.c_ptr(), f, tmp);
        res = m.mk_exists(sorts.size(), sorts.c_ptr(), names.c_ptr(), tmp, 1);
    }

    void get_subst(model &model, expr *v, expr *f, expr_ref &res) {
        expr_safe_replace sub(m);
        sub.insert(v, model(v));
        sub(f, res);
    }

    bool is_sat(expr *a, expr *b = nullptr, expr *c = nullptr) {
        params_ref p;
        ref<solver> sol = mk_smt_solver(m, p, symbol::null);
        sol->assert_expr(a);
        if (b != nullptr) sol->assert_expr(b);
        if (c != nullptr) sol->assert_expr(c);
        return (sol->check_sat(0, nullptr) != l_false);
    }

    // computes mbp(pi && sig, model, v)
    // input: new_fmls ==> \exist v sig
    // output: new_fmls ==> bg && \exists v pi && sig
    void lazy_mbp(expr_ref_vector &bg, expr_ref_vector &sig,
                  expr_ref_vector &pi, expr_ref v, expr_ref_vector &new_fmls,
                  model &model) {
        expr_ref negged_quant_conj(m);
        negged_quant_conj = m.mk_and(mk_and(pi), mk_and(sig), mk_and(bg));
        if (!contains(negged_quant_conj, v)) {
            flatten_and(negged_quant_conj, new_fmls);
            return;
        }
        app_ref_vector vec(m);
        vec.push_back(to_app(v.get()));
        mk_exists(negged_quant_conj, vec, negged_quant_conj);
        negged_quant_conj = m.mk_not(negged_quant_conj);

        expr_ref new_fmls_conj(m), r(m);
        new_fmls_conj = m.mk_and(mk_and(new_fmls), mk_and(bg));

        expr_ref_vector substs(m);
        for (auto f : pi) {
            get_subst(model, v, f, r);
            substs.push_back(r);
        }
        unsigned init_sz = substs.size(); // for stats

        if (!is_sat(new_fmls_conj, mk_and(substs), negged_quant_conj)) {
            new_fmls.append(substs);
            TRACE("bv_tmp", tout << "\nLazy MBP completed. sig size " << init_sz
                                 << " no substitutions in sig \n";);
            return;
        }

        // todo: possibly, optimize with incremental SMT
        for (auto f : sig) {
            // too weak; add missing substs
            get_subst(model, v, f, r);
            substs.push_back(r);

            if (!is_sat(new_fmls_conj, mk_and(substs), negged_quant_conj))
                break;
        }

        TRACE("bv_tmp", tout << "\nLazy MBP completed. pi size " << init_sz
                             << " substitutions in sig "
                             << substs.size() - init_sz << " and sig size "
                             << sig.size() << "\n";);
        new_fmls.append(substs);
    }

    // project a single variable
    bool operator()(model &model, app *v, app_ref_vector &vars,
                    expr_ref_vector &lits) {
        app_ref_vector vs(m);
        vs.push_back(v);
        project(model, vs, lits, false);
        return vs.empty();
    }

    bool solve(model &model, app_ref_vector &vars, expr_ref_vector &lits) {
        TRACE("bv_tmp",
              tout << "entering solve with " << mk_and(lits) << "\n";);
        expr_ref_vector sc_bvr(m);
        expr_ref res(m), lit_and(m);
        expr_mark reduced;
        lit_and = mk_and(lits);
        app_ref_vector nw_vars(m);
        vector<bnd> bnds, nw_bnds;
        for (auto *e : vars) {
            bnds.reset();
            bv_ext_rw_cfg bv_ext_rw(m, e);
            get_extrt_bnds(e, lit_and, bnds);
            if (bnds.size() == 0) continue;
            collapse_bnds(bnds, nw_bnds);
            bv_ext_rw.add_bnds(nw_bnds, nw_vars);
            bv_ext_rw.register_nw_vars(model);
            rewriter_tpl<bv_ext_rw_cfg> rw(m, false, bv_ext_rw);
            rw(lit_and.get(), lit_and);
            reduced.mark(e);
        }
        unsigned i = 0;
        for (auto *e : vars) {
            if (!reduced.is_marked(e)) vars[i++] = e;
        }
        vars.shrink(i);
        vars.append(nw_vars);
        bv_mbp_rw_cfg bvr(m, sc_bvr);
        bvr.add_model(&model);
        rewriter_tpl<bv_mbp_rw_cfg> bv_rw(m, false, bvr);
        bv_rw(lit_and.get(), lit_and);
        lits.reset();
        flatten_and(lit_and, lits);
        lits.append(sc_bvr);
        // returning false because all preprocessing is over
        return false;
    }
};

/**********************************************************/
/*  bv_project_plugin implementation                     */
/**********************************************************/
bv_project_plugin::bv_project_plugin(ast_manager &m) { m_imp = alloc(imp, m); }

bv_project_plugin::~bv_project_plugin() { dealloc(m_imp); }

bool bv_project_plugin::operator()(model &model, app *var, app_ref_vector &vars,
                                   expr_ref_vector &lits) {
    return (*m_imp)(model, var, vars, lits);
}

void bv_project_plugin::operator()(model &model, app_ref_vector &vars,
                                   expr_ref_vector &lits) {
    m_imp->project(model, vars, lits, false);
}

vector<def> bv_project_plugin::project(model &model, app_ref_vector &vars,
                                       expr_ref_vector &lits) {
    return m_imp->project(model, vars, lits, true);
}

void bv_project_plugin::set_check_purified(bool check_purified) {
    UNREACHABLE();
}

bool bv_project_plugin::solve(model &model, app_ref_vector &vars,
                              expr_ref_vector &lits) {
    return m_imp->solve(model, vars, lits);
}

void bv_project_plugin::saturate(model &model,
                                 func_decl_ref_vector const &shared,
                                 expr_ref_vector &lits) {
    NOT_IMPLEMENTED_YET();
}

family_id bv_project_plugin::get_family_id() {
    return m_imp->bv.get_family_id();
}

opt::inf_eps bv_project_plugin::maximize(expr_ref_vector const &fmls,
                                         model &mdl, app *t, expr_ref &ge,
                                         expr_ref &gt) {
    UNREACHABLE();
    opt::inf_eps value;
    return value;
}

} // namespace qe

template class rewriter_tpl<qe::bv_mbp_rw_cfg>;
