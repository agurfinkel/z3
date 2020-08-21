/*++
Copyright (c) 2020 Arie Gurfinkel

Module Name:

  spacer_global_generalizer.cpp

Abstract:

  Global Guidance for Spacer

Author:

  Hari Govind V K
  Arie Gurfinkel


--*/
#include "muz/spacer/spacer_global_generalizer.h"
#include "ast/arith_decl_plugin.h"
#include "ast/ast_util.h"
#include "ast/for_each_expr.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "model/model2expr.h"
#include "muz/spacer/spacer_context.h"
#include "muz/spacer/spacer_manager.h"
#include "muz/spacer/spacer_matrix.h"
#include "muz/spacer/spacer_util.h"
#include "smt/smt_solver.h"

using namespace spacer;

namespace spacer {
class lemma_info;
using lemma_info_vector = vector<lemma_info, true>;
} // namespace spacer

namespace {
// compute lcm of m_val and denomenator of input expression n, if n is a numeral
struct compute_lcm {
    ast_manager &m;
    arith_util m_arith;
    rational m_val;
    compute_lcm(ast_manager &a_m) : m(a_m), m_arith(m), m_val(1) {}
    void operator()(expr *n) const {}
    void operator()(app *n) {
        rational val;
        if (m_arith.is_numeral(n, val)) {
            m_val = lcm(denominator(abs(val)), m_val);
        }
    }
};
// check whether cnst appears inside an array select expression
struct cnst_in_ind_proc {
    ast_manager &m;
    array_util m_array;
    expr_ref c;
    bool found;
    expr_ref_vector cnsts;
    cnst_in_ind_proc(ast_manager &a_m, expr *cnst)
        : m(a_m), m_array(m), c(cnst, m), found(false), cnsts(m) {}
    void operator()(expr *n) const {}
    void operator()(app *n) {
        if (m_array.is_select(n)) {
            cnsts.reset();
            spacer::get_uninterp_consts(n, cnsts);
            if (cnsts.contains(c)) found = true;
        }
    }
};
bool cnst_in_ind(ast_manager &m, expr *c, expr *n) {
    cnst_in_ind_proc finder(m, c);
    for_each_expr(finder, n);
    return finder.found;
}

// make fresh constant of sort s
app *mk_frsh_const(ast_manager &m, unsigned idx, sort *s) {
    std::stringstream name;
    name << "gspcVar!" << idx;
    return m.mk_const(symbol(name.str().c_str()), s);
}

// check whether sub contains a mapping to a bv_numeral.
// return bv_size of the bv_numeral in the first such mapping.
bool contains_bv(ast_manager &m, const substitution &sub, unsigned &sz) {
    bv_util m_bv(m);
    std::pair<unsigned, unsigned> v;
    expr_offset r;
    for (unsigned j = 0; j < sub.get_num_bindings(); j++) {
        sub.get_binding(j, v, r);
        rational offset;
        if (m_bv.is_numeral(r.get_expr(), offset, sz)) return true;
    }
    return false;
}

// check whether 1) all expressions in the range of sub are bv_numerals 2) all
// bv_numerals in range are of size sz
bool all_same_sz(ast_manager &m, const substitution &sub, unsigned sz) {
    bv_util m_bv(m);
    std::pair<unsigned, unsigned> v;
    expr_offset r;
    for (unsigned j = 0; j < sub.get_num_bindings(); j++) {
        sub.get_binding(j, v, r);
        rational offset;
        if (!(m_bv.is_numeral(r.get_expr(), offset) &&
              m_bv.get_bv_size(r.get_expr()) == sz))
            return false;
    }
    return true;
}
} // namespace
namespace spacer {
lemma_global_generalizer::lemma_global_generalizer(context &ctx)
    : lemma_generalizer(ctx), m(ctx.get_ast_manager()), m_arith(m), m_array(m),
      m_bv(m), m_cvx_cls(m, ctx.use_sage()), m_dim_frsh_cnsts(m),
      m_dim_vars(m) {
    m_solver = mk_smt_solver(m, params_ref::get_empty(), symbol::null);
}

void lemma_global_generalizer::operator()(lemma_ref &lemma) {
    scoped_watch _w_(m_st.watch);
    core(lemma);
}

// get lcm of all the denominators of all the rational values in e
static rational get_lcm(expr *e, ast_manager &m) {
    compute_lcm g(m);
    for_each_expr(g, e);
    TRACE("subsume_verb",
          tout << "lcm of " << mk_pp(e, m) << " is " << g.m_val << "\n";);
    return g.m_val;
}

/// Removes all occurrences of (to_real t) from \p fml where t is a constant
///
/// Applies the following rewrites upto depth \p depth
/// v:Real                             --> mk_int(v) where v is a real value
/// (to_real v:Int)                    --> v
/// (to_int v)                         --> (strip_to_real v)
/// (select A (to_int (to_real i)))    --> (select A i)
/// (op (to_real a0) ... (to_real aN)) --> (op a0 ... aN) where op is an
///                                         arithmetic operation
/// on all other formulas, do nothing
/// NOTE: cannot use a rewriter since we change the sort of fml
static void strip_to_real(expr_ref &fml, unsigned depth = 3) {
    ast_manager &m = fml.get_manager();
    arith_util arith(m);
    rational r;
    if (arith.is_numeral(fml, r)) {
        SASSERT(denominator(r).is_one());
        fml = arith.mk_int(r);
        return;
    }
    if (depth == 0) { return; }
    if (arith.is_to_real(fml)) {
        fml = to_app(fml)->get_arg(0);
        return;
    }
    if (arith.is_to_int(fml) && arith.is_to_real(to_app(fml)->get_arg(0))) {
        expr *arg = to_app(fml)->get_arg(0);
        fml = to_app(arg)->get_arg(0);
        return;
    }
    SASSERT(is_app(fml));
    app *f_app = to_app(fml);
    unsigned num = f_app->get_num_args();
    expr_ref_buffer new_args(m);
    expr_ref child(m);
    for (unsigned i = 0; i < num; i++) {
        child = f_app->get_arg(i);
        strip_to_real(child, depth - 1);
        new_args.push_back(child);
    }
    fml = m.mk_app(f_app->get_family_id(), f_app->get_decl_kind(),
                   new_args.size(), new_args.c_ptr());
    return;
}

/// Converts real subexpressions in \p fml into Int expressions
///
/// Works on arithmetic (in)equalities
/// if fml contains a mod, fml is not normalized
/// otherwise, lcm of fml is computed and lcm * fml is computed
static void to_int_expr(expr_ref &fml) {
    ast_manager &m = fml.get_manager();
    arith_util arith(m);
    if (!(arith.is_arith_expr(fml) || m.is_eq(fml))) return;
    app *fml_app = to_app(fml);
    SASSERT(fml_app->get_num_args() == 2);
    expr_ref lhs(fml_app->get_arg(0), m);
    expr_ref rhs(fml_app->get_arg(1), m);
    // handle mod
    if (contains_mod(lhs) || contains_mod(rhs)) {
        SASSERT(!(contains_real(lhs) || contains_real(rhs)));
        return;
    }
    rational lcm = get_lcm(fml, m);
    SASSERT(lcm != rational::zero());
    mul_by_rat(lhs, lcm);
    mul_by_rat(rhs, lcm);
    strip_to_real(lhs);
    strip_to_real(rhs);
    fml =
        m.mk_app(fml_app->get_family_id(), fml_app->get_decl_kind(), lhs, rhs);
}

/// Convert all fractional constants in \p fml to integers
static void to_int(expr_ref &fml) {
    ast_manager &m = fml.get_manager();
    arith_util arith(m);
    expr_ref_vector fml_vec(m);
    expr_ref_buffer new_fml(m);
    expr_ref new_lit(m);
    flatten_and(fml, fml_vec);
    for (auto *lit : fml_vec) {
        new_lit = lit;
        to_int_expr(new_lit);
        new_fml.push_back(new_lit);
    }
    fml = m.mk_and(new_fml);
}

/// Wrap integer uninterpreted constants in expression \p fml with (to_real)
///
/// only supports arithmetic expressions
/// Applies the following rewrite rules upto depth \p depth
/// (to_real_expr c)                           --> (c:Real) where c is a numeral
/// (to_real_expr i:Int)                       --> (to_real i) where i is a
/// constant/var (to_real_expr (select A i:Int))            --> (select A
/// (to_int (to_real i))) (to_real_expr (op (a0:Int) ... (aN:Int)))  --> (op
/// (to_real a0) ... (to_real aN))
///                                           where op is an arithmetic
///                                           operation
/// on all other formulas, do nothing
/// NOTE: cannot use a rewriter since we change the sort of fml
static void to_real_expr(expr_ref &fml, unsigned depth = 3) {
    ast_manager &m = fml.get_manager();
    arith_util arith(m);
    array_util array(m);
    if (!arith.is_int_real(fml)) return;
    rational r;
    if (arith.is_numeral(fml, r)) {
        fml = arith.mk_real(r);
        return;
    }
    if (is_uninterp(fml)) {
        if (arith.is_int(fml)) fml = arith.mk_to_real(fml);
        return;
    }
    if (arith.is_to_real(fml)) {
        expr *arg = to_app(fml)->get_arg(0);
        if (arith.is_numeral(arg, r)) fml = arith.mk_real(r);
        return;
    }
    if (depth == 0) return;
    SASSERT(is_app(fml));
    app *fml_app = to_app(fml);
    expr *const *args = fml_app->get_args();
    unsigned num = fml_app->get_num_args();
    expr_ref_buffer new_args(m);
    expr_ref child(m);

    // handle selects separately because sort of index needs to be preserved
    if (array.is_select(fml)) {
        new_args.push_back(args[0]);
        for (unsigned i = 1; i < num; i++) {
            SASSERT(arith.is_int(args[i]));
            child = arith.mk_to_real(args[i]);
            child = arith.mk_to_int(child);
            new_args.push_back(child);
        }
    } else {
        expr_ref child(m);
        for (unsigned i = 0; i < num; i++) {
            child = args[i];
            to_real_expr(child, depth - 1);
            new_args.push_back(child);
        }
    }
    fml = m.mk_app(fml_app->get_family_id(), fml_app->get_decl_kind(),
                   new_args.size(), new_args.c_ptr());
    return;
}

/// Wrap integer uninterpreted constants in conjunction \p fml with (to_real)
static void to_real(expr_ref &fml) {
    ast_manager &m = fml.get_manager();
    // cannot use an expr_ref_buffer since flatten_and operates on
    // expr_ref_vector
    expr_ref_vector fml_vec(m);
    flatten_and(fml, fml_vec);
    expr_ref_buffer new_args(m), new_fml(m);
    expr_ref kid(m), new_f(m);
    for (auto *f : fml_vec) {
        new_args.reset();
        app *f_app = to_app(f);
        for (auto *arg : *f_app) {
            kid = arg;
            to_real_expr(kid);
            new_args.push_back(kid);
        }
        // Uninterpreted functions cannot be created using the mk_app api that
        // is being used.
        if (is_uninterp(f)) new_f = f;
        // use this api to change sorts in domain of f
        else
            new_f = m.mk_app(f_app->get_family_id(), f_app->get_decl_kind(),
                             new_args.size(), new_args.c_ptr());
        TRACE("subsume", tout << "to real op2 " << new_f << "\n";);
        new_fml.push_back(new_f);
    }
    fml = m.mk_and(new_fml);
}

/// Create new vars to compute convex cls
void lemma_global_generalizer::add_dim_vars(const lemma_cluster &lc) {
    // AG: review. This code looks fishy.
    const expr_ref &pattern = lc.get_pattern();
    expr_offset r;
    std::pair<unsigned, unsigned> v;

    // temporary pointer to an existing expr
    var_ref var(m);

    auto &lemmas = lc.get_lemmas();
    const substitution &t_sub = lemmas.get(0).get_sub();
    unsigned n_vars = get_num_vars(pattern);
    for (unsigned j = 0; j < n_vars; j++) {
        // get var id
        t_sub.get_binding(j, v, r);
        // always compute convex closure over integers.
        var = m.mk_var(v.first, m.get_sort(r.get_expr()));
        m_cvx_cls.set_dimension(j, var);
        m_dim_vars[j] = var;

        app_ref var_app(m);
        var_app = m.mk_fresh_const("mrg_cvx", m.get_sort(r.get_expr()));
        // TODO: do we need two variables for a <= x <= b ?
        m_dim_frsh_cnsts[j] = var_app;
    }
}

// populate m_cvx_cls by 1) collecting all substitutions in the cluster lc
// 2) converting them to integer numerals
void lemma_global_generalizer::populate_cvx_cls(const lemma_cluster &lc) {
    vector<rational> point;
    unsigned n_vars = get_num_vars(lc.get_pattern());
    const lemma_info_vector &lemmas = lc.get_lemmas();
    expr_offset r;
    std::pair<unsigned, unsigned> v;
    // compute lcm
    rational m_lcm = rational::one();
    for (const lemma_info &lemma : lemmas) {
        const substitution &sub(lemma.get_sub());
        point.reset();
        for (unsigned j = 0; j < n_vars; j++) {
            sub.get_binding(j, v, r);
            rational offset;
            if (!m_arith.is_numeral(r.get_expr(), offset)) {
                m_bv.is_numeral(r.get_expr(), offset);
            }
            m_lcm = lcm(m_lcm, denominator(abs(offset)));
        }
    }
    m_cvx_cls.set_lcm(m_lcm);
    // compute m_lcm and multiply m_data to make everything in integer.
    for (const lemma_info &lemma : lemmas) {
        const substitution &sub(lemma.get_sub());
        point.reset();
        for (unsigned j = 0; j < n_vars; j++) {
            sub.get_binding(j, v, r);
            rational offset;
            if (!m_arith.is_numeral(r.get_expr(), offset)) {
                m_bv.is_numeral(r.get_expr(), offset);
            }
            point.push_back(m_lcm * offset);
        }
        m_cvx_cls.push_back(point);
    }
}

// reset state
void lemma_global_generalizer::reset(unsigned n_vars) {
    // start convex closure computation
    m_cvx_cls.reset(n_vars);
    m_dim_vars.reset();
    m_dim_frsh_cnsts.reset();
    m_dim_frsh_cnsts.reserve(n_vars);
    m_dim_vars.reserve(n_vars);
}

// if all m_dim_frsh_cnsts appear inside array selects in f, skolemize them
// append new constants to cnsts
bool lemma_global_generalizer::skolemize_sel_vars(expr_ref &f,
                                                  app_ref_vector &cnsts) {
    unsigned idx = cnsts.size();
    TRACE("subsume", tout << "Trying to skolemize " << f << "\n";);
    // if there are constants in m_dim_fresh_cnsts that don't appear as indices
    // in sel, return false
    for (auto c : m_dim_frsh_cnsts) {
        if (!cnst_in_ind(m, c, f)) {
            TRACE("global",
                  tout << "not in index " << f << " " << mk_pp(c, m) << "\n";);
            return false;
        }
    }
    expr_ref sk(m), c(m);
    app_ref v(m);
    expr_safe_replace sub(m);
    for (unsigned i = 0; i < m_dim_frsh_cnsts.size(); i++) {
        c = m_dim_frsh_cnsts.get(i);
        // Make fresh constants for instantiation
        // TODO: Is it better to use one of the actual values?
        v = mk_frsh_const(m, i + idx, m.get_sort(c));
        cnsts.push_back(v);
        // Make skolem constants for ground pob
        sk = mk_zk_const(m, i + idx, m.get_sort(c));
        sub.insert(c, sk);
    }
    sub(f.get(), f);
    TRACE("subsume", tout << "skolemized into " << f << "\n";);
    m_dim_frsh_cnsts.reset();
    return true;
}

// compute a lemma that subsumes lemmas in lc
bool lemma_global_generalizer::subsume(lemma_cluster lc, lemma_ref &lemma,
                                       expr_ref_vector &subs_gen) {
    const expr_ref &pattern = lc.get_pattern();
    unsigned n_vars = get_num_vars(pattern);
    SASSERT(n_vars > 0);
    reset(n_vars);

    unsigned sz = 0;
    bool bv_clus = contains_bv(m, lc.get_lemmas()[0].get_sub(), sz);
    if (bv_clus) {
        if (!all_same_sz(m, lc.get_lemmas()[0].get_sub(), sz)) {
            TRACE(
                "global",
                tout
                    << "cannot compute cvx cls of different size variables\n";);
            return false;
        }
        m_cvx_cls.set_bv(sz);
    }
    // create and add dim vars
    add_dim_vars(lc);
    // add points
    populate_cvx_cls(lc);
    expr_ref_vector cls(m);
    bool no_new_vars = m_cvx_cls.closure(cls);
    CTRACE("subsume_verb", !no_new_vars,
           tout << "Convex closure introduced new variables. Closure is"
                << mk_and(cls) << "\n";);

    if (!no_new_vars) {
        // For now, no syntactic convex closure for bv
        if (bv_clus) return false;
        m_st.m_num_syn_cls++;
        // Add the new variables to the list of variables to be eliminated
        const var_ref_vector &vars = m_cvx_cls.get_nw_vars();
        app_ref var_app(m);
        for (auto v : vars) {
            m_dim_vars.push_back(v);
            var_app = m.mk_fresh_const("mrg_syn_cvx", m_arith.mk_real());
            m_dim_frsh_cnsts.push_back(var_app);
        }
    }

    cls.push_back(pattern.get());
    expr_ref cvx_pattern(m);
    var_to_const(mk_and(cls), cvx_pattern);

    if (!no_new_vars) {
        to_real(cvx_pattern);
        TRACE("subsume_verb",
              tout << "To real produced " << cvx_pattern << "\n";);
        rewrite_fresh_cnsts();
    }

    model_ref mdl;

    // get a model for the lemma
    expr_ref_vector pat(m);
    pat.push_back(cvx_pattern);

    // call solver to get model for mbp
    m_solver->push();
    m_solver->assert_expr(pat);
    m_solver->push();
    expr_ref_vector neg(m);
    for (auto l : lc.get_lemmas()) {
        neg.push_back((l.get_lemma()->get_expr()));
    }
    expr_ref neg_expr(m.mk_and(neg), m);
    m_solver->assert_expr(neg_expr);
    lbool res = m_solver->check_sat(0, nullptr);
    if (res == l_true) {
        m_solver->get_model(mdl);
        m_solver->pop(1);
    } else {
        m_solver->pop(1);
        res = m_solver->check_sat(0, nullptr);
        m_solver->get_model(mdl);
    }
    VERIFY(res == l_true);

    SASSERT(mdl.get() != nullptr);
    TRACE("subsume", expr_ref t(m); model2expr(mdl, t);
          tout << "calling mbp with " << cvx_pattern << " and " << t << "\n";);
    qe_project(m, m_dim_frsh_cnsts, cvx_pattern, *mdl.get(), true, true,
               !m_ctx.use_ground_pob());
    // TODO: make sure that all new vars introduced by convex closure are
    // projected
    TRACE("subsume_verb", tout << "Pattern after mbp of computing cvx cls: "
                               << cvx_pattern << "\n";);

    if (!no_new_vars) { to_int(cvx_pattern); }
    if (m_dim_frsh_cnsts.size() > 0 && !m_ctx.use_ground_pob()) {
        app_ref_vector &vars = lemma->get_bindings();
        // Try to skolemize
        bool skmized = skolemize_sel_vars(cvx_pattern, vars);
        if (!skmized) {
            m_st.m_num_mbp_failed++;
            m_solver->pop(1);
            TRACE("subsume", tout << "could not eliminate all vars\n";);
            return false;
        }
        // TODO: fix. Should not assume that the skolem mpb overapproximates
        // cvx_cls
        flatten_and(cvx_pattern, subs_gen);
        return true;
    }
    // check whether mbp over approximates cnx_cls
    // If not, remove literals from mbp till mbp overapproximates cnx_cls
    expr_ref_vector neg_mbp(m);
    // subs_gen stores the generalization
    flatten_and(cvx_pattern, subs_gen);
    for (expr *e : subs_gen) { neg_mbp.push_back(mk_not(m, e)); }

    expr_ref asmpt(m);
    expr_ref_vector pat_nw(m), n_mbp_nw(m);

    while (neg_mbp.size() > 0) {
        asmpt = mk_or(neg_mbp);
        TRACE("subsume_verb", tout << "checking neg mbp: " << asmpt << "\n";);

        m_solver->push();
        m_solver->assert_expr(asmpt);
        res = m_solver->check_sat(0, nullptr);
        if (res == l_false) {
            // one for getting model and one for checking cvx_cls ==> mbp
            m_solver->pop(2);
            return true;
        }

        // remove satisfied literals
        model_ref rslt;
        m_solver->get_model(rslt);

        for (unsigned i = 0; i < neg_mbp.size(); i++) {
            if (!rslt->is_true(neg_mbp.get(i))) {
                n_mbp_nw.push_back(neg_mbp.get(i));
                pat_nw.push_back(subs_gen.get(i));
            }
        }
        neg_mbp.reset();
        for (auto a : n_mbp_nw) neg_mbp.push_back(a);
        subs_gen.reset();
        for (auto a : pat_nw) subs_gen.push_back(a);
        n_mbp_nw.reset();
        pat_nw.reset();

        // reset solver
        m_solver->pop(1);
    }
    // could not find an over approximation
    TRACE("global", tout << "mbp could not overapproximate cnx_cls\n";);
    m_solver->pop(1);
    m_st.m_num_no_ovr_approx++;
    return false;
}

/// Attempt to set a conjecture on pob \p n by dropping literal \p lit from its
/// post. \p lvl and \p gas are the level and gas for conjecture pob
/// returns true if conjecture is set
bool lemma_global_generalizer::do_conjecture(pob_ref n, expr_ref lit,
                                             unsigned lvl, unsigned gas) {
    expr_ref_vector conj(m), fml_vec(m);
    expr_ref n_pob = expr_ref(n->post(), m);
    flatten_and(fml_vec);
    bool is_smaller = drop_lit(fml_vec, lit, conj);
    SASSERT(gas > 0 && gas < UINT_MAX);
    if (conj.size() == 0) {
        // If the pob cannot be abstracted, stop using generalization on
        // it
        TRACE("global", tout << "stop local generalization on pob " << n_pob
                             << " id is " << n_pob->get_id() << "\n";);
        n->stop_local_gen();
        return false;
    }
    if (!is_smaller) {
        // The literal to be abstracted is not in the pob
        TRACE("global", tout << "cannot conjecture on " << n_pob << " with lit "
                             << lit << "\n";);
        // TODO: Should we stop local generalization at this point ?
        m_st.m_num_cant_abs++;
        return false;
    }
    // There is enough gas to conjecture on pob
    n->set_conj_pattern(conj);
    n->set_expand_bnd();
    n->set_may_pob_lvl(lvl);
    n->set_gas(gas);
    TRACE("global", tout << "set conjecture " << conj << " at level "
                         << n->get_may_pob_lvl() << "\n";);
    return true;
}

// decide global guidance based on lemma
void lemma_global_generalizer::core(lemma_ref &lemma) {
    lemma_cluster *pt_cls = (&*lemma->get_pob())->pt().clstr_match(lemma);
    /// Lemma does not belong to any cluster. return
    if (pt_cls == nullptr) return;

    // the lemma has not been added to the cluster yet since the lemma has not
    // been added to spacer yet. So we create a new, local, cluster and add the
    // lemma to it.
    lemma_cluster lc(*pt_cls);
    lc.add_lemma(lemma, true);

    const expr_ref &pattern = lc.get_pattern();
    pob_ref n = lemma->get_pob();
    expr_ref lit(m);

    // if the cluster does not have enough gas, stop local generalization and return
    if (pt_cls->get_gas() == 0) {
        m_st.m_num_cls_ofg++;
        n->stop_local_gen();
        TRACE("global", tout << "stop local generalization on pob "
                             << mk_pp(n->post(), m) << " id is "
                             << n->post()->get_id() << "\n";);
        return;
    }

    TRACE("global",
          tout << "Start global generalization of lemma : " << lemma->get_cube()
               << "\n Discovered cluster: " << pattern << "\n and lemmas ";
          for (const lemma_info &lemma
               : lc.get_lemmas()) {
              tout << "\n \t" << lemma.get_lemma()->get_cube();
          });

    // Concretize
    if (has_nonlinear_var_mul(pattern, m)) {
        m_st.m_num_non_lin++;

        TRACE("global",
              tout << "Found non linear pattern. Marked to concretize \n";);
        // not constructing the concrete pob here since we need a model for n->post()
        n->set_concr_pat(pattern);
        n->set_concretize();
        n->set_gas(pt_cls->get_pob_gas());
        pt_cls->dec_gas();
        return;
    }

    //Conjecture
    if (should_conjecture(pattern, lit)) {
        // Create a conjecture by dropping literal from pob.
        TRACE("global", tout << "Conjecture with pattern " << mk_pp(pattern, m)
                             << " with gas " << pt_cls->get_gas() << "\n";);
        unsigned gas = pt_cls->get_pob_gas();
        unsigned lvl = pt_cls->get_min_lvl() + 1;
        if (do_conjecture(n, lit, lvl, gas)) {
            // decrease the number of times this cluster is going to be used for conjecturing
            pt_cls->dec_gas();
            return;
        }
        // if conjecture failed, try subsume
    }

    // if subsumption removed all the other lemmas, there is nothing to
    // generalize
    if (lc.get_size() < 2) return;

    // Subsume
    expr_ref_vector subsume_gen(m);
    if (subsume(lc, lemma, subsume_gen)) {
        n->set_subsume_pob(subsume_gen);
        n->set_subsume_bindings(lemma->get_bindings());
        n->set_may_pob_lvl(pt_cls->get_min_lvl() + 1);
        n->set_gas(pt_cls->get_pob_gas() + 1);
        n->set_expand_bnd();
        TRACE("global", tout << "subsume pob " << mk_and(subsume_gen)
                             << " at level " << pt_cls->get_min_lvl() + 1
                             << " set on pob " << mk_pp(n->post(), m)
                             << "\n";);
        //This decision is hard to explain. I believe this helped in solving an instance
        n->stop_local_gen();
    }
    return;
}

/// Replace bound vars in \p fml with uninterpreted constants
void lemma_global_generalizer::var_to_const(expr *pattern,
                                            expr_ref &rw_pattern) {
    expr_safe_replace s(m);
    obj_map<expr, expr *> sub;
    for (unsigned i = 0; i < m_dim_vars.size(); i++) {
        s.insert(m_dim_vars[i].get(), to_expr(m_dim_frsh_cnsts[i].get()));
    }
    s(pattern, rw_pattern);
    TRACE("subsume_verb", tout << "Rewrote all vars into u_consts "
                               << mk_pp(pattern, m) << " into " << rw_pattern
                               << "\n";);
    return;
}

// convert all LIA constants in m_dim_frsh_cnsts to LRA constants using to_real
void lemma_global_generalizer::rewrite_fresh_cnsts() {
    app_ref var_app(m);
    for (unsigned i = 0; i < m_dim_vars.size(); i++) {
        if (m_arith.is_real(m_dim_frsh_cnsts.get(i))) continue;
        var_app = m_arith.mk_to_real(m_dim_frsh_cnsts.get(i));
        m_dim_frsh_cnsts[i] = var_app;
    }
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
