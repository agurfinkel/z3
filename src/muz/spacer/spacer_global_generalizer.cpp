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
// Compute lcm of m_val and denomenator of input expression n, if n is a numeral
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

/// Check whether there are Real constants in \p c
bool contains_real_cnsts(app_ref_vector &c) {
    arith_util m_arith(c.get_manager());
    for (auto f : c) {
        if (m_arith.is_real(f)) return true;
    }
    return false;
}
// check whether there is an equivalent of function \p f in LRA
bool exists_lra_equiv(expr_ref &f) {
    ast_manager &m = f.m();
    arith_util a(m);
    //uninterpreted constants do not have arguments. So equivalent function exists.
    if (is_uninterp_const(f)) return true;
    SASSERT(is_app(f));
    func_decl *f_decl = to_app(f)->get_decl();
    return f_decl->get_family_id() == a.get_family_id();
}
// Check whether there are Int constants in \p c
bool contains_int_cnsts(app_ref_vector &c) {
    arith_util m_arith(c.get_manager());
    for (auto f : c) {
        if (m_arith.is_int(f)) return true;
    }
    return false;
}

// Check whether \p sub contains a mapping to a bv_numeral.
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

// Check whether 1) all expressions in the range of \p sub are bv_numerals 2)
// all bv_numerals in range are of size sz
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
lemma_global_generalizer::subsumer::subsumer(ast_manager &a_m, bool use_sage,
                                             bool ground_pob)
    : m(a_m), m_arith(m), m_bv(m), m_cvx_cls(m, use_sage), m_dim_frsh_cnsts(m),
      m_dim_vars(m), m_ground_pob(ground_pob) {
    scoped_ptr<solver_factory> factory(
        mk_smt_strategic_solver_factory(symbol::null));
    m_solver = (*factory)(m, params_ref::get_empty(), false, true, false,
                          symbol::null);
}

lemma_global_generalizer::lemma_global_generalizer(context &ctx)
    : lemma_generalizer(ctx), m(ctx.get_ast_manager()),
      m_subsumer(m, ctx.use_sage(), ctx.use_ground_pob()) {}

void lemma_global_generalizer::operator()(lemma_ref &lemma) {
    scoped_watch _w_(m_st.watch);
    core(lemma);
}

/// Get lcm of all the denominators of all the rational values in e
static rational get_lcm(expr *e, ast_manager &m) {
    compute_lcm g(m);
    for_each_expr(g, e);
    TRACE("subsume_verb",
          tout << "lcm of " << mk_pp(e, m) << " is " << g.m_val << "\n";);
    return g.m_val;
}

// clang-format off
/// Removes all occurrences of (to_real t) from \p fml where t is a constant
///
/// Applies the following rewrites upto depth \p depth
/// v:Real                                                        --> mk_int(v) where v is a real value
/// (to_real v:Int)                                               --> v
/// (to_int v)                                                    --> (strip_to_real v)
/// (store A (to_int (to_real i0)) ... (to_int (to_real iN)) k)   --> (store A i0 ... iN
///                                                                      (strip_to_real k))
/// (select A (to_int (to_real i0)) ... (to_int (to_real iN)))    --> (select A i0 ... iN)
/// (op (to_real a0) ... (to_real aN))                            --> (op a0 ... aN) where op is an
///                                                                    arithmetic operation
/// on all other formulas, do nothing
/// NOTE: cannot use a rewriter since we change the sort of fml
// clang-format on
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

/// Coerces a rational inequality to a semantically equivalent inequality with
/// integer coefficients
///
/// Works on arithmetic (in)equalities
/// if fml contains a mod, fml is not normalized
/// otherwise, lcm of fml is computed and lcm * fml is computed
static void to_int_term(expr_ref &fml) {
    ast_manager &m = fml.get_manager();
    arith_util arith(m);
    if (!contains_real(fml)) return;
    if (!(arith.is_arith_expr(fml) || m.is_eq(fml))) return;
    app *fml_app = to_app(fml);
    SASSERT(fml_app->get_num_args() == 2);
    expr_ref lhs(fml_app->get_arg(0), m);
    expr_ref rhs(fml_app->get_arg(1), m);
    // mod not supported
    SASSERT(!(contains_mod(lhs) || contains_mod(rhs)));
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
    expr_ref_vector fml_vec(m), new_fml(m);
    expr_ref new_lit(m);
    flatten_and(fml, fml_vec);
    for (auto *lit : fml_vec) {
        new_lit = lit;
        to_int_term(new_lit);
        new_fml.push_back(new_lit);
    }
    fml = mk_and(new_fml);
}

// clang-format off
/// Wrap integer uninterpreted constants in expression \p fml with (to_real)
///
/// only supports arithmetic expressions
/// Applies the following rewrite rules upto depth \p depth
/// (to_real_term c)                                           --> (c:Real) where c is a numeral
/// (to_real_term i:Int)                                       --> (to_real i) where i is a constant/var
/// (to_real_term (select A i0:Int ... iN:Int))                --> (select A (to_int (to_real i0)) ...
///                                                                          (to_int (to_real iN)))
/// (to_real_term (store A i0:Int ... iN:Int k))               --> (store A (to_int (to_real i0)) ...
///                                                                         (to_int (to_real iN))
///                                                                         (to_real_term k))
/// (to_real_term (op (a0:Int) ... (aN:Int)))                  --> (op (to_real a0) ... (to_real aN))
///                                                                where op is
///                                                                an arithmetic
///                                                                operation
/// on all other formulas, do nothing
/// NOTE: cannot use a rewriter since we change the sort of fml
// clang-format on
static void to_real_term(expr_ref &fml, unsigned depth = 3) {
    ast_manager &m = fml.get_manager();
    arith_util arith(m);
    datatype_util datatype(m);
    if (!arith.is_int_real(fml)) return;
    rational r;
    if (arith.is_numeral(fml, r)) {
        fml = arith.mk_real(r);
        return;
    }
    if (is_uninterp_const(fml)) {
        if (arith.is_int(fml)) fml = arith.mk_to_real(fml);
        return;
    }
    if (arith.is_to_real(fml)) {
        expr *arg = to_app(fml)->get_arg(0);
        if (arith.is_numeral(arg, r)) fml = arith.mk_real(r);
        return;
    }

    if (is_uninterp(fml)) return;
    if (depth == 0) return;
    SASSERT(is_app(fml));
    app *fml_app = to_app(fml);
    expr *const *args = fml_app->get_args();
    unsigned num = fml_app->get_num_args();
    expr_ref_buffer new_args(m);
    expr_ref child(m);

    if (!exists_lra_equiv(fml)) {
        new_args.push_back(args[0]);
        for (unsigned i = 1; i < num; i++) {
            child = args[i];
            to_real_term(child, depth - 1);
            if (arith.is_int(args[i])) child = arith.mk_to_int(child);
            SASSERT(args[i]->get_sort() == child->get_sort());
            new_args.push_back(child);
        }
        fml = m.mk_app(fml_app->get_decl(), new_args);
    } else {
        expr_ref child(m);
        for (unsigned i = 0; i < num; i++) {
            child = args[i];
            to_real_term(child, depth - 1);
            new_args.push_back(child);
        }
        // The mk_app method selects the function sort based on the sort of
        // new_args
        fml = m.mk_app(fml_app->get_family_id(), fml_app->get_decl_kind(),
                       new_args.size(), new_args.c_ptr());
    }
    return;
}

/// Wrap integer uninterpreted constants in conjunction \p fml with (to_real)
static void to_real(expr_ref &fml) {
    ast_manager &m = fml.get_manager();
    // cannot use an expr_ref_buffer since flatten_and operates on
    // expr_ref_vector
    expr_ref_vector fml_vec(m), new_fml(m);
    flatten_and(fml, fml_vec);
    expr_ref_buffer new_args(m);
    expr_ref kid(m), new_f(m);
    for (auto *f : fml_vec) {
        new_args.reset();
        app *f_app = to_app(f);
        for (auto *arg : *f_app) {
            kid = arg;
            to_real_term(kid);
            new_args.push_back(kid);
        }
        // Uninterpreted functions cannot be created using the mk_app api that
        // is being used.
        if (is_uninterp(f)) new_f = f;
        // use this api to change sorts in domain of f
        else
            new_f = m.mk_app(f_app->get_family_id(), f_app->get_decl_kind(),
                             new_args.size(), new_args.c_ptr());
        new_fml.push_back(new_f);
    }
    fml = mk_and(new_fml);
}

/// Create new vars to compute convex cls
void lemma_global_generalizer::subsumer::add_dim_vars(const lemma_cluster &lc) {
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
        var = m.mk_var(v.first, r.get_expr()->get_sort());
        m_cvx_cls.set_dimension(j, var);
        m_dim_vars[j] = var;

        app_ref var_app(m);
        var_app = m.mk_fresh_const("mrg_cvx", r.get_expr()->get_sort());
        // TODO: do we need two variables for a <= x <= b ?
        m_dim_frsh_cnsts[j] = var_app;
    }
}

// Populate m_cvx_cls by 1) collecting all substitutions in the cluster \p lc
// 2) converting them to integer numerals
void lemma_global_generalizer::subsumer::populate_cvx_cls(
    const lemma_cluster &lc) {
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
void lemma_global_generalizer::subsumer::reset(unsigned n_vars) {
    // start convex closure computation
    m_cvx_cls.reset(n_vars);
    m_dim_vars.reset();
    m_dim_frsh_cnsts.reset();
    m_dim_frsh_cnsts.reserve(n_vars);
    m_dim_vars.reserve(n_vars);
}

/// Find a representative for \p c
// TODO: replace with a symbolic representative
expr *lemma_global_generalizer::subsumer::find_repr(const model_ref &mdl,
                                                    const app_ref &c) {
    return mdl->get_const_interp(c->get_decl());
}

/// Skolemize all m_dim_frsh_cnsts in \p f
///
/// \p cnsts is appended with ground terms from \p mdl
void lemma_global_generalizer::subsumer::skolemize(expr_ref &f,
                                                   app_ref_vector &cnsts,
                                                   const model_ref &mdl) {
    unsigned idx = cnsts.size();
    app_ref sk(m), c(m);
    expr_ref eval(m);
    expr_safe_replace sub(m);
    expr_ref_vector f_cnsts(m);
    spacer::get_uninterp_consts(f, f_cnsts);
    for (unsigned i = 0; i < m_dim_frsh_cnsts.size(); i++) {
        c = m_dim_frsh_cnsts.get(i);
        if (!f_cnsts.contains(c)) continue;
        SASSERT(m_arith.is_int(c));
        // Make skolem constants for ground pob
        sk = mk_zk_const(m, i + idx, c->get_sort());
        eval = find_repr(mdl, c);
        SASSERT(is_app(eval));
        cnsts.push_back(to_app(eval));
        // push back original values for bindings
        sub.insert(c, sk);
    }
    sub(f.get(), f);
    TRACE("subsume", tout << "skolemized into " << f << "\n";);
    m_dim_frsh_cnsts.reset();
}

///\p a is a hard constraint and \p b is a soft constraint that have to be
/// satisfied by mdl
bool lemma_global_generalizer::subsumer::maxsat_with_model(const expr_ref a,
                                                           const expr_ref b,
                                                           model_ref &mdl) {
    TRACE("subsume_verb",
          tout << "maxsat with model " << a << " " << b << "\n";);
    SASSERT(is_ground(a));
    m_solver->push();
    m_solver->assert_expr(a);
    expr_ref_buffer tmp(m);
    expr_ref tag(m), assump_b(m);
    lbool res;
    if (is_ground(b)) {
        tag = m.mk_fresh_const("get_mdl_assump", m.mk_bool_sort());
        tmp.push_back(tag);
        assump_b = m.mk_implies(tag, b);
        m_solver->assert_expr(assump_b);
    }
    res = m_solver->check_sat(tmp.size(), tmp.c_ptr());
    if (res != l_true && tmp.size() > 0) {
        tmp.pop_back();
        tmp.push_back(m.mk_not(tag));
        res = m_solver->check_sat(tmp.size(), tmp.c_ptr());
    }
    if (res != l_true) return false;
    m_solver->get_model(mdl);
    m_solver->pop(1);
    return true;
}

/// Returns false if subsumption is not supported for \p lc
bool lemma_global_generalizer::subsumer::is_handled(const lemma_cluster &lc) {
    // check whether all substitutions are to bv_numerals
    unsigned sz = 0;
    bool bv_clus = contains_bv(m, lc.get_lemmas()[0].get_sub(), sz);
    // If there are no BV numerals, cases are handled.
    // TODO: put restriction on Arrays, non linear arithmetic etc
    if (!bv_clus) return true;
    if (!all_same_sz(m, lc.get_lemmas()[0].get_sub(), sz)) {
        TRACE("subsume",
              tout << "cannot compute cvx cls of different size variables\n";);
        return false;
    }
    return true;
}

/// Prepare internal state for computing subsumption
void lemma_global_generalizer::subsumer::setup_subsume(
    const lemma_cluster &lc) {
    unsigned sz = 0;
    bool bv_clus = contains_bv(m, lc.get_lemmas()[0].get_sub(), sz);
    if (bv_clus) m_cvx_cls.set_bv(sz);
    // create and add dim vars
    add_dim_vars(lc);
    // add points
    populate_cvx_cls(lc);
}

/// Add variables introduced by cvx_cls to the list of variables
void lemma_global_generalizer::subsumer::add_cvx_cls_vars() {
    const var_ref_vector &vars = m_cvx_cls.get_new_vars();
    app_ref var_app(m);
    for (auto v : vars) {
        m_dim_vars.push_back(v);
        var_app = m.mk_fresh_const("mrg_syn_cvx", v->get_sort());
        m_dim_frsh_cnsts.push_back(var_app);
    }
}

/// Compute a cube \p subs_gen such that \neg subs_gen subsumes all the lemmas
/// in \p lc \p bindings is the set of skolem constants in \p subs_gen
bool lemma_global_generalizer::subsumer::subsume(const lemma_cluster &lc,
                                                 expr_ref_vector &subs_gen,
                                                 app_ref_vector &bindings) {
    const expr_ref &pattern = lc.get_pattern();
    unsigned n_vars = get_num_vars(pattern);
    SASSERT(n_vars > 0);
    reset(n_vars);

    if (!is_handled(lc)) return false;
    // prepare internal state to compute subsumption
    setup_subsume(lc);

    // compute convex closure
    expr_ref_vector cls(m);
    bool has_new_vars = m_cvx_cls.closure(cls);
    CTRACE("subsume_verb", has_new_vars,
           tout << "Convex closure introduced new variables. Closure is "
                << mk_and(cls) << "\n";);

    // If convex closure introduced new variables, add them to m_dim_frsh_cnsts
    if (has_new_vars) {
        m_st.m_num_syn_cls++;
        add_cvx_cls_vars();
    }

    cls.push_back(pattern);
    // Making convex closure ground
    expr_ref cvx_pattern(m);
    ground_free_vars(mk_and(cls), cvx_pattern);

    // store convex closure. cvx_pattern is going to be modified
    expr_ref cvx_cls(m);
    cvx_cls = cvx_pattern;

    // eliminate convex closure variables using mbp
    bool res = eliminate_vars(
        cvx_pattern, lc, has_new_vars && contains_int_cnsts(m_dim_frsh_cnsts),
        bindings);

    if (!res) return false;

    flatten_and(cvx_pattern, subs_gen);
    return over_approximate(subs_gen, cvx_cls);
}

/// Eliminate m_dim_frsh_cnsts from \p cvx_cls
///
/// Uses \p lc to get a model for mbp.
/// \p mlir indicates whether \p cvx_cls contains both ints and reals.
/// all vars that could not be eliminated are skolemized and added to \p
/// bindings
bool lemma_global_generalizer::subsumer::eliminate_vars(
    expr_ref &cvx_pattern, const lemma_cluster &lc, bool mlir,
    app_ref_vector &bindings) {
    if (mlir) {
        to_real(cvx_pattern);
        TRACE("subsume_verb",
              tout << "To real produced " << cvx_pattern << "\n";);
        to_real_cnsts();
    }

    // Get a model that is not satisfied by ANY of the cubes in the
    // cluster
    expr_ref neg_cubes(m);
    // all models for neg_cubes are outside all the cubes in the cluster
    lc.get_conj_lemmas(neg_cubes);
    model_ref mdl;
    // call solver to get the model
    if (!maxsat_with_model(cvx_pattern, neg_cubes, mdl)) {
        TRACE("subsume",
              tout << "Convex closure is unsat " << cvx_pattern << "\n";);
        return false;
    }

    SASSERT(mdl.get() != nullptr);
    TRACE("subsume", expr_ref t(m); model2expr(mdl, t);
          tout << "calling mbp with " << cvx_pattern << " and " << t << "\n";);

    qe_project(m, m_dim_frsh_cnsts, cvx_pattern, *mdl.get(), true, true,
               !m_ground_pob);

    TRACE("subsume", tout << "Pattern after mbp of computing cvx cls: "
                          << cvx_pattern << "\n";);
    if (!m_ground_pob && contains_real_cnsts(m_dim_frsh_cnsts)) {
        TRACE("subsume", tout << "Could not eliminate non integer variables\n";
              for (auto e
                   : m_dim_vars) tout
              << mk_pp(e, m);
              tout << "\n";);
        return false;
    }
    SASSERT(!m_ground_pob || m_dim_frsh_cnsts.empty());
    if (mlir) { to_int(cvx_pattern); }

    // If not all variables have been eliminated, skolemize and add bindings
    if (m_dim_frsh_cnsts.size() > 0) {
        SASSERT(!m_ground_pob);
        skolemize(cvx_pattern, bindings, mdl);
    }

    return true;
}

/// Weaken \p a such that \p b ==> a
///
/// drop literals from a until b && \not a is unsat. Each time a sat answer is
/// obtained, use a model to choose which literals to drop next
bool lemma_global_generalizer::subsumer::over_approximate(expr_ref_vector &a,
                                                          const expr_ref b) {
    expr_ref tag(m);
    expr_ref_vector tags(m), assump_a(m);
    expr_ref_buffer new_a(m), new_tags(m);
    std::string name = "ovr_approx_assump";
    for (auto e : a) {
        tag = m.mk_fresh_const(symbol(name), m.mk_bool_sort());
        tags.push_back(tag);
        assump_a.push_back(m.mk_implies(tag, e));
    }
    // neg_a stores the negation of a
    expr_ref neg_a(m);
    neg_a = push_not(mk_and(assump_a));
    lbool res = l_true;
    TRACE("subsume_verb", tout << "weakening " << mk_and(a)
                               << " to over approximate " << b << "\n";);
    bool all_tags_disabled = false;
    m_solver->push();
    m_solver->assert_expr(b);
    m_solver->assert_expr(neg_a);
    while (!all_tags_disabled) {
        res = m_solver->check_sat(tags.size(), tags.c_ptr());
        if (res == l_false) { break; }
        // remove satisfied literals
        model_ref rslt;
        m_solver->get_model(rslt);

        all_tags_disabled = true;
        new_tags.reset();
        for (unsigned i = 0; i < a.size(); i++) {
            if (!m.is_not(tags.get(i)) && rslt->is_false(a.get(i))) {
                // mark a[i] as to be removed by negating the tag
                new_tags.push_back(m.mk_not(tags.get(i)));
                all_tags_disabled = false;
            } else {
                new_tags.push_back(tags.get(i));
            }
        }
        SASSERT(new_tags.size() == tags.size());
        // TODO: assert # negations in new_tags > # negations in tags
        tags.reset();
        for (auto e : new_tags) tags.push_back(e);
    }
    m_solver->pop(1);
    if (all_tags_disabled) {
        // could not find an over approximation
        TRACE("subsume", tout << "mbp could not overapproximate cvx_cls\n";);
        m_st.m_num_no_ovr_approx++;
        a.reset();
        return false;
    }
    // remove all expressions whose tags are false
    for (unsigned i = 0; i < tags.size(); i++) {
        if (!m.is_not(tags.get(i))) new_a.push_back(a.get(i));
    }
    a.reset();
    for (auto e : new_a) a.push_back(e);
    TRACE("subsume",
          tout << "over approximate produced " << mk_and(a) << "\n";);
    return true;
}

/// Attempt to set a conjecture on pob \p n.
///
/// Done by dropping literal \p lit from
/// post of \p n. \p lvl is level for conjecture pob. \p gas is the gas for the
/// conjecture pob returns true if conjecture is set
bool lemma_global_generalizer::do_conjecture(pob_ref n, expr_ref lit,
                                             unsigned lvl, unsigned gas) {
    expr_ref_vector conj(m), fml_vec(m);
    expr_ref n_pob = expr_ref(n->post(), m);
    normalize_order(n_pob, n_pob);
    fml_vec.push_back(n_pob);
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
        n->stop_local_gen();
        m_st.m_num_cant_abs++;
        return false;
    }
    // There is enough gas to conjecture on pob
    n->set_conj_pattern(conj);
    n->set_expand_bnd();
    n->set_may_pob_lvl(lvl);
    n->set_gas(gas);
    n->stop_local_gen();
    TRACE("global", tout << "set conjecture " << conj << " at level "
                         << n->get_may_pob_lvl() << "\n";);
    return true;
}

// Decide global guidance based on lemma
void lemma_global_generalizer::core(lemma_ref &lemma) {
    // -- pob that the lemma blocks
    pob_ref pob = lemma->get_pob();
    // -- cluster that the lemma belongs to
    lemma_cluster *cluster = pob->pt().clstr_match(lemma);

    /// Lemma does not belong to any cluster. return
    if (!cluster) return;

    // if the cluster does not have enough gas, stop local generalization and
    // return
    if (cluster->get_gas() == 0) {
        m_st.m_num_cls_ofg++;
        pob->stop_local_gen();
        TRACE("global", tout << "stop local generalization on pob "
                             << mk_pp(pob->post(), m) << " id is "
                             << pob->post()->get_id() << "\n";);
        return;
    }

    // -- local cluster that includes the new lemma
    lemma_cluster lc(*cluster);
    lc.add_lemma(lemma, true);

    const expr_ref &pat = lc.get_pattern();
    expr_ref lit(m);

    TRACE("global", {
        tout << "Start global generalization of lemma : " << lemma->get_cube()
             << "\n Discovered cluster: " << pat << "\n and lemmas ";
        for (const lemma_info &lemma : lc.get_lemmas()) {
            tout << "\n \t" << lemma.get_lemma()->get_cube();
        }
    });

    // Concretize
    if (has_nonlinear_var_mul(pat, m)) {
        m_st.m_num_non_lin++;

        TRACE("global",
              tout << "Found non linear pattern. Marked to concretize \n";);
        // not constructing the concrete pob here since we need a model for
        // n->post()
        pob->set_concr_pat(pat);
        pob->set_concretize();
        pob->set_gas(cluster->get_pob_gas());
        cluster->dec_gas();
        return;
    }

    // Conjecture
    if (should_conjecture(pat, lit)) {
        // Create a conjecture by dropping literal from pob.
        TRACE("global", tout << "Conjecture with pattern " << mk_pp(pat, m)
                             << " with gas " << cluster->get_gas() << "\n";);
        unsigned gas = cluster->get_pob_gas();
        unsigned lvl = cluster->get_min_lvl();
        if (do_conjecture(pob, lit, lvl, gas)) {
            // decrease the number of times this cluster is going to be used for
            // conjecturing
            cluster->dec_gas();
            return;
        }
        // if conjecture failed, try subsume
    }

    // if subsumption removed all the other lemmas, there is nothing to
    // generalize
    if (lc.get_size() < 2) return;

    // -- new pob that is blocked by generalized lemma
    expr_ref_vector new_pob(m);
    // -- bindings for free variables of new_pob
    // -- subsumer might introduce extra free variables
    app_ref_vector bindings(m);
    bindings.append(lemma->get_bindings());

    if (m_subsumer.subsume(lc, new_pob, bindings)) {
        pob->set_subsume_pob(new_pob);
        pob->set_subsume_bindings(bindings);
        pob->set_may_pob_lvl(cluster->get_min_lvl());
        pob->set_gas(cluster->get_pob_gas() + 1);
        pob->set_expand_bnd();
        TRACE("global", tout << "subsume pob " << mk_and(new_pob)
                             << " at level " << cluster->get_min_lvl()
                             << " set on pob " << mk_pp(pob->post(), m)
                             << "\n";);
        // -- stop local generalization
        // -- maybe not the best choice in general. Helped with one instance on
        // -- our benchmarks
        pob->stop_local_gen();
        cluster->dec_gas();
    }
}

/// Replace bound vars in \p fml with uninterpreted constants
void lemma_global_generalizer::subsumer::ground_free_vars(expr *pat,
                                                          expr_ref &out) {
    SASSERT(!is_ground(pat));
    expr_safe_replace s(m);
    obj_map<expr, expr *> sub;
    for (unsigned i = 0; i < m_dim_vars.size(); i++) {
        s.insert(m_dim_vars.get(i), to_expr(m_dim_frsh_cnsts.get(i)));
    }
    s(pat, out);
    TRACE("subsume_verb", tout << "Rewrote all vars into u_consts "
                               << mk_pp(pat, m) << " into " << out << "\n";);
    SASSERT(is_ground(out));
    return;
}

// convert all LIA constants in m_dim_frsh_cnsts to LRA constants using to_real
void lemma_global_generalizer::subsumer::to_real_cnsts() {
    app_ref var_app(m);
    for (unsigned i = 0; i < m_dim_frsh_cnsts.size(); i++) {
        if (m_arith.is_real(m_dim_frsh_cnsts.get(i))) continue;
        var_app = m_arith.mk_to_real(m_dim_frsh_cnsts.get(i));
        m_dim_frsh_cnsts.set(i, var_app);
    }
}

void lemma_global_generalizer::subsumer::collect_statistics(
    statistics &st) const {
    st.update("SPACER num no over approximate", m_st.m_num_no_ovr_approx);
    st.update("SPACER num sync cvx cls", m_st.m_num_syn_cls);
    st.update("SPACER num mbp failed", m_st.m_num_mbp_failed);
    m_cvx_cls.collect_statistics(st);
}

void lemma_global_generalizer::collect_statistics(statistics &st) const {
    st.update("time.spacer.solve.reach.gen.global", m_st.watch.get_seconds());
    st.update("SPACER cluster out of gas", m_st.m_num_cls_ofg);
    st.update("SPACER num non lin", m_st.m_num_non_lin);
    st.update("SPACER num cant abstract", m_st.m_num_cant_abs);
}

} // namespace spacer
