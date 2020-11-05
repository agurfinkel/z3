/*++
Copyright (c) 2020 Arie Gurfinkel

Module Name:

  spacer_cluster.cpp

Abstract:

  Discover and mark lemma clusters

Author:

  Hari Govind V K
  Arie Gurfinkel


--*/
#include <algorithm>

#include "ast/arith_decl_plugin.h"
#include "ast/ast_util.h"
#include "ast/rewriter/var_subst.h"
#include "ast/substitution/substitution.h"
#include "muz/spacer/spacer_antiunify.h"
#include "muz/spacer/spacer_cluster.h"
#include "muz/spacer/spacer_context.h"
#include "muz/spacer/spacer_manager.h"
#include "muz/spacer/spacer_util.h"
#include "smt/tactic/unit_subsumption_tactic.h"
#include "util/mpq.h"
#include "util/vector.h"

#define MAX_CLUSTER_SIZE 5
#define MAX_CLUSTERS 5

using namespace spacer;
namespace spacer {
lemma_cluster_finder::lemma_cluster_finder(ast_manager &_m)
    : m(_m), m_arith(m), m_bv(m) {}

/// Check whether \p cube and \p lcube differ only in interpreted constants
bool lemma_cluster_finder::are_neighbours(const expr_ref &cube,
                                          const expr_ref &lcube) {
    SASSERT(is_ground(cube) && is_ground(lcube));
    anti_unifier anti(m);
    expr_ref pat(m);
    substitution sub1(m), sub2(m);
    anti(cube, lcube, pat, sub1, sub2);
    SASSERT(sub1.get_num_bindings() == sub2.get_num_bindings());
    return is_numeric_sub(sub1) && is_numeric_sub(sub2);
}

/// Compute antiunification of \p cube with all formulas in \p fmls.
///
/// Should return
///         \exist res (\forall f \in fmls (\exist i_sub res[i_sub] == f))
/// However, the algorithm is incomplete: it returns such a res iff
///         res \in {antiU(cube,  e) | e \in fmls}
/// Returns true if res is found
/// TODO: do complete n-ary anti-unification. Not done now
/// because anti_unifier does not support free variables
bool lemma_cluster_finder::anti_unify_n_intrp(expr_ref &cube,
                                              expr_ref_vector &fmls,
                                              expr_ref &res) {
    expr_ref_vector patterns(m);
    expr_ref pat(m), fml(m);
    substitution sub1(m), sub2(m);
    anti_unifier anti_u(m);
    substitution s1(m), s2(m);

    TRACE("cluster_stats_verb",
          tout << "Trying to generate a general pattern for " << cube
               << " neighbours are " << fmls << "\n";);

    // collect candidates for res
    for (expr *c : fmls) {
        anti_u.reset();
        s1.reset();
        s2.reset();
        fml.reset();
        fml = expr_ref(c, m);
        SASSERT(are_neighbours(cube, fml));
        anti_u(cube, fml, pat, s1, s2);
        patterns.push_back(pat);
    }

    // go through all the patterns to see if there is a pattern which is general
    // enough to include all lemmas.
    bool is_general_pattern = false, pos = true, all_same = true;
    sem_matcher matcher(m);
    unsigned n_vars_pat = 0;
    for (expr *e : patterns) {
        TRACE("cluster_stats_verb",
              tout << "Checking pattern " << mk_pp(e, m) << "\n";);
        is_general_pattern = true;
        n_vars_pat = get_num_vars(e);
        all_same = all_same && n_vars_pat == 0;
        for (auto *lcube : fmls) {
            matcher.reset();
            s1.reset();
            s1.reserve(1, n_vars_pat);
            if (!(matcher(e, lcube, s1, pos) && pos)) {
                // this pattern is no good
                is_general_pattern = false;
                break;
            }
        }
        if (is_general_pattern) {
            SASSERT(e != nullptr);
            TRACE("cluster_stats",
                  tout << "Found a general pattern " << mk_pp(e, m) << "\n";);
            // found a good pattern
            res = expr_ref(e, m);
            return true;
        }
    }

    CTRACE("cluster_stats", !all_same,
           tout << "Failed to find a general pattern for cluster. Cube is: "
                << cube << " Patterns are " << patterns << "\n";);
    return false;
}

/// Add a new lemma \p lemma to a cluster
///
/// Creates a new cluster for the lemma if necessary
void lemma_cluster_finder::cluster(lemma_ref &lemma) {
    scoped_watch _w_(m_st.watch);
    pred_transformer &pt = (lemma->get_pob())->pt();

    // check whether lemmas has already been added
    if (pt.clstr_contains(lemma)) return;

    /// Add the lemma to a cluster it is matched against
    lemma_cluster *clstr = pt.clstr_match(lemma);
    if (clstr && clstr->get_size() <= MAX_CLUSTER_SIZE) {
        TRACE("cluster_stats_verb", {
                tout << "Trying to add lemma " << lemma->get_cube()
                     << " to an existing cluster ";
                for (auto l : clstr->get_lemmas())
                    tout << l.get_lemma()->get_cube() << "\n";
            });
        clstr->add_lemma(lemma);
        return;
    }

    /// Dont create more than MAX_CLUSTERS number of clusters
    if (clstr && pt.clstr_count(clstr->get_pattern()) > MAX_CLUSTERS) {
        return;
    }

    // Try to create a new cluster with lemma even if it can belong to an
    // oversized cluster. The new cluster will not contain any lemma that is
    // already in another cluster.
    lemma_ref_vector all_lemmas;
    pt.get_all_lemmas(all_lemmas, false);

    expr_ref lcube(m), cube(m);
    lcube = mk_and(lemma->get_cube());
    normalize_order(lcube, lcube);

    expr_ref_vector lma_cubes(m);
    lemma_ref_vector neighbours;

    for (auto *l : all_lemmas) {
        cube.reset();
        cube = mk_and(l->get_cube());
        normalize_order(cube, cube);
        // make sure that l is not in any other clusters
        if (are_neighbours(lcube, cube) && cube != lcube &&
            !pt.clstr_contains(l)) {
            neighbours.push_back(l);
            lma_cubes.push_back(cube);
        }
    }

    if (neighbours.empty()) return;

    // compute the most general pattern to which lemmas fit
    expr_ref pattern(m);
    bool is_cluster = anti_unify_n_intrp(lcube, lma_cubes, pattern);

    // no general pattern
    if (!is_cluster || get_num_vars(pattern) == 0) return;

    // When creating a cluster, its size can be more than MAX_CLUSTER_SIZE. The
    // size limitation is only for adding new lemmas to the cluster. The size is
    // just an arbitrary number.
    // What matters is that we do not allow a cluster to grow indefinitely.
    // for example, given a cluster in which one lemma subsumes all other
    // lemmas. No matter how big the cluster is, GSpacer is going to produce the
    // exact same pob on this cluster. This can lead to divergence. The
    // subsumption check we do is based on unit propagation, it is not complete.
    lemma_cluster *cluster = pt.mk_cluster(pattern);

    TRACE("cluster_stats",
          tout << "created new cluster with pattern: " << pattern << "\n"
               << " and lemma cube: " << lcube << "\n";);

    IF_VERBOSE(1, verbose_stream() << "\ncreated new cluster with pattern: "
                                   << pattern << "\n"
                                   << " and lemma cube: " << lcube << "\n";);

    for (const lemma_ref &l : neighbours) {
        SASSERT(cluster->can_contain(l));
        cluster->add_lemma(l, false);
        TRACE("cluster_stats",
              tout << "Added lemma " << mk_and(l->get_cube()) << "\n";);
    }

    // finally add the lemma and do subsumption check
    cluster->add_lemma(lemma, true);
    SASSERT(cluster->get_size() >= 1);
}

void lemma_cluster_finder::collect_statistics(statistics &st) const {
    st.update("time.spacer.solve.reach.cluster", m_st.watch.get_seconds());
}

/// Removes subsumed lemmas in the cluster
///
/// Removed lemmas are placed into \p removed_lemmas
void lemma_cluster::rm_subsumed(lemma_info_vector &removed_lemmas) {
    removed_lemmas.reset();
    if (m_lemma_vec.size() <= 1) return;
    // set up and run the simplifier
    tactic_ref simplifier = mk_unit_subsumption_tactic(m);
    goal_ref g(alloc(goal, m, false, false, false));
    goal_ref_buffer result;
    for (auto l : m_lemma_vec) { g->assert_expr(l.get_lemma()->get_expr()); }
    (*simplifier)(g, result);
    SASSERT(result.size() == 1);

    goal *r = result[0];
    // nothing removed
    if (r->size() == m_lemma_vec.size()) return;
    // collect removed lemmas
    lemma_info_vector non_subsumd_lemmas;
    for (auto l : m_lemma_vec) {
        bool found = false;
        for (unsigned i = 0; i < r->size(); i++) {
            if (l.get_lemma()->get_expr() == r->form(i)) {
                found = true;
                non_subsumd_lemmas.push_back(l);
                TRACE("cluster_stats_verb", tout << "Keeping lemma "
                                                 << l.get_lemma()->get_cube()
                                                 << "\n";);
                break;
            }
        }
        if (!found) {
            TRACE("cluster_stats_verb", tout << "Removing subsumed lemma "
                                             << l.get_lemma()->get_cube()
                                             << "\n";);
            removed_lemmas.push_back(l);
        }
    }
    m_lemma_vec.reset();
    m_lemma_vec.append(non_subsumd_lemmas);
}

/// Checks whether \p e matches the pattern of the cluster
/// Returns true on success and set \p sub to the corresponding substitution
bool lemma_cluster::match(const expr_ref &e, substitution &sub) {
    bool pos;
    std::pair<unsigned, unsigned> var;
    expr_offset r;
    arith_util a_util(m);
    bv_util bv(m);

    m_matcher.reset();
    bool is_match = m_matcher(m_pattern.get(), e.get(), sub, pos);
    if (!(is_match && pos)) return false;

    unsigned n_binds = sub.get_num_bindings();
    auto is_numeral = [&](expr *e) {
        return a_util.is_numeral(e) || bv.is_numeral(e);
    };
    // All the matches should be numerals
    for (unsigned i = 0; i < n_binds; i++) {
        sub.get_binding(i, var, r);
        if (!is_numeral(r.get_expr())) return false;
    }
    return true;
}

/// A a lemma to a cluster
///
/// Removes subsumed lemmas if \p subs_check is true
///
/// Returns false if lemma does not match the pattern or if it is already in the
/// cluster. Repetition of lemmas is avoided by doing a linear scan over the
/// lemmas in the cluster. Adding a lemma can reduce the size of the cluster due
/// to subsumption reduction.
bool lemma_cluster::add_lemma(const lemma_ref &lemma, bool subs_check) {
    substitution sub(m);
    expr_ref cube(m);

    sub.reserve(1, get_num_vars(m_pattern.get()));
    cube = mk_and(lemma->get_cube());
    normalize_order(cube, cube);

    if (!match(cube, sub)) return false;

    // cluster already contains the lemma
    if (contains(lemma)) return false;

    TRACE("cluster_stats_verb",
          tout << "Trying to add lemma " << lemma->get_cube() << "\n";);

    lemma_info li(lemma, sub);
    m_lemma_vec.push_back(li);

    if (subs_check) {
        lemma_info_vector removed_lemmas;
        rm_subsumed(removed_lemmas);
        for (auto rl_li : removed_lemmas) {
            // There is going to atmost one subsumed lemma that matches l_i
            if (rl_li.get_lemma() == li.get_lemma()) return false;
        }
    }
    TRACE("cluster_stats", tout << "Added lemma " << lemma->get_cube()
                                << " to  existing cluster " << m_pattern
                                << "\n";);
    return true;
}

} // namespace spacer
