#pragma once
/*++
Copyright (c) 2020 Arie Gurfinkel

Module Name:

  spacer_cluster.h

Abstract:

  Discover and mark lemma clusters

Author:

  Hari Govind V K
  Arie Gurfinkel


--*/

#include "muz/spacer/spacer_context.h"
namespace spacer {
class lemma_cluster_finder {
    struct stats {
        unsigned max_group_size;
        stopwatch watch;
        stats() { reset(); }
        void reset() {
            max_group_size = 0;
            watch.reset();
        }
    };
    stats m_st;
    ast_manager &m;
    arith_util m_arith;
    bv_util m_bv;
    typedef std::pair<unsigned, unsigned> var_offset;

    /// Check whether \p cube and \p lcube differ only in interpreted constants
    bool are_neighbours(const expr_ref &cube, const expr_ref &lcube);

    /// N-ary antiunify. Returns whether there is a substitution with only
    /// interpreted consts
    bool anti_unify_n_intrp(expr_ref &cube, expr_ref_vector &fmls,
                            expr_ref &res);

  public:
    lemma_cluster_finder(ast_manager &m);
    void cluster(lemma_ref &lemma);
    void collect_statistics(statistics &st) const;
    void reset_statistics() { m_st.reset(); }
};
} // namespace spacer
