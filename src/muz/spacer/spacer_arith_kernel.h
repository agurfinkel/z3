#pragma once

#include "spacer_matrix.h"
#include "util/statistics.h"
namespace spacer {

/**
Interface to compute arith_kernel. Computes kernel of m_matrix
*/
class arith_kernel {
  protected:
    struct stats {
        unsigned m_failed;
        stats() { reset(); }
        void reset() { m_failed = 0; }
    };
    stats m_st;

    const spacer_matrix &m_matrix;
    spacer_matrix m_kernel;
    bool m_use_sage;
    virtual bool compute_arith_kernel() { return false; };

  public:
    arith_kernel(spacer_matrix &matrix, bool use_sage)
        : m_matrix(matrix), m_kernel(0, 0), m_use_sage(use_sage) {}
    virtual ~arith_kernel() = default;

    bool compute_kernel() {
        SASSERT(m_matrix.num_rows() > 1);
        if (m_matrix.compute_linear_deps(m_kernel)) {
            // the matrix cannot be reduced further
            if (m_matrix.num_cols() - m_kernel.num_rows() <= 1) return true;
            // AG: what if we are not using Sage?
            // use sage to find ALL linear deps
            m_kernel.reset(m_kernel.num_cols());
            SASSERT(m_matrix.num_cols() > 2);
        }
        if (m_matrix.num_cols() > 2) m_st.m_failed++;
        return (m_matrix.num_cols() > 2) && m_use_sage &&
               compute_arith_kernel();
    }

    void reset() { m_kernel = spacer_matrix(0, 0); }
    const spacer_matrix &get_kernel() const { return m_kernel; }
    virtual void collect_statistics(statistics &st) const {
        st.update("SPACER need sage", m_st.m_failed);
    }
    virtual void reset_statistics() { m_st.reset(); }
};

} // namespace spacer
