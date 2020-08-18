#pragma once
#include "spacer_arith_kernel.h"
#include "util/stopwatch.h"
#include "util/util.h"
#include <fstream>
#include <signal.h>
#include <sys/wait.h>
#include <unistd.h>

namespace spacer {

class Sage;
/**
   Kernel computation of a matrix using Sage

   Used for Debug only!
*/
class Sage_kernel : public arith_kernel {
    struct stats {
        stopwatch watch;
        unsigned m_sage_calls;
        stats() { reset(); }
        void reset() {
            watch.reset();
            m_sage_calls = 0;
        }
    };
    stats m_st;

    scoped_ptr<Sage> m_sage;
    bool compute_arith_kernel() override;
    std::string print_matrix() const;
    std::string print_kernel() const;

  public:
    Sage_kernel(spacer_matrix &matrix);
    virtual void collect_statistics(statistics &st) const override {
        st.update("time.spacer.sage.calls", m_st.watch.get_seconds());
        st.update("SPACER sage calls", m_st.m_sage_calls);
    }
    virtual void reset_statistics() override { m_st.reset(); }
};

} // namespace spacer
