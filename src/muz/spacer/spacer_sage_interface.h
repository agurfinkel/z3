#pragma once
#include "spacer_arith_kernel.h"
#include "util/stopwatch.h"
#include "util/util.h"
#include <fstream>
#include <signal.h>
#include <sys/wait.h>
#include <unistd.h>

namespace spacer {

/*
  Interface to Sage. Supports initialization and writing to sage. To get
  output from Sage, write to file and read from the file. Could not find
  standard methods to convert file descriptors to streams. Easier to write to
  file and use ifstream
 */
class Sage {
    FILE *m_out;
    FILE *m_in;
    std::string tmp_name;
    pid_t child_pid;

  public:
    Sage();
    bool test();
    ~Sage() {
        kill(child_pid, SIGKILL);
        int status;
        waitpid(child_pid, &status, 0);
    }
    FILE *get_ostream() const { return m_out; }
    FILE *get_istream() const { return m_in; }
};

/*
  Compute kernel using Sage.
 */
class Sage_kernel : public arith_kernel {
    Sage m_sage;
    bool compute_arith_kernel() override;
    std::string print_matrix() const;
    std::string print_kernel() const;
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

  public:
    Sage_kernel(spacer_matrix &matrix) : arith_kernel(matrix, true), m_sage() {}
    ~Sage_kernel() override {}

    virtual void collect_statistics(statistics &st) const override {
        st.update("time.spacer.sage.calls", m_st.watch.get_seconds());
        st.update("SPACER sage calls", m_st.m_sage_calls);
    }
    virtual void reset_statistics() override { m_st.reset(); }
};

} // namespace spacer
