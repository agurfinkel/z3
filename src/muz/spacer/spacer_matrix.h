/*++
Copyright (c) 2017 Arie Gurfinkel

Module Name:

    spacer_matrix.h

Abstract:
    a matrix

Author:
    Bernhard Gleiss

Revision History:


--*/
#pragma once

#include "util/rational.h"
#include "util/vector.h"

namespace spacer {

    class spacer_matrix {
    public:
        spacer_matrix(unsigned m, unsigned n); // m rows, n columns

        unsigned num_rows() const;
        unsigned num_cols() const;

        const rational &get(unsigned i, unsigned j) const;
        void set(unsigned i, unsigned j, const rational& v);

        unsigned perform_gaussian_elimination();

        const vector<rational> &get_row(unsigned i) const {
            SASSERT(i < num_rows());
            return m_matrix.get(i);
        }

        // copies over all the elements in col i
        void get_col(unsigned i, vector<rational> &data) const {
            SASSERT(i < m_num_cols);
            data.reset();
            data.reserve(m_num_rows);
            unsigned j = 0;
            for (auto &v : m_matrix) { data[j++] = (v.get(i)); }
            SASSERT(data.size() == m_num_rows);
        }

        void add_row(vector<rational> &row);
        void reset(unsigned n_cols) {
            m_num_rows = 0;
            m_num_cols = n_cols;
            m_matrix.reset();
        }
        void print_matrix();
        void normalize();
        bool compute_linear_deps(spacer_matrix &eq) const;
    private:
        unsigned m_num_rows;
        unsigned m_num_cols;
        vector<vector<rational>> m_matrix;
        bool is_lin_reltd(unsigned i, unsigned j, rational &coeff1,
                          rational &coeff2, rational &off) const;
    };
}

