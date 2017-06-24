/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    spacer_smt_context_manager.cpp

Abstract:

    Manager of smt contexts

Author:

    Nikolaj Bjorner (nbjorner) 2011-11-26.

Revision History:

--*/

#include "spacer_smt_context_manager.h"
#include "has_free_vars.h"
#include "ast_pp.h"
#include "ast_smt_pp.h"
#include <sstream>
#include "smt_params.h"

#include "ast_pp_util.h"
#include "smt_context.h"
#include "spacer_util.h"
namespace spacer {




smt_context_manager::smt_context_manager(ast_manager &m,
        unsigned max_num_contexts,
        const params_ref &p) :
    m_fparams(p),
    m(m),
    m_max_num_contexts(max_num_contexts),
    m_num_contexts(0) { m_stats.reset();}


smt_context_manager::~smt_context_manager()
{
    std::for_each(m_solvers.begin(), m_solvers.end(),
                  delete_proc<spacer::virtual_solver_factory>());
}

virtual_solver* smt_context_manager::mk_fresh()
{
    ++m_num_contexts;
    virtual_solver_factory *solver_factory = 0;

    if (m_max_num_contexts == 0 || m_solvers.size() < m_max_num_contexts) {
        m_solvers.push_back(alloc(spacer::virtual_solver_factory, m, m_fparams));
        solver_factory = m_solvers.back();
    } else
    { solver_factory = m_solvers[(m_num_contexts - 1) % m_max_num_contexts]; }

    return solver_factory->mk_solver();
}

void smt_context_manager::collect_statistics(statistics& st) const
{
    for (unsigned i = 0; i < m_solvers.size(); ++i) {
        m_solvers[i]->collect_statistics(st);
    }
}

void smt_context_manager::reset_statistics()
{
    for (unsigned i = 0; i < m_solvers.size(); ++i) {
        m_solvers[i]->reset_statistics();
    }
}


};

