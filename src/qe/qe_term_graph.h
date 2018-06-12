/**++
Copyright (c) Arie Gurfinkel

Module Name:

    qe_term_graph.h

Abstract:

    Equivalence graph of terms

Author:

    Arie Gurfinkel

Notes:

--*/
#ifndef QE_TERM_GRAPH_H__
#define QE_TERM_GRAPH_H__

#include "ast/ast.h"
#include "util/plugin_manager.h"
#include "qe/qe_solve_plugin.h"
#include "qe/qe_vartest.h"

namespace qe {

    class term;
    namespace {class projector;}

    class term_graph {
        friend class projector;

        class is_variable_proc : public ::is_variable_proc {
            bool m_exclude;
            obj_hashtable<func_decl> m_decls, m_solved;
        public:
            bool operator()(const expr *e) const override;
            bool operator()(const term &t) const;

            void set_decls(const func_decl_ref_vector &decls, bool exclude);
            void mark_solved(const expr *e);
            void reset_solved() {m_solved.reset();}
            void reset() {m_decls.reset(); m_solved.reset(); m_exclude = true;}
        };

        struct term_hash { unsigned operator()(term const* t) const; };
        struct term_eq { bool operator()(term const* a, term const* b) const; };
        ast_manager &     m;
        ptr_vector<term>  m_terms;
        expr_ref_vector    m_lits; // NSB: expr_ref_vector?
        u_map<term* >     m_app2term;
        ast_ref_vector    m_pinned;
        u_map<expr*>      m_term2app;
        plugin_manager<qe::solve_plugin> m_plugins;
        ptr_hashtable<term, term_hash, term_eq> m_cg_table;
        vector<std::pair<term*,term*>> m_merge;

        term_graph::is_variable_proc m_is_var;
        void merge(term &t1, term &t2);
        void merge_flush();

        term *mk_term(expr *t);
        term *get_term(expr *t);

        term *internalize_term(expr *t);
        void internalize_eq(expr *a1, expr *a2);
        void internalize_lit(expr *lit);

        bool is_internalized(expr *a);

        bool term_lt(term const &t1, term const &t2);
        void pick_root (term &t);
        void pick_roots();

        void reset_marks();

        expr* mk_app_core(expr* a);
        expr_ref mk_app(term const &t);
        expr* mk_pure(term& t);
        expr_ref mk_app(expr *a);
        void mk_equalities(term const &t, expr_ref_vector &out);
        void mk_all_equalities(term const &t, expr_ref_vector &out);
        void display(std::ostream &out);

        bool is_pure_def(expr* atom, expr *& v);
        void solve_for_vars();


    public:
        term_graph(ast_manager &m);
        ~term_graph();

        void set_vars(func_decl_ref_vector const& decls, bool exclude);

        ast_manager& get_ast_manager() const { return m;}

        void add_lit(expr *lit);
        void add_lits(expr_ref_vector const &lits) { for (expr* e : lits) add_lit(e); }
        void add_eq(expr* a, expr* b) { internalize_eq(a, b); }

        void reset();

        // deprecate?
        void to_lits(expr_ref_vector &lits, bool all_equalities = false);
        expr_ref to_app();

        /**
         * Return literals obtained by projecting added literals
         * onto the vocabulary of decls (if exclude is false) or outside the
         * vocabulary of decls (if exclude is true).
         */
         expr_ref_vector project();
         expr_ref_vector solve();
        
    };

}
#endif
