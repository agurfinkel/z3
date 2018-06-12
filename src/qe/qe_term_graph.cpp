/**++
Copyright (c) Arie Gurfinkel

Module Name:

    qe_term_graph.cpp

Abstract:

    Equivalence graph of terms

Author:

    Arie Gurfinkel

Notes:

--*/

#include "util/util.h"
#include "util/uint_set.h"
#include "ast/ast_pp.h"
#include "ast/ast_util.h"
#include "ast/for_each_expr.h"
#include "ast/occurs.h"
#include "qe/qe_term_graph.h"

namespace qe {

    namespace is_pure_ns {
        struct found{};
        struct proc {
            is_variable_proc &m_is_var;
            proc(is_variable_proc &is_var) : m_is_var(is_var) {}
            void operator()(var *n) const {if (m_is_var(n)) throw found();}
            void operator()(app const *n) const {if (m_is_var(n)) throw found();}
            void operator()(quantifier *n) const {}
        };
    }

    bool is_pure(is_variable_proc &is_var, expr *e) {
        try {
            is_pure_ns::proc v(is_var);
            quick_for_each_expr(v, e);
        }
        catch (is_pure_ns::found) {
            return false;
        }
        return true;
    }

    class term {
        // -- an app represented by this term
        expr* m_expr; // NSB: to make usable with exprs
        // -- root of the equivalence class
        term* m_root;
        // -- next element in the equivalence class (cyclic linked list)
        term* m_next;
        // -- eq class size
        unsigned m_class_size;
        // -- general purpose mark
        unsigned m_mark:1;
        // -- general purpose second mark
        unsigned m_mark2:1;
        // -- is an interpreted constant
        unsigned m_interpreted:1;

        // -- terms that contain this term as a child
        ptr_vector<term> m_parents;

        // arguments of term.
        ptr_vector<term> m_children;

    public:
        term(expr* v, u_map<term*>& app2term) :
            m_expr(v),
            m_root(this),
            m_next(this),
            m_class_size(1),
            m_mark(false),
            m_mark2(false),
            m_interpreted(false) {
            if (!is_app()) return;
            for (expr* e : *to_app(m_expr)) {
                term* t = app2term[e->get_id()];
                t->get_root().m_parents.push_back(this);
                m_children.push_back(t);
            }
        }

        ~term() {}

        class parents {
            term const& t;
        public:
            parents(term const& _t):t(_t) {}
            parents(term const* _t):t(*_t) {}
            ptr_vector<term>::const_iterator begin() const { return t.m_parents.begin(); }
            ptr_vector<term>::const_iterator end() const { return t.m_parents.end(); }
        };

        class children {
            term const& t;
        public:
            children(term const& _t):t(_t) {}
            children(term const* _t):t(*_t) {}
            ptr_vector<term>::const_iterator begin() const { return t.m_children.begin(); }
            ptr_vector<term>::const_iterator end() const { return t.m_children.end(); }
        };

        // Congruence table hash function is based on
        // roots of children and function declaration.

        unsigned get_hash() const {
            unsigned a, b, c;
            a = b = c = get_decl_id();
            for (term * ch : children(this)) {
                a = ch->get_root().get_id();
                mix(a, b, c);
            }
            return c;
        }

        static bool cg_eq(term const * t1, term const * t2) {
            if (t1->get_decl_id() != t2->get_decl_id()) return false;
            if (t1->m_children.size() != t2->m_children.size()) return false;
            for (unsigned i = 0, sz = t1->m_children.size(); i < sz; ++ i) {
                if (t1->m_children[i]->get_root().get_id() != t2->m_children[i]->get_root().get_id()) return false;
            }
            return true;
        }

        unsigned get_id() const { return m_expr->get_id();}

        unsigned get_decl_id() const { return is_app() ? get_app()->get_decl()->get_id() : m_expr->get_id(); }

        bool is_marked() const {return m_mark;}
        void set_mark(bool v){m_mark = v;}
        bool is_marked2() const {return m_mark2;} // NSB: where is this used?
        void set_mark2(bool v){m_mark2 = v;}      // NSB: where is this used?

        bool is_interpreted() const {return m_interpreted;}
        bool is_theory() const { return !is_app() || get_app()->get_family_id() != null_family_id; }
        void mark_as_interpreted() {m_interpreted=true;}
        expr* get_expr() const {return m_expr;}
        bool is_app() const {return ::is_app(m_expr);}
        app *get_app() const {return is_app() ? to_app(m_expr) : nullptr;}
        unsigned get_num_args() const { return is_app() ? get_app()->get_num_args() : 0; }

        term &get_root() const {return *m_root;}
        bool is_root() const {return m_root == this;}
        void set_root(term &r) {m_root = &r;}
        term &get_next() const {return *m_next;}
        void add_parent(term* p) { m_parents.push_back(p); }

        unsigned get_class_size() const {return m_class_size;}

        void merge_eq_class(term &b) {
            std::swap(this->m_next, b.m_next);
            m_class_size += b.get_class_size();
            // -- reset (useful for debugging)
            b.m_class_size = 0;
        }

        // -- make this term the root of its equivalence class
        void mk_root() {
            if (is_root()) return;

            term *curr = this;
            do {
                if (curr->is_root()) {
                    // found previous root
                    SASSERT(curr != this);
                    m_class_size = curr->get_class_size();
                    curr->m_class_size = 0;
                }
                curr->set_root(*this);
                curr = &curr->get_next();
            }
            while (curr != this);
        }
    };


    bool term_graph::is_variable_proc::operator()(const expr * e) const {
        if (!is_app(e)) return false;
        const app *a = ::to_app(e);
        if (a->get_family_id() != null_family_id) return false;
        if (m_solved.contains(a->get_decl()->get_id())) return false;
        return m_exclude == m_decls.contains(a->get_decl()->get_id());
    }
    bool term_graph::is_variable_proc::operator()(const term &t) const {
        return !t.is_theory() && m_exclude == m_decls.contains(t.get_decl_id());
    }

    void term_graph::is_variable_proc::set_decls(const func_decl_ref_vector &decls, bool exclude) {
        reset();
        m_exclude = exclude;
        for (auto *d : decls) m_decls.insert(d->get_id(), true);
    }
    void term_graph::is_variable_proc::mark_solved(const expr *e) {
        if ((*this)(e))
            m_solved.insert(::to_app(e)->get_decl()->get_id(), true);
    }


    unsigned term_graph::term_hash::operator()(term const* t) const { return t->get_hash(); }

    bool term_graph::term_eq::operator()(term const* a, term const* b) const { return term::cg_eq(a, b); }

    term_graph::term_graph(ast_manager &man) : m(man), m_lits(m), m_pinned(m) {
        m_plugins.register_plugin(mk_basic_solve_plugin(m, m_is_var));
        m_plugins.register_plugin(mk_arith_solve_plugin(m, m_is_var));
    }

    term_graph::~term_graph() {
        reset();
    }

    bool term_graph::is_pure_def(expr *atom, expr *v) {
        expr *e = nullptr;
        return m.is_eq(atom, v, e) && m_is_var(v) && is_pure(m_is_var, e);
    }

    static family_id get_family_id(ast_manager &m, expr *lit) {
        if (m.is_not(lit, lit))
            return get_family_id(m, lit);

        expr *a = nullptr, *b = nullptr;
        // deal with equality using sort of range
        if (m.is_eq (lit, a, b)) {
            return get_sort (a)->get_family_id();
        }
        // extract family_id of top level app
        else if (is_app(lit)) {
            return to_app(lit)->get_decl()->get_family_id();
        }
        else {
            return null_family_id;
        }
    }
    void term_graph::add_lit(expr *l) {
        expr_ref lit(m);

        family_id fid = get_family_id(m, l);
        qe::solve_plugin *pin = m_plugins.get_plugin(fid);
        lit = pin ? (*pin)(l) : l;
        m_lits.push_back(lit);
        internalize_lit(lit);
    }

    bool term_graph::is_internalized(expr *a) {
        return m_app2term.contains(a->get_id());
    }

    term* term_graph::get_term(expr *a) {
        term *res;
        return m_app2term.find (a->get_id(), res) ? res : nullptr;
    }

    term *term_graph::mk_term(expr *a) {
        term * t = alloc(term, a, m_app2term);
        if (t->get_num_args() == 0 && m.is_unique_value(a)){
            t->mark_as_interpreted();
        }

        m_terms.push_back(t);
        m_app2term.insert(a->get_id(), t);
        return t;
    }

    term* term_graph::internalize_term(expr *t) {
        term* res = get_term(t);
        if (res) return res;
        ptr_buffer<expr> todo;
        todo.push_back(t);
        while (!todo.empty()) {
            t = todo.back();
            res = get_term(t);
            if (res) {
                todo.pop_back();
                continue;
            }
            unsigned sz = todo.size();
            if (is_app(t)) {
                for (expr * arg : *::to_app(t)) {
                    if (!get_term(arg))
                        todo.push_back(arg);
                }
            }
            if (sz < todo.size()) continue;
            todo.pop_back();
            res = mk_term(t);
        }
        SASSERT(res);
        return res;
    }

    void term_graph::internalize_eq(expr *a1, expr* a2) {
        SASSERT(m_merge.empty());
        merge(*internalize_term(a1), *internalize_term(a2));
        merge_flush();
        SASSERT(m_merge.empty());
    }

    void term_graph::internalize_lit(expr* lit) {
        expr *e1 = nullptr, *e2 = nullptr;
        if (m.is_eq (lit, e1, e2)) {
            internalize_eq (e1, e2);
        }
        else {
            internalize_term(lit);
        }
    }

    void term_graph::merge_flush() {
        while (!m_merge.empty()) {
            term* t1 = m_merge.back().first;
            term* t2 = m_merge.back().second;
            m_merge.pop_back();
            merge(*t1, *t2);
        }
    }

    void term_graph::merge(term &t1, term &t2) {
        // -- merge might invalidate term2app cache
        m_term2app.reset();
        m_pinned.reset();

        term *a = &t1.get_root();
        term *b = &t2.get_root();

        if (a == b) return;

        if (a->get_class_size() > b->get_class_size()) {
            std::swap(a, b);
        }

        // Remove parents of it from the cg table.
        for (term* p : term::parents(b)) {
            if (!p->is_marked()) {
                p->set_mark(true);
                m_cg_table.erase(p);
            }
        }
        // make 'a' be the root of the equivalence class of 'b'
        b->set_root(*a);
        for (term *it = &b->get_next(); it != b; it = &it->get_next()) {
            it->set_root(*a);
        }

        // merge equivalence classes
        a->merge_eq_class(*b);

        // Insert parents of b's old equilvalence class into the cg table
        for (term* p : term::parents(a)) {
            if (p->is_marked()) {
                term* p_old = m_cg_table.insert_if_not_there(p);
                p->set_mark(false);
                a->add_parent(p);
                // propagate new equalities.
                if (p->get_root().get_id() != p_old->get_root().get_id()) {
                    m_merge.push_back(std::make_pair(p, p_old));
                }
            }
        }
    }

    expr* term_graph::mk_app_core (expr *e) {
        if (is_app(e)) {
            expr_ref_buffer kids(m);
            app* a = ::to_app(e);
            for (expr * arg : *a) {
                kids.push_back (mk_app(arg));
            }
            app* res = m.mk_app(a->get_decl(), a->get_num_args(), kids.c_ptr());
            m_pinned.push_back(res);
            return res;
        }
        else {
            return e;
        }
    }

    expr_ref term_graph::mk_app(term const &r) {
        SASSERT(r.is_root());

        if (r.get_num_args() == 0) {
            return expr_ref(r.get_expr(), m);
        }

        expr* res = nullptr;
        if (m_term2app.find(r.get_id(), res)) {
            return expr_ref(res, m);
        }

        res = mk_app_core (r.get_app());
        m_term2app.insert(r.get_id(), res);
        return expr_ref(res, m);

    }

    expr_ref term_graph::mk_app(expr *a) {
        term *t = get_term(a);
        if (!t)
            return expr_ref(a, m);
        else
            return mk_app(t->get_root());

    }

    void term_graph::mk_equalities(term const &t, expr_ref_vector &out) {
        SASSERT(t.is_root());
        expr_ref rep(mk_app(t), m);
        for (term *it = &t.get_next(); it != &t; it = &it->get_next()) {
            expr* mem = mk_app_core(it->get_app());
            out.push_back (m.mk_eq (rep, mem));
        }
    }

    void term_graph::mk_all_equalities(term const &t, expr_ref_vector &out) {
        mk_equalities(t, out);

        for (term *it = &t.get_next(); it != &t; it = &it->get_next ()) {
            expr* a1 = mk_app_core (it->get_app());
            for (term *it2 = &it->get_next(); it2 != &t; it2 = &it2->get_next()) {
                expr* a2 =  mk_app_core(it2->get_app());
                out.push_back (m.mk_eq (a1, a2));
            }
        }
    }

    void term_graph::reset_marks() {
        for (term * t : m_terms) {
            t->set_mark(false);
        }
    }

    /// Order of preference for roots of equivalence classes
    /// XXX This should be factored out to let clients control the preference
    bool term_graph::term_lt(term const &t1, term const &t2) {

        // prefer constants over applications
        // prefer uninterpreted constants over values
        // prefer smaller expressions over larger ones
        if (t1.get_num_args() == 0 || t2.get_num_args() == 0) {
            if (t1.get_num_args() == t2.get_num_args()) {
                // t1.get_num_args() == t2.get_num_args() == 0
                if (m.is_value(t1.get_expr()) == m.is_value(t2.get_expr()))
                    return t1.get_id() < t2.get_id();
                return m.is_value(t2.get_expr());
            }
            return t1.get_num_args() < t2.get_num_args();
        }

        unsigned sz1 = get_num_exprs(t1.get_expr());
        unsigned sz2 = get_num_exprs(t1.get_expr());
        return sz1 < sz2;
    }

    void term_graph::pick_root (term &t) {
        term *r = &t;
        for (term *it = &t.get_next(); it != &t; it = &it->get_next()) {
            it->set_mark(true);
            if (term_lt(*it, *r)) { r = it; }
        }

        // -- if found something better, make it the new root
        if (r != &t) {
            r->mk_root();
        }
    }

    /// Choose better roots for equivalence classes
    void term_graph::pick_roots() {
        for (term* t : m_terms) {
            if (!t->is_marked() && t->is_root())
                pick_root(*t);
        }
        reset_marks();
    }

    void term_graph::display(std::ostream &out) {
        for (term * t : m_terms) {
            out << mk_pp(t->get_expr(), m) << " is root " << t->is_root()
                << " cls sz " << t->get_class_size()
                << " term " << t
                << "\n";
        }
    }

    void term_graph::to_lits (expr_ref_vector &lits, bool all_equalities) {
        pick_roots();

        for (expr * a : m_lits) {
            if (is_internalized(a)) {
                lits.push_back (::to_app(mk_app(a)));
            }
        }

        for (term * t : m_terms) {
            if (!t->is_root())
                continue;
            else if (all_equalities)
                mk_all_equalities (*t, lits);
            else
                mk_equalities(*t, lits);
        }
    }

    expr_ref term_graph::to_app() {
        expr_ref_vector lits(m);
        to_lits(lits);
        return mk_and(lits);
    }

    void term_graph::reset() {
        m_term2app.reset();
        m_pinned.reset();
        m_app2term.reset();
        std::for_each(m_terms.begin(), m_terms.end(), delete_proc<term>());
        m_terms.reset();
        m_lits.reset();
        m_cg_table.reset();
    }

    namespace {
        class projector {
            term_graph &m_tg;
            ast_manager &m;
            u_map<expr*> m_term2app;
            u_map<expr*> m_root2rep;

            expr_ref_vector m_pinned;  // tracks expr in the maps

            expr* mk_pure(term const& t) {
                expr* e = nullptr;
                if (m_term2app.find(t.get_id(), e)) return e;
                e = t.get_expr();
                if (!is_app(e)) return nullptr;
                app* a = ::to_app(e);
                expr_ref_buffer kids(m);
                for (term* ch : term::children(t)) {
                    if (!m_root2rep.find(ch->get_root().get_id(), e)) return nullptr;
                    kids.push_back(e);
                }
                expr* pure = m.mk_app(a->get_decl(), kids.size(), kids.c_ptr());
                m_pinned.push_back(pure);
                m_term2app.insert(t.get_id(), pure);
                return pure;
            }

            bool is_better_rep(expr *t1, expr *t2) {
                if (!t2) return t1 != nullptr;
                return m.is_unique_value(t1) && !m.is_unique_value(t2);
            }

            void purify() {
                // - propagate representatives up over parents.
                //   use work-list + marking to propagate.
                // - produce equalities over represented classes.
                // - produce other literals over represented classes
                //   (walk disequalities in m_lits and represent
                //   lhs/rhs over decls or excluding decls)

                ptr_vector<term> worklist;
                for (term * t : m_tg.m_terms) {
                    worklist.push_back(t);
                    t->set_mark(true);
                }

                while (!worklist.empty()) {
                    term* t = worklist.back();
                    worklist.pop_back();
                    t->set_mark(false);
                    if (m_term2app.contains(t->get_id()))
                        continue;
                    if (!t->is_theory() && is_projected(*t))
                        continue;

                    expr* pure = mk_pure(*t);
                    if (!pure) continue;

                    m_term2app.insert(t->get_id(), pure);
                    expr* rep = nullptr;
                    // ensure that the root has a representative
                    m_root2rep.find(t->get_root().get_id(), rep);

                    // update rep with pure if it is better
                    if (pure != rep && is_better_rep(pure, rep)) {
                        m_root2rep.insert(t->get_root().get_id(), pure);
                        for (term * p : term::parents(t->get_root())) {
                            m_term2app.remove(p->get_id());
                            if (!p->is_marked()) {
                                p->set_mark(true);
                                worklist.push_back(p);
                            }
                        }
                    }
                }

                // Here we could also walk equivalence classes that
                // contain interpreted values by sort and extract
                // disequalities bewteen non-unique value
                // representatives.  these disequalities are implied
                // and can be mined using other means, such as theory
                // aware core minimization
                m_tg.reset_marks();
            }

            void solve_core() {
                ptr_vector<term> worklist;
                for (term * t : m_tg.m_terms) {
                    // skip pure terms
                    if (m_term2app.contains(t->get_id())) continue;
                    worklist.push_back(t);
                    t->set_mark(true);
                }

                while (!worklist.empty()) {
                    term* t = worklist.back();
                    worklist.pop_back();
                    t->set_mark(false);
                    if (m_term2app.contains(t->get_id()))
                        continue;

                    expr* pure = mk_pure(*t);
                    if (!pure) continue;

                    m_term2app.insert(t->get_id(), pure);
                    expr* rep = nullptr;
                    // ensure that the root has a representative
                    m_root2rep.find(t->get_root().get_id(), rep);

                    if (!rep) {
                        m_root2rep.insert(t->get_root().get_id(), pure);
                        for (term * p : term::parents(t->get_root())) {
                            SASSERT(!m_term2app.contains(p->get_id()));
                            if (!p->is_marked()) {
                                p->set_mark(true);
                                worklist.push_back(p);
                            }
                        }
                    }
                }
                m_tg.reset_marks();
            }

            bool find_app(term &t, expr *&res) {
                return m_root2rep.find(t.get_root().get_id(), res);
            }

            bool find_app(expr *lit, expr *&res) {
                return m_root2rep.find(m_tg.get_term(lit)->get_root().get_id(), res);
            }

            void mk_lits(expr_ref_vector &res) {
                expr *e = nullptr;
                for (auto *lit : m_tg.m_lits) {
                    if (!m.is_eq(lit) && find_app(lit, e))
                        res.push_back(e);
                }
            }

            void mk_pure_equalities(const term &t, expr_ref_vector &res) {
                SASSERT(t.is_root());
                expr *rep = nullptr;
                if (!m_root2rep.find(t.get_id(), rep)) return;
                obj_hashtable<expr> members;
                members.insert(rep);
                term const * r = &t;
                do {
                    expr* member = nullptr;
                    if (m_term2app.find(r->get_id(), member) && !members.contains(member)) {
                        res.push_back (m.mk_eq (rep, member));
                        members.insert(member);
                    }
                    r = &r->get_next();
                }
                while (r != &t);
            }

            bool is_projected(const term &t) {return m_tg.m_is_var(t);}

            void mk_unpure_equalities(const term &t, expr_ref_vector &res) {
                expr *rep = nullptr;
                if (!m_root2rep.find(t.get_id(), rep)) return;
                obj_hashtable<expr> members;
                members.insert(rep);
                term const * r = &t;
                do {
                    expr* member = mk_pure(*r);
                    SASSERT(member);
                    if (!members.contains(member) &&
                        (!is_projected(*r) || !is_solved_eq(rep, member))) {
                        res.push_back(m.mk_eq(rep, member));
                        members.insert(member);
                    }
                    r = &r->get_next();
                }
                while (r != &t);
            }

            void mk_equalities(bool pure, expr_ref_vector &res) {
                for (term *t : m_tg.m_terms) {
                    if (!t->is_root()) continue;
                    if (!m_root2rep.contains(t->get_id())) continue;
                    if (pure)
                        mk_pure_equalities(*t, res);
                    else
                        mk_unpure_equalities(*t, res);
                }
            }

            void mk_pure_equalities(expr_ref_vector &res) {
                return mk_equalities(true, res);
            }

            void mk_unpure_equalities(expr_ref_vector &res) {
                return mk_equalities(false, res);
            }

            // TBD: generalize for also the case of a (:var n)
            bool is_solved_eq(expr *_lhs, expr* _rhs) {
                if (!is_app(_lhs) || !is_app(_rhs)) return false;
                app *lhs, *rhs;
                lhs = ::to_app(_lhs);
                rhs = ::to_app(_rhs);

                if (rhs->get_num_args() > 0) return false;
                if (rhs->get_family_id() != null_family_id) return false;

                return !occurs(rhs, lhs);
            }

        public:
            projector(term_graph &tg) : m_tg(tg), m(m_tg.m), m_pinned(m) {}

            void reset() {
                m_tg.reset_marks();
                m_term2app.reset();
                m_root2rep.reset();
                m_pinned.reset();
            }
            expr_ref_vector project() {
                expr_ref_vector res(m);
                purify();
                mk_lits(res);
                mk_pure_equalities(res);
                reset();
                return res;
            }
            expr_ref_vector solve() {
                expr_ref_vector res(m);
                purify();
                solve_core();
                mk_lits(res);
                mk_unpure_equalities(res);
                reset();
                return res;
            }
        };
    }

    void term_graph::solve_for_vars() {
        expr_ref new_lit(m);
        expr *old_lit = nullptr, *v = nullptr;
        for (unsigned i = 0, sz = m_lits.size(); i < sz; ++i) {
            old_lit = m_lits.get(i);
            qe::solve_plugin *pin = m_plugins.get_plugin(get_family_id(m, old_lit));
            if (pin) {
                new_lit = (*pin)(old_lit);
                if (new_lit.get() != old_lit) {
                    m_lits.set(i, new_lit);
                    internalize_lit(new_lit);
                }
                if (is_pure_def(new_lit, v)) {
                    m_is_var.mark_solved(v);
                }
            }
        }
        m_is_var.reset_solved();
    }
    expr_ref_vector term_graph::project(func_decl_ref_vector const& decls, bool exclude) {
        m_is_var.set_decls(decls, exclude);
        solve_for_vars();
        projector p(*this);
        m_is_var.reset();
        expr_ref_vector v = p.project();
        return v;
    }

    expr_ref_vector term_graph::solve(func_decl_ref_vector const &decls, bool exclude) {
        m_is_var.set_decls(decls, exclude);
        solve_for_vars();
        projector p(*this);
        expr_ref_vector v = p.solve();
        m_is_var.reset();
        return v;
    }

}
