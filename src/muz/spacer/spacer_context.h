/**++
Copyright (c) 2017 Microsoft Corporation and Arie Gurfinkel

Module Name:

    spacer_context.h

Abstract:

    SPACER predicate transformers and search context.

Author:

    Arie Gurfinkel
    Anvesh Komuravelli

    Based on muz/pdr/pdr_context.h by Nikolaj Bjorner (nbjorner)

Notes:

--*/

#ifndef _SPACER_CONTEXT_H_
#define _SPACER_CONTEXT_H_

#ifdef _CYGWIN
#undef min
#undef max
#endif
#include <queue>
#include "util/scoped_ptr_vector.h"
#include "muz/spacer/spacer_manager.h"
#include "muz/spacer/spacer_prop_solver.h"
#include "muz/spacer/spacer_json.h"

#include "muz/base/fixedpoint_params.hpp"

namespace datalog {
    class rule_set;
    class context;
};

namespace spacer {

class pred_transformer;
class derivation;
class pob_queue;
class context;

typedef obj_map<datalog::rule const, app_ref_vector*> rule2inst;
typedef obj_map<func_decl, pred_transformer*> decl2rel;

class pob;
typedef ref<pob> pob_ref;
typedef sref_vector<pob> pob_ref_vector;
typedef sref_buffer<pob> pob_ref_buffer;

class reach_fact;
typedef ref<reach_fact> reach_fact_ref;
typedef sref_vector<reach_fact> reach_fact_ref_vector;

class reach_fact {
    unsigned m_ref_count;

    expr_ref m_fact;
    ptr_vector<app> m_aux_vars;

    const datalog::rule &m_rule;
    reach_fact_ref_vector m_justification;

    // variable used to tag this reach fact in an incremental disjunction
    app_ref m_tag;

    bool m_init;

public:
    reach_fact (ast_manager &m, const datalog::rule &rule,
                expr* fact, const ptr_vector<app> &aux_vars,
                bool init = false) :
        m_ref_count (0), m_fact (fact, m), m_aux_vars (aux_vars),
        m_rule(rule), m_tag(m), m_init (init) {}
    reach_fact (ast_manager &m, const datalog::rule &rule,
                expr* fact, bool init = false) :
        m_ref_count (0), m_fact (fact, m), m_rule(rule), m_tag(m), m_init (init) {}

    bool is_init () {return m_init;}
    const datalog::rule& get_rule () {return m_rule;}

    void add_justification (reach_fact *f) {m_justification.push_back (f);}
    const reach_fact_ref_vector& get_justifications () {return m_justification;}

    expr *get () {return m_fact.get ();}
    const ptr_vector<app> &aux_vars () {return m_aux_vars;}

    app* tag() const {SASSERT(m_tag); return m_tag;}
    void set_tag(app* tag) {m_tag = tag;}

    void inc_ref () {++m_ref_count;}
    void dec_ref ()
        {
            SASSERT (m_ref_count > 0);
            --m_ref_count;
            if(m_ref_count == 0) { dealloc(this); }
        }
};


class lemma;
typedef ref<lemma> lemma_ref;
typedef sref_vector<lemma> lemma_ref_vector;

typedef pob pob;

// a lemma
class lemma {
    unsigned m_ref_count;

    ast_manager &m;
    expr_ref m_body;
    expr_ref_vector m_cube;
    app_ref_vector m_zks;
    app_ref_vector m_bindings;
    unsigned m_lvl;            // current level of the lemma
    unsigned m_init_lvl;       // level at which lemma was created
    pob_ref m_pob;
    model_ref m_ctp; // counter-example to pushing
    bool m_external;

    void mk_expr_core();
    void mk_cube_core();
public:
    lemma(ast_manager &manager, expr * fml, unsigned lvl);
    lemma(pob_ref const &p);
    lemma(pob_ref const &p, expr_ref_vector &cube, unsigned lvl);
//    lemma(const lemma &other) = delete;

    ast_manager &get_ast_manager() {return m;}

    model_ref& get_ctp() {return m_ctp;}
    bool has_ctp() {return !is_inductive() && m_ctp;}
    void set_ctp(model_ref &v) {m_ctp = v;}
    void reset_ctp() {m_ctp.reset();}

    expr *get_expr();
    bool is_false();
    expr_ref_vector const &get_cube();
    void update_cube(pob_ref const &p, expr_ref_vector &cube);

    bool has_pob() {return m_pob;}
    pob_ref &get_pob() {return m_pob;}
    inline unsigned weakness();

    void add_skolem(app *zk, app* b);

    inline void set_external(bool ext){m_external = ext;}
    inline bool external() { return m_external;}

    bool is_inductive() const {return is_infty_level(m_lvl);}
    unsigned level () const {return m_lvl;}
    unsigned init_level() const {return m_init_lvl;}
    void set_level (unsigned lvl);
    app_ref_vector& get_bindings() {return m_bindings;}
    bool has_binding(app_ref_vector const &binding);
    void add_binding(app_ref_vector const &binding);
    void instantiate(expr * const * exprs, expr_ref &result, expr *e = nullptr);
    void mk_insts(expr_ref_vector& inst, expr* e = nullptr);
    bool is_ground () {return !is_quantifier (get_expr());}

    void inc_ref () {++m_ref_count;}
    void dec_ref () {
        SASSERT (m_ref_count > 0);
        --m_ref_count;
        if(m_ref_count == 0) {dealloc(this);}
    }
};

struct lemma_lt_proc : public std::binary_function<lemma*, lemma *, bool> {
    bool operator() (lemma *a, lemma *b) {
        return (a->level () < b->level ()) ||
            (a->level () == b->level () &&
             ast_lt_proc() (a->get_expr (), b->get_expr ()));
    }
};



//
// Predicate transformer state.
// A predicate transformer corresponds to the
// set of rules that have the same head predicates.
//

class pred_transformer {

    struct stats {
        unsigned m_num_propagations; // num of times lemma is pushed higher
        unsigned m_num_invariants; // num of infty lemmas found
        unsigned m_num_ctp_blocked; // num of time ctp blocked lemma pushing
        unsigned m_num_is_invariant; // num of times lemmas are pushed
        unsigned m_num_lemma_level_jump; // lemma learned at higher level than expected
        unsigned m_num_reach_queries;

        stats() { reset(); }
        void reset() { memset(this, 0, sizeof(*this)); }
    };

    /// manager of the lemmas in all the frames
#include "muz/spacer/spacer_legacy_frames.h"
    class frames {
    private:
        pred_transformer &m_pt;            // parent pred_transformer
        lemma_ref_vector m_pinned_lemmas;  // all created lemmas
        lemma_ref_vector m_lemmas;         // active lemmas
        unsigned m_size;                   // num of frames

        bool m_sorted;                     // true if m_lemmas is sorted by m_lt
        lemma_lt_proc m_lt;                // sort order for m_lemmas

        void sort ();

    public:
        frames (pred_transformer &pt) : m_pt (pt), m_size(0), m_sorted (true) {}
        ~frames() {}
        void simplify_formulas ();

        pred_transformer& pt () {return m_pt;}


        void get_frame_lemmas (unsigned level, expr_ref_vector &out) const {
            for (auto &lemma : m_lemmas) {
                if (lemma->level() == level) {
                    out.push_back(lemma->get_expr());
                }
            }
        }
        void get_frame_geq_lemmas (unsigned level, expr_ref_vector &out) const {
            for (auto &lemma : m_lemmas) {
                if(lemma->level() >= level) {
                    out.push_back(lemma->get_expr());
                }
            }
        }

        unsigned size () const {return m_size;}
        unsigned lemma_size () const {return m_lemmas.size ();}
        void add_frame () {m_size++;}
        void inherit_frames (frames &other) {
            for (auto &other_lemma : other.m_lemmas) {
                lemma_ref new_lemma = alloc(lemma, m_pt.get_ast_manager(),
                                            other_lemma->get_expr(),
                                            other_lemma->level());
                new_lemma->add_binding(other_lemma->get_bindings());
                add_lemma(new_lemma.get());
            }
            m_sorted = false;
        }

        bool add_lemma (lemma *new_lemma);
        void propagate_to_infinity (unsigned level);
        bool propagate_to_next_level (unsigned level);
    };

    /**
        manager of proof-obligations (pobs)
     */
    class pobs {
        typedef ptr_buffer<pob, 1> pob_buffer;
        typedef obj_map<expr, pob_buffer > expr2pob_buffer;

        pred_transformer &m_pt;

        expr2pob_buffer m_pobs;
        pob_ref_vector m_pinned;
    public:
        pobs(pred_transformer &pt) : m_pt(pt) {}
        pob* mk_pob(pob *parent, unsigned level, unsigned depth,
                    expr *post, app_ref_vector const &b);

        pob* mk_pob(pob *parent, unsigned level, unsigned depth,
                    expr *post) {
            app_ref_vector b(m_pt.get_ast_manager());
            return mk_pob (parent, level, depth, post, b);
        }
        unsigned size() const {return m_pinned.size();}

    };

    typedef obj_map<datalog::rule const, expr*> rule2expr;
    typedef obj_map<datalog::rule const, ptr_vector<app> > rule2apps;
    typedef obj_map<expr, datalog::rule const*> expr2rule;
    manager&                     pm;                // spacer::manager
    ast_manager&                 m;                 // ast_manager
    context&                     ctx;               // spacer::context

    func_decl_ref                m_head;            // predicate
    func_decl_ref_vector         m_sig;             // signature
    ptr_vector<pred_transformer> m_use;             // places where 'this' is referenced.
    ptr_vector<datalog::rule>    m_rules;           // rules used to derive transformer
    scoped_ptr<prop_solver>      m_solver;          // solver context
    ref<solver>                  m_reach_solver;       // context for reachability facts
    pobs                         m_pobs;            // proof obligations created so far
    frames                       m_frames;          // frames with lemmas
    reach_fact_ref_vector        m_reach_facts;     // reach facts
    unsigned                     m_rf_init_sz;      // number of reach fact from INIT
    expr2rule                    m_tag2rule;        // map tag predicate to rule.
    rule2expr                    m_rule2tag;        // map rule to predicate tag.
    rule2expr                    m_rule2transition; // map rules to transition
    rule2apps                    m_rule2vars;       // map rule to auxiliary variables
    expr_ref_vector              m_transition_clause; // extra clause for trans
    expr_ref                     m_transition;      // transition relation
    expr_ref                     m_init;            // initial condition
    app_ref                      m_extend_lit0;     // first literal used to extend initial state
    app_ref                      m_extend_lit;      // current literal to extend initial state
    bool                         m_all_init;        // true if the pt has no uninterpreted body in any rule
    ptr_vector<func_decl>        m_predicates;      // temp vector used with find_predecessors()
    stats                        m_stats;
    stopwatch                    m_initialize_watch;
    stopwatch                    m_must_reachable_watch;
    stopwatch                    m_ctp_watch;
    stopwatch                    m_mbp_watch;

    void init_sig();
    app_ref mk_extend_lit();
    void ensure_level(unsigned level);
    void add_lemma_core (lemma *lemma, bool ground_only = false);
    void add_lemma_from_child (pred_transformer &child, lemma *lemma,
                               unsigned lvl, bool ground_only = false);

    void mk_assumptions(func_decl* head, expr* fml, expr_ref_vector& result);

    // Initialization
    void init_rules(decl2rel const& pts);
    void init_rule(decl2rel const& pts, datalog::rule const& rule, vector<bool>& is_init,
                   ptr_vector<datalog::rule const>& rules, expr_ref_vector& transition);
    void init_atom(decl2rel const& pts, app * atom, app_ref_vector& var_reprs,
                   expr_ref_vector& side, unsigned tail_idx);

    void simplify_formulas(tactic& tac, expr_ref_vector& fmls);

    void add_premises(decl2rel const& pts, unsigned lvl, datalog::rule& rule, expr_ref_vector& r);

    app_ref mk_fresh_rf_tag ();

public:
    pred_transformer(context& ctx, manager& pm, func_decl* head);
    ~pred_transformer();

    inline bool use_native_mbp ();
    reach_fact *get_rf (expr *v) {
        for (auto *rf : m_reach_facts) {
            if (v == rf->get()) {return rf;}
        }
        return nullptr;
    }
    void find_predecessors(datalog::rule const& r, ptr_vector<func_decl>& predicates) const;

    void add_rule(datalog::rule* r) {m_rules.push_back(r);}
    void add_use(pred_transformer* pt) {if(!m_use.contains(pt)) {m_use.insert(pt);}}
    void initialize(decl2rel const& pts);

    func_decl* head() const {return m_head;}
    ptr_vector<datalog::rule> const& rules() const {return m_rules;}
    func_decl* sig(unsigned i) const {return m_sig[i];} // signature
    func_decl* const* sig() {return m_sig.c_ptr();}
    unsigned  sig_size() const {return m_sig.size();}
    expr*  transition() const {return m_transition;}
    expr*  init() const {return m_init;}
    expr*  rule2tag(datalog::rule const* r) {return m_rule2tag.find(r);}
    unsigned get_num_levels() const {return m_frames.size ();}
    expr_ref get_cover_delta(func_decl* p_orig, int level);
    void     add_cover(unsigned level, expr* property);
    expr_ref get_reachable();

    std::ostream& display(std::ostream& strm) const;

    void collect_statistics(statistics& st) const;
    void reset_statistics();

    bool is_must_reachable(expr* state, model_ref* model = nullptr);
    /// \brief Returns reachability fact active in the given model
    /// all determines whether initial reachability facts are included as well
    reach_fact *get_used_rf(model_evaluator_util& mev, bool all = true);
    /// \brief Returns reachability fact active in the origin of the given model
    reach_fact* get_used_origin_rf(model_evaluator_util &mev, unsigned oidx);
    expr_ref get_origin_summary(model_evaluator_util &mev,
                                unsigned level, unsigned oidx, bool must,
                                const ptr_vector<app> **aux);

    bool is_ctp_blocked(lemma *lem);
    const datalog::rule *find_rule(model &mdl);
    const datalog::rule *find_rule(model &mev, bool& is_concrete,
                                   vector<bool>& reach_pred_used,
                                   unsigned& num_reuse_reach);
    expr* get_transition(datalog::rule const& r) { return m_rule2transition.find(&r); }
    ptr_vector<app>& get_aux_vars(datalog::rule const& r) { return m_rule2vars.find(&r); }

    bool propagate_to_next_level(unsigned level);
    void propagate_to_infinity(unsigned level);
    /// \brief  Add a lemma to the current context and all users
    bool add_lemma(expr * lemma, unsigned lvl);
    bool add_lemma(lemma* lem) {return m_frames.add_lemma(lem);}
    expr* get_reach_case_var (unsigned idx) const;
    bool has_rfs () const { return !m_reach_facts.empty () ;}

    /// initialize reachability facts using initial rules
    void init_rfs ();
    reach_fact *mk_rf(pob &n, model_evaluator_util &mev,
                              const datalog::rule &r);
    void add_rf (reach_fact *fact);  // add reachability fact
    reach_fact* get_last_rf () const { return m_reach_facts.back (); }
    expr* get_last_rf_tag () const;

    pob* mk_pob(pob *parent, unsigned level, unsigned depth,
                expr *post, app_ref_vector const &b){
        return m_pobs.mk_pob(parent, level, depth, post, b);
    }

    pob* mk_pob(pob *parent, unsigned level, unsigned depth,
                expr *post) {
        return m_pobs.mk_pob(parent, level, depth, post);
    }

    lbool is_reachable(pob& n, expr_ref_vector* core, model_ref *model,
                       unsigned& uses_level, bool& is_concrete,
                       datalog::rule const*& r,
                       vector<bool>& reach_pred_used,
                       unsigned& num_reuse_reach);
    bool is_invariant(unsigned level, lemma* lem,
                      unsigned& solver_level,
                      expr_ref_vector* core = nullptr);

    bool is_invariant(unsigned level, expr* lem,
                      unsigned& solver_level, expr_ref_vector* core = nullptr) {
        // XXX only needed for legacy_frames to compile
        UNREACHABLE(); return false;
    }

    bool check_inductive(unsigned level, expr_ref_vector& state,
                         unsigned& assumes_level, unsigned weakness = UINT_MAX);

    expr_ref get_formulas(unsigned level) const;

    void simplify_formulas();

    context& get_context () const {return ctx;}
    manager& get_manager() const {return pm;}
    ast_manager& get_ast_manager() const {return m;}

    void add_premises(decl2rel const& pts, unsigned lvl, expr_ref_vector& r);

    void inherit_lemmas(pred_transformer& other);

    void ground_free_vars(expr* e, app_ref_vector& vars, ptr_vector<app>& aux_vars,
                          bool is_init);

    /// \brief Adds a given expression to the set of initial rules
    app* extend_initial (expr *e);

    /// \brief Returns true if the obligation is already blocked by current lemmas
    bool is_blocked (pob &n, unsigned &uses_level);
    /// \brief Returns true if the obligation is already blocked by current quantified lemmas
    bool is_qblocked (pob &n);

    /// \brief interface to Model Based Projection
    void mbp(app_ref_vector &vars, expr_ref &fml, const model_ref &mdl,
             bool reduce_all_selects = true);

    void updt_solver(prop_solver *solver);

    void updt_solver_with_lemmas(prop_solver *solver,
                                 const pred_transformer &pt,
                                 app *rule_tag, unsigned pos);
    void update_solver_with_rfs(prop_solver *solver,
                              const pred_transformer &pt,
                              app *rule_tag, unsigned pos);

};


/**
 * A proof obligation.
 */
class pob {
    friend class context;
    unsigned m_ref_count;
    /// parent node
    pob_ref          m_parent;
    /// predicate transformer
    pred_transformer&       m_pt;
    /// post-condition decided by this node
    expr_ref                m_post;
    // if m_post is not ground, then m_binding is an instantiation for
    // all quantified variables
    app_ref_vector          m_binding;
    /// new post to be swapped in for m_post
    expr_ref                m_new_post;
    /// level at which to decide the post
    unsigned                m_level;

    unsigned                m_depth;

    /// whether a concrete answer to the post is found
    bool                    m_open;
    /// whether to use farkas generalizer to construct a lemma blocking this node
    bool                    m_use_farkas;

    unsigned                m_weakness;
    /// derivation representing the position of this node in the parent's rule
    scoped_ptr<derivation>   m_derivation;

    /// pobs created as children of this pob (at any time, not
    /// necessarily currently active)
    ptr_vector<pob>  m_kids;
    // lemmas created to block this pob (at any time, not necessarily active)
    ptr_vector<lemma> m_lemmas;

    // depth -> watch
    std::map<unsigned, stopwatch> m_expand_watches;
    unsigned m_blocked_lvl;
public:
    pob (pob* parent, pred_transformer& pt,
         unsigned level, unsigned depth=0, bool add_to_parent=true);

    ~pob() {if(m_parent) { m_parent->erase_child(*this); }}

    unsigned weakness() {return m_weakness;}
    void bump_weakness() {m_weakness++;}
    void reset_weakness() {m_weakness=0;}

    void inc_level () {m_level++; m_depth++;reset_weakness();}

    void inherit(pob const &p);
    void set_derivation (derivation *d) {m_derivation = d;}
    bool has_derivation () const {return (bool)m_derivation;}
    derivation &get_derivation() const {return *m_derivation.get ();}
    void reset_derivation () {set_derivation (nullptr);}
    /// detaches derivation from the node without deallocating
    derivation* detach_derivation () {return m_derivation.detach ();}

    pob* parent () const { return m_parent.get (); }

    pred_transformer& pt () const { return m_pt; }
    ast_manager& get_ast_manager () const { return m_pt.get_ast_manager (); }
    manager& get_manager () const { return m_pt.get_manager (); }
    context& get_context () const {return m_pt.get_context ();}

    unsigned level () const { return m_level; }
    unsigned depth () const {return m_depth;}
    unsigned width () const {return m_kids.size();}
    unsigned blocked_at(unsigned lvl=0){return (m_blocked_lvl = std::max(lvl, m_blocked_lvl)); }

    bool use_farkas_generalizer () const {return m_use_farkas;}
    void set_farkas_generalizer (bool v) {m_use_farkas = v;}

    expr* post() const { return m_post.get (); }
    void set_post(expr *post);
    void set_post(expr *post, app_ref_vector const &binding);

    /// indicate that a new post should be set for the node
    void new_post(expr *post) {if(post != m_post) {m_new_post = post;}}
    /// true if the node needs to be updated outside of the priority queue
    bool is_dirty () {return m_new_post;}
    /// clean a dirty node
    void clean();

    void reset () {clean (); m_derivation = nullptr; m_open = true;}

    bool is_closed () const { return !m_open; }
    void close();

    const ptr_vector<pob> &children() {return m_kids;}
    void add_child (pob &v) {m_kids.push_back (&v);}
    void erase_child (pob &v) {m_kids.erase (&v);}

    const ptr_vector<lemma> &lemmas() {return m_lemmas;}
    void add_lemma(lemma* new_lemma) {m_lemmas.push_back(new_lemma);}

    bool is_ground () const { return m_binding.empty (); }
    unsigned get_free_vars_size() const { return m_binding.size(); }
    app_ref_vector const &get_binding() const {return m_binding;}
    /*
     * Returns a map from variable id to skolems that implicitly
     * represent them in the pob. Note that only some (or none) of the
     * skolems returned actually appear in the post of the pob.
     */
    void get_skolems(app_ref_vector& v);

    void on_expand() { m_expand_watches[m_depth].start(); if(m_parent.get()){m_parent.get()->on_expand();} }
    void off_expand() { m_expand_watches[m_depth].stop(); if(m_parent.get()){m_parent.get()->off_expand();} };
    double get_expand_time(unsigned depth) { return m_expand_watches[depth].get_seconds();}

    void inc_ref () {++m_ref_count;}
    void dec_ref () {
        --m_ref_count;
        if(m_ref_count == 0) {dealloc(this);}
    }

    class on_expand_event
    {
        pob &m_p;
    public:
        on_expand_event(pob &p) : m_p(p) {m_p.on_expand();}
        ~on_expand_event() {m_p.off_expand();}
    };
};


struct pob_lt :
        public std::binary_function<const pob*, const pob*, bool>
{bool operator() (const pob *pn1, const pob *pn2) const;};

struct pob_gt :
        public std::binary_function<const pob*, const pob*, bool> {
    pob_lt lt;
    bool operator() (const pob *n1, const pob *n2) const
        {return lt(n2, n1);}
};

struct pob_ref_gt :
        public std::binary_function<const pob_ref&, const model_ref &, bool> {
    pob_gt gt;
    bool operator() (const pob_ref &n1, const pob_ref &n2) const
        {return gt (n1.get (), n2.get ());}
};

inline unsigned lemma::weakness() {return m_pob ? m_pob->weakness() : UINT_MAX;}
/**
 */
class derivation {
    /// a single premise of a derivation
    class premise {
        pred_transformer &m_pt;
        /// origin order in the rule
        unsigned m_oidx;
        /// summary fact corresponding to the premise
        expr_ref m_summary;
        ///  whether this is a must or may premise
        bool m_must;
        app_ref_vector m_ovars;

    public:
        premise (pred_transformer &pt, unsigned oidx, expr *summary, bool must,
                 const ptr_vector<app> *aux_vars = nullptr);
        premise (const premise &p);

        bool is_must() {return m_must;}
        expr * get_summary() {return m_summary.get ();}
        app_ref_vector &get_ovars() {return m_ovars;}
        unsigned get_oidx() {return m_oidx;}
        pred_transformer &pt() {return m_pt;}

        /// \brief Updated the summary.
        /// The new summary is over n-variables.
        void set_summary(expr * summary, bool must,
                         const ptr_vector<app> *aux_vars = nullptr);
    };


    /// parent model node
    pob&                         m_parent;

    /// the rule corresponding to this derivation
    const datalog::rule &m_rule;

    /// the premises
    vector<premise>                     m_premises;
    /// pointer to the active premise
    unsigned                            m_active;
    // transition relation over origin variables
    expr_ref                            m_trans;
    //  implicitly existentially quantified variables in m_trans
    app_ref_vector                      m_evars;
    /// -- create next child using given model as the guide
    /// -- returns NULL if there is no next child
    pob* create_next_child (model_evaluator_util &mev);
    /// existentially quantify vars and skolemize the result
    void exist_skolemize(expr *fml, app_ref_vector &vars, expr_ref &res);
public:
    derivation (pob& parent, datalog::rule const& rule,
                expr *trans, app_ref_vector const &evars);
    void add_premise (pred_transformer &pt, unsigned oidx,
                      expr * summary, bool must, const ptr_vector<app> *aux_vars = nullptr);

    /// creates the first child. Must be called after all the premises
    /// are added. The model must be valid for the premises
    /// Returns NULL if no child exits
    pob *create_first_child (model_evaluator_util &mev);

    /// Create the next child. Must summary of the currently active
    /// premise must be consistent with the transition relation
    pob *create_next_child ();

    datalog::rule const& get_rule () const { return m_rule; }
    pob& get_parent () const { return m_parent; }
    ast_manager &get_ast_manager () const {return m_parent.get_ast_manager ();}
    manager &get_manager () const {return m_parent.get_manager ();}
    context &get_context() const {return m_parent.get_context();}
    pred_transformer &pt() const {return m_parent.pt();}
};


class pob_queue {
    pob_ref  m_root;
    unsigned m_max_level;
    unsigned m_min_depth;

    std::priority_queue<pob_ref, std::vector<pob_ref>,
                        pob_ref_gt>     m_obligations;

public:
    pob_queue(): m_root(nullptr), m_max_level(0), m_min_depth(0) {}
    ~pob_queue();

    void reset();
    pob * top ();
    void pop () {m_obligations.pop ();}
    void push (pob &n);

    void inc_level () {
        SASSERT (!m_obligations.empty () || m_root);
        m_max_level++;
        m_min_depth++;
        if(m_root && m_obligations.empty()) { m_obligations.push(m_root); }
    }

    pob& get_root() const {return *m_root.get ();}
    void set_root(pob& n);
    bool is_root (pob& n) const {return m_root.get () == &n;}

    unsigned max_level() const {return m_max_level;}
    unsigned min_depth() const {return m_min_depth;}
    size_t size() const {return m_obligations.size();}
};


/**
 * Generalizers (strengthens) a lemma
 */
class lemma_generalizer {
protected:
    context& m_ctx;
public:
    lemma_generalizer(context& ctx): m_ctx(ctx) {}
    virtual ~lemma_generalizer() {}
    virtual void operator()(lemma_ref &lemma) = 0;
    virtual void collect_statistics(statistics& st) const {}
    virtual void reset_statistics() {}
};


class spacer_callback {
protected:
    context &m_context;

public:
    spacer_callback(context &context) : m_context(context) {}

    virtual ~spacer_callback() = default;

    context &get_context() { return m_context; }

    virtual inline bool new_lemma() { return false; }

    virtual void new_lemma_eh(expr *lemma, unsigned level) {}

    virtual inline bool predecessor() { return false; }

    virtual void predecessor_eh() {}

    virtual inline bool unfold() { return false; }

    virtual void unfold_eh() {}

    virtual inline bool propagate() { return false; }

    virtual void propagate_eh() {}

};


class context {

    struct stats {
        unsigned m_num_queries;
        unsigned m_num_reuse_reach;
        unsigned m_max_query_lvl;
        unsigned m_max_depth;
        unsigned m_cex_depth;
        unsigned m_expand_pob_undef;
        unsigned m_num_lemmas;
        unsigned m_num_restarts;
        unsigned m_num_lemmas_imported;
        unsigned m_num_lemmas_discarded;
        stats() { reset(); }
        void reset() { memset(this, 0, sizeof(*this)); }
    };

    // stat watches
    stopwatch m_solve_watch;
    stopwatch m_propagate_watch;
    stopwatch m_reach_watch;
    stopwatch m_is_reach_watch;
    stopwatch m_create_children_watch;
    stopwatch m_init_rules_watch;

    fixedpoint_params const&    m_params;
    ast_manager&         m;
    datalog::context*    m_context;
    manager              m_pm;

    // three solver pools for different queries
    scoped_ptr<solver_pool> m_pool0;
    scoped_ptr<solver_pool> m_pool1;
    scoped_ptr<solver_pool> m_pool2;


    decl2rel             m_rels;         // Map from relation predicate to fp-operator.
    func_decl_ref        m_query_pred;
    pred_transformer*    m_query;
    mutable pob_queue    m_pob_queue;
    lbool                m_last_result;
    unsigned             m_inductive_lvl;
    unsigned             m_expanded_lvl;
    ptr_buffer<lemma_generalizer>  m_lemma_generalizers;
    stats                m_stats;
    model_converter_ref  m_mc;
    proof_converter_ref  m_pc;
    bool                 m_use_native_mbp;
    bool                 m_ground_cti;
    bool                 m_instantiate;
    bool                 m_use_qlemmas;
    bool                 m_weak_abs;
    bool                 m_use_restarts;
    unsigned             m_restart_initial_threshold;
    scoped_ptr_vector<spacer_callback> m_callbacks;
    json_marshaller      m_json_marshaller;

    // Functions used by search.
    lbool solve_core(unsigned from_lvl = 0);
    bool is_requeue(pob &n);
    bool check_reachability();
    bool propagate(unsigned min_prop_lvl, unsigned max_prop_lvl,
                   unsigned full_prop_lvl);
    bool is_reachable(pob &n);
    lbool expand_pob(pob &n, pob_ref_buffer &out);
    bool create_children(pob& n, const datalog::rule &r,
                         model_evaluator_util &mdl,
                         const vector<bool>& reach_pred_used,
                         pob_ref_buffer &out);

    expr_ref mk_sat_answer();
    expr_ref mk_unsat_answer() const;
    unsigned get_cex_depth ();

    // Generate inductive property
    void get_level_property(unsigned lvl, expr_ref_vector& res,
                            vector<relation_info> & rs) const;


    // Initialization
    void init_lemma_generalizers();
    void reset_lemma_generalizers();
    void inherit_lemmas(const decl2rel& rels);
    void init_global_smt_params();
    void init_rules(datalog::rule_set& rules, decl2rel& transformers);
    // (re)initialize context with new relations
    void init(const decl2rel &rels);

    bool validate();
    bool check_invariant(unsigned lvl);
    bool check_invariant(unsigned lvl, func_decl* fn);

    void checkpoint();

    void simplify_formulas();

    void dump_json();

    void predecessor_eh();

public:
    /**
       Initial values of predicates are stored in corresponding relations in dctx.
       We check whether there is some reachable state of the relation checked_relation.
    */
    context(fixedpoint_params const&  params, ast_manager& m);
    ~context();

    const fixedpoint_params &get_params() const { return m_params; }
    bool use_native_mbp () {return m_use_native_mbp;}
    bool use_ground_cti () {return m_ground_cti;}
    bool use_instantiate () {return m_instantiate;}
    bool weak_abs() {return m_weak_abs;}
    bool use_qlemmas () {return m_use_qlemmas;}

    ast_manager&      get_ast_manager() const {return m;}
    manager&          get_manager() {return m_pm;}
    decl2rel const&   get_pred_transformers() const {return m_rels;}
    pred_transformer& get_pred_transformer(func_decl* p) const {return *m_rels.find(p);}

    datalog::context& get_datalog_context() const {
        SASSERT(m_context); return *m_context;
    }

    void update_rules(datalog::rule_set& rules);
    lbool solve(unsigned from_lvl = 0);
    lbool solve_from_lvl (unsigned from_lvl);


    expr_ref          get_answer();
    /**
     * get bottom-up (from query) sequence of ground predicate instances
     * (for e.g. P(0,1,0,0,3)) that together form a ground derivation to query
     */
    expr_ref          get_ground_sat_answer ();
    void get_rules_along_trace (datalog::rule_ref_vector& rules);

    void collect_statistics(statistics& st) const;
    void reset_statistics();
    void reset();

    std::ostream& display(std::ostream& out) const;
    void display_certificate(std::ostream& out) const {NOT_IMPLEMENTED_YET();}

    pob& get_root() const {return m_pob_queue.get_root();}
    void set_query(func_decl* q) {m_query_pred = q;}
    void set_unsat() {m_last_result = l_false;}
    void set_model_converter(model_converter_ref& mc) {m_mc = mc;}
    model_converter_ref get_model_converter() { return m_mc; }
    void set_proof_converter(proof_converter_ref& pc) { m_pc = pc; }
    scoped_ptr_vector<spacer_callback> &callbacks() {return m_callbacks;}

    unsigned get_num_levels(func_decl* p);

    expr_ref get_cover_delta(int level, func_decl* p_orig, func_decl* p);
    void add_cover(int level, func_decl* pred, expr* property);
    expr_ref get_reachable (func_decl* p);
    void add_invariant (func_decl *pred, expr* property);
    model_ref get_model();
    proof_ref get_proof() const;

    expr_ref get_constraints (unsigned lvl);
    void add_constraint (expr *c, unsigned lvl);

    void new_lemma_eh(pred_transformer &pt, lemma *lem);
    void new_pob_eh(pob *p);

    bool is_inductive();


    // three different solvers with three different sets of parameters
    // different solvers are used for different types of queries in spacer
    solver* mk_solver0() {return m_pool0->mk_solver();}
    solver* mk_solver1() {return m_pool1->mk_solver();}
    solver* mk_solver2() {return m_pool2->mk_solver();}
};

inline bool pred_transformer::use_native_mbp () {return ctx.use_native_mbp ();}
}

#endif
