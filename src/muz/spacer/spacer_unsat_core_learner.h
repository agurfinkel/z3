#ifndef _SPACER_UNSAT_CORE_LEARNER_H_
#define _SPACER_UNSAT_CORE_LEARNER_H_

#include "ast.h"
#include "spacer_util.h"

#pragma mark - proof iterators

namespace spacer {

    /*
     * iterator, which traverses the proof in depth-first post-order.
     */
    class ProofIteratorPostOrder
    {
    public:
        ProofIteratorPostOrder(proof* refutation, ast_manager& manager);
        bool hasNext();
        proof* next();
        
    private:
        ptr_vector<proof> todo;
        ast_mark visited; // the proof nodes we have already visited
        
        ast_manager& m;
    };

    
    class unsat_core_plugin;
    class unsat_core_learner
    {
        typedef obj_hashtable<expr> expr_set;
        
    public:
        unsat_core_learner(ast_manager& m) : m(m), m_unsat_core(m) {};
        virtual ~unsat_core_learner();
        
        ast_manager& m;
 
        /*
         * register a plugin for computation of partial unsat cores
         * currently plugins are called in the order they have been registered
         */
        void register_plugin(unsat_core_plugin* plugin);
        
        /*
         * compute unsat core using the registered unsat-core-plugins
         */
        void compute_unsat_core(proof* root, expr_set& asserted_b, expr_ref_vector& unsat_core);
        
        /*
         * getter/setter methods for data structures exposed to plugins
         * the following invariants can be assumed and need to be maintained by the plugins:
         *  - a node is a-marked iff it is derived using at least one asserted proof step from A.
         *  - a node is b-marked iff its derivation contains no asserted proof steps from A and
         *    no hypothesis (with the additional complication that lemmas conceptually remove hypothesis)
         *  - a node is h-marked, iff it is derived using at least one hypothesis
         *  - a node is closed, iff it has already been interpolated, i.e. its contribution is
         *    already covered by the unsat-core.
         */
        bool is_a_marked(proof* p);
        bool is_b_marked(proof* p);
        bool is_h_marked(proof* p);
        bool is_closed(proof* p);
        void set_closed(proof* p, bool value);
        
        /*
         * adds a lemma to the unsat core
         */
        void add_lemma_to_core(expr_ref lemma);
        
        /*
         * helper method, which can be used by plugins
         * returns true iff all symbols of expr occur in some b-asserted formula.
         * must only be called after a call to collect_symbols_b.
         */
        bool only_contains_symbols_b(expr* expr) const;
        
    private:
        ptr_vector<unsat_core_plugin> m_plugins;
        func_decl_set m_symbols_b; // symbols, which occur in any b-asserted formula
        void collect_symbols_b(expr_set axioms_b);
        
        ast_mark m_a_mark;
        ast_mark m_b_mark;
        ast_mark m_h_mark;
        ast_mark m_closed;
        
        expr_ref_vector m_unsat_core; // collects the lemmas of the unsat-core, will at the end be inserted into unsat_core.
        
        /*
         * computes partial core for step by delegating computation to plugins
         */
        void compute_partial_core(proof* step);
        
        /*
         * finalize computation of unsat-core
         */
        void finalize();
    };

}

#endif
