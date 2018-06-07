/*++
Copyright (c) 2017 Arie Gurfinkel

Module Name:

    spacer_proof_utils.cpp

Abstract:
    Utilities to traverse and manipulate proofs

Author:
    Bernhard Gleiss
    Arie Gurfinkel

Revision History:

--*/

#include "util/params.h"
#include "ast/ast_pp.h"
#include "ast/ast_util.h"
#include "ast/proofs/proof_checker.h"
#include "muz/base/dl_util.h"
#include "muz/spacer/spacer_iuc_proof.h"

#include "ast/proofs/proof_utils.h"
#include "muz/spacer/spacer_proof_utils.h"
#include "muz/spacer/spacer_util.h"

namespace spacer {

// arithmetic lemma recognizer
bool is_arith_lemma(ast_manager& m, proof* pr)
{
    // arith lemmas: second parameter specifies exact type of lemma,
    // could be "farkas", "triangle-eq", "eq-propagate",
    // "assign-bounds", maybe also something else
    if (pr->get_decl_kind() == PR_TH_LEMMA) {
        func_decl* d = pr->get_decl();
        symbol sym;
        return d->get_num_parameters() >= 1 &&
            d->get_parameter(0).is_symbol(sym) &&
            sym == "arith";
    }
    return false;
}

// farkas lemma recognizer
bool is_farkas_lemma(ast_manager& m, proof* pr)
{
    if (pr->get_decl_kind() == PR_TH_LEMMA)
    {
        func_decl* d = pr->get_decl();
        symbol sym;
        return d->get_num_parameters() >= 2 &&
            d->get_parameter(0).is_symbol(sym) && sym == "arith" &&
            d->get_parameter(1).is_symbol(sym) && sym == "farkas";
    }
    return false;
}


/*
 * ====================================
 * methods for transforming proofs
 * ====================================
 */

void theory_axiom_reducer::reset() {
    m_cache.reset();
    m_pinned.reset();
}

// -- rewrite theory axioms into theory lemmas
proof_ref theory_axiom_reducer::reduce(proof* pr) {
    proof_post_order pit(pr, m);
    while (pit.hasNext()) {
        proof* p = pit.next();

        if (m.get_num_parents(p) == 0 && is_arith_lemma(m, p)) {
            // we have an arith-theory-axiom and want to get rid of it
            // we need to replace the axiom with
            // (a) corresponding hypothesis,
            // (b) a theory lemma, and
            // (c) a lemma.
            // Furthermore update data-structures
            app *fact = to_app(m.get_fact(p));
            ptr_buffer<expr> cls;
            if (m.is_or(fact)) {
                for (unsigned i = 0, sz = fact->get_num_args(); i < sz; ++i)
                 cls.push_back(fact->get_arg(i));
            }
            else
                cls.push_back(fact);

            // (a) create hypothesis
            ptr_buffer<proof> hyps;
            for (unsigned i = 0, sz = cls.size(); i < sz; ++i) {
                expr *c;
                expr_ref hyp_fact(m);
                if (m.is_not(cls[i], c))
                    hyp_fact = c;
                else
                    hyp_fact = m.mk_not (cls[i]);

                proof* hyp = m.mk_hypothesis(hyp_fact);
                m_pinned.push_back(hyp);
                hyps.push_back(hyp);
            }

            // (b) create farkas lemma. Rebuild parameters since
            // mk_th_lemma() adds tid as first parameter
            unsigned num_params = p->get_decl()->get_num_parameters();
            parameter const* params = p->get_decl()->get_parameters();
            vector<parameter> parameters;
            for (unsigned i = 1; i < num_params; ++i) parameters.push_back(params[i]);

            SASSERT(params[0].is_symbol());
            family_id tid = m.mk_family_id(params[0].get_symbol());
            SASSERT(tid != null_family_id);

            proof* th_lemma = m.mk_th_lemma(tid, m.mk_false(),
                                            hyps.size(), hyps.c_ptr(),
                                            num_params-1, parameters.c_ptr());
            m_pinned.push_back(th_lemma);
            SASSERT(is_arith_lemma(m, th_lemma));

            // (c) create lemma
            proof* res = m.mk_lemma(th_lemma, fact);
            m_pinned.push_back(res);
            m_cache.insert(p, res);

            SASSERT(m.get_fact(res) == m.get_fact(p));
        }
        else {
            // proof is dirty, if a sub-proof of one of its premises
            // has been transformed
            bool dirty = false;

            ptr_buffer<expr> args;
            for (unsigned i = 0, sz = m.get_num_parents(p); i < sz; ++i) {
                proof *pp, *tmp;
                pp = m.get_parent(p, i);
                VERIFY(m_cache.find(pp, tmp));
                args.push_back(tmp);
                dirty |= (pp != tmp);
            }
            // if not dirty just use the old step
            if (!dirty) m_cache.insert(p, p);
            // otherwise create new proof with the corresponding proofs
            // of the premises
            else {
                if (m.has_fact(p)) args.push_back(m.get_fact(p));

                SASSERT(p->get_decl()->get_arity() == args.size());

                proof* res = m.mk_app(p->get_decl(),
                                      args.size(), (expr * const*)args.c_ptr());
                m_pinned.push_back(res);
                m_cache.insert(p, res);
            }
        }
    }

    proof* res;
    VERIFY(m_cache.find(pr,res));
    DEBUG_CODE(
        proof_checker pc(m);
        expr_ref_vector side(m);
        SASSERT(pc.check(res, side));
        );

    return proof_ref(res, m);
}

/* ------------------------------------------------------------------------- */
/* hypothesis_reducer */
/* ------------------------------------------------------------------------- */

proof_ref hypothesis_reducer::reduce(proof* pr) {
    compute_hypsets(pr);
    collect_units(pr);

    proof_ref res(reduce_core(pr), m);
    SASSERT(res);
    reset();

    DEBUG_CODE(proof_checker pc(m);
               expr_ref_vector side(m);
               SASSERT(pc.check(res, side)););
    return res;
}

void hypothesis_reducer::reset() {
    m_active_hyps.reset();
    m_units.reset();
    m_cache.reset();
    for (auto t : m_pinned_active_hyps) dealloc(t);
    m_pinned_active_hyps.reset();
    m_pinned.reset();
    m_hyp_mark.reset();
    m_open_mark.reset();
    m_visited.reset();
}

void hypothesis_reducer::compute_hypsets(proof *pr) {
    ptr_buffer<proof> todo;
    todo.push_back(pr);

    while (!todo.empty()) {
        proof* p = todo.back();

        if (m_visited.is_marked(p)) {
            todo.pop_back();
            continue;
        }

        unsigned todo_sz = todo.size();
        for (unsigned i = 0, sz = m.get_num_parents(p); i < sz; ++i) {
            SASSERT(m.is_proof(p->get_arg(i)));
            proof *parent = to_app(p->get_arg(i));

            if (!m_visited.is_marked(parent))
                todo.push_back(parent);
        }
        if (todo.size() > todo_sz) continue;

        todo.pop_back();

        m_visited.mark(p);


        proof_ptr_vector* active_hyps = nullptr;
        // fill both sets
        if (m.is_hypothesis(p)) {
            // create active_hyps-set for step p
            proof_ptr_vector* active_hyps = alloc(proof_ptr_vector);
            m_pinned_active_hyps.insert(active_hyps);
            m_active_hyps.insert(p, active_hyps);
            active_hyps->push_back(p);
            m_open_mark.mark(p);
            m_hyp_mark.mark(m.get_fact(p));
            continue;
        }

        ast_fast_mark1 seen;

        active_hyps = alloc(proof_ptr_vector);
        for (unsigned i = 0, sz = m.get_num_parents(p); i < sz; ++i) {
            proof* parent = m.get_parent(p, i);
            // lemmas clear all hypotheses above them
            if (m.is_lemma(p)) continue;
            for (auto *x : *m_active_hyps.find(parent)) {
                if (!seen.is_marked(x)) {
                    seen.mark(x);
                    active_hyps->push_back(x);
                    m_open_mark.mark(p);
                }
            }
        }
        if (active_hyps->empty()) {
            dealloc(active_hyps);
            m_active_hyps.insert(p, &m_empty_vector);
        }
        else {
            m_pinned_active_hyps.push_back(active_hyps);
            m_active_hyps.insert(p, active_hyps);
        }
    }
}

// collect all units that are hyp-free and are used as hypotheses somewhere
// requires that m_active_hyps has been computed
void hypothesis_reducer::collect_units(proof* pr) {

    proof_post_order pit(pr, m);
    while (pit.hasNext()) {
        proof* p = pit.next();
        if (!m.is_hypothesis(p)) {
            // collect units that are hyp-free and are used as
            // hypotheses in the proof pr
            if (!m_open_mark.is_marked(p) && m.has_fact(p) &&
                m_hyp_mark.is_marked(m.get_fact(p)))
                m_units.insert(m.get_fact(p), p);
        }
    }
}

/**
   \brief returns true if p is an ancestor of q
 */
bool hypothesis_reducer::is_ancestor(proof *p, proof *q) {
    if (p == q) return true;
    ptr_vector<proof> todo;
    todo.push_back(q);

    expr_mark visited;
    while (!todo.empty()) {
        proof *cur;
        cur = todo.back();
        todo.pop_back();

        if (visited.is_marked(cur)) continue;

        if (cur == p) return true;
        visited.mark(cur);

        for (unsigned i = 0, sz = m.get_num_parents(cur); i < sz; ++i) {
            todo.push_back(m.get_parent(cur, i));
        }
    }
    return false;
}

proof* hypothesis_reducer::reduce_core(proof* pf) {
    SASSERT(m.is_false(m.get_fact(pf)));

    proof *res = NULL;

    ptr_vector<proof> todo;
    todo.push_back(pf);
    ptr_buffer<proof> args;
    bool dirty = false;

    while (true) {
        proof *p, *tmp, *pp;
        unsigned todo_sz;

        p = todo.back();
        if (m_cache.find(p, tmp)) {
            todo.pop_back();
            continue;
        }

        dirty = false;
        args.reset();
        todo_sz = todo.size();
        for (unsigned i = 0, sz = m.get_num_parents(p); i < sz; ++i) {
            pp = m.get_parent(p, i);
            if (m_cache.find(pp, tmp)) {
                args.push_back(tmp);
                dirty |= pp != tmp;
            } else {
                todo.push_back(pp);
            }
        }

        if (todo_sz < todo.size()) continue;

        todo.pop_back();

        // transform the current proof node

        if (m.is_hypothesis(p)) {
            // if possible, replace a hypothesis by a unit derivation
            if (m_units.find(m.get_fact(p), tmp)) {
                // use already transformed proof of the unit if it is available
                proof* proof_of_unit;
                if (!m_cache.find(tmp, proof_of_unit)) {
                    proof_of_unit = tmp;
                }

                // make sure hypsets for the unit are computed
                // AG: is this needed?
                compute_hypsets(proof_of_unit);

                // if the transformation doesn't create a cycle, perform it
                if (!is_ancestor(p, proof_of_unit)) {
                    res = proof_of_unit;
                }
                else {
                    // -- failed to transform the proof, perhaps bad
                    // -- choice of the proof of unit
                    res = p;
                }
            }
            else {
                // -- no unit found to replace the hypothesis
                res = p;
            }
        }

        else if (!dirty) {res = p;}

        else if (m.is_lemma(p)) {
            // lemma: reduce the premise; remove reduced consequences
            // from conclusion
            SASSERT(args.size() == 1);
            res = mk_lemma_core(args[0], m.get_fact(p));
            // -- re-compute hypsets
            compute_hypsets(res);
        }
        else if (m.is_unit_resolution(p)) {
            // unit: reduce untis; reduce the first premise; rebuild
            // unit resolution
            res = mk_unit_resolution_core(p, args);
            // -- re-compute hypsets
            compute_hypsets(res);
        }
        else {
            res = mk_proof_core(p, args);
            // -- re-compute hypsets
            compute_hypsets(res);
        }

        SASSERT(res);
        m_cache.insert(p, res);

        // bail out as soon as found a sub-proof of false
        if (!m_open_mark.is_marked(res) && m.has_fact(res) && m.is_false(m.get_fact(res)))
            return res;
    }
    UNREACHABLE();
    return nullptr;
}

proof* hypothesis_reducer::mk_lemma_core(proof* premise, expr *fact) {
    SASSERT(m.is_false(m.get_fact(premise)));
    SASSERT(m_active_hyps.contains(premise));

    proof_ptr_vector* active_hyps = m_active_hyps.find(premise);

    // if there is no active hypothesis return the premise
    if (!m_open_mark.is_marked(premise)) {
        // XXX just in case premise might go away
        m_pinned.push_back(premise);
        return premise;
    }

    // add some stability
    std::stable_sort(active_hyps->begin(), active_hyps->end(), ast_lt_proc());
    // otherwise, build a disjunction of the negated active hypotheses
    // and add a lemma proof step
    expr_ref_buffer args(m);
    for (auto hyp : *active_hyps) {
        expr *hyp_fact, *t;
        hyp_fact = m.get_fact(hyp);
        if (m.is_not(hyp_fact, t))
            args.push_back(t);
        else
            args.push_back(m.mk_not(hyp_fact));
    }

    expr_ref lemma(m);
    lemma = mk_or(m, args.size(), args.c_ptr());

    proof* res;
    res = m.mk_lemma(premise, lemma);
    m_pinned.push_back(res);
    return res;
}

proof* hypothesis_reducer::mk_unit_resolution_core(proof *ures,
                                                   ptr_buffer<proof>& args) {
    // if any literal is false, we don't need a unit resolution step
    // This can be the case due to some previous transformations
    for (unsigned i = 1, sz = args.size(); i < sz; ++i) {
        if (m.is_false(m.get_fact(args[i]))) {
            // XXX pin just in case
            m_pinned.push_back(args[i]);
            return args[i];
        }
    }

    proof* arg0 = args[0];
    app *fact0 = to_app(m.get_fact(arg0));


    ptr_buffer<proof> pf_args;
    ptr_buffer<expr> pf_fact;
    pf_args.push_back(arg0);

    // compute literals to be resolved
    ptr_buffer<expr> lits;

    // fact0 is a literal whenever the original resolution was a
    // binary resolution to an empty clause
    if (m.get_num_parents(ures) == 2 && m.is_false(m.get_fact(ures))) {
        lits.push_back(fact0);
    }
    // fact0 is a literal unless it is a dijsunction
    else if (!m.is_or(fact0)) {
        lits.push_back(fact0);
    }
    // fact0 is a literal only if it appears as a literal in the
    // original resolution
    else {
        lits.reset();
        app* ures_fact = to_app(m.get_fact(m.get_parent(ures, 0)));
        for (unsigned i = 0, sz = ures_fact->get_num_args(); i < sz; ++i) {
            if (ures_fact->get_arg(i) == fact0) {
                lits.push_back(fact0);
                break;
            }
        }
        if (lits.empty()) {
            lits.append(fact0->get_num_args(), fact0->get_args());
        }

    }

    // -- find all literals that are resolved on
    for (unsigned i = 0, sz = lits.size(); i < sz; ++i) {
        bool found = false;
        for (unsigned j = 1; j < args.size(); ++j) {
            if (m.is_complement(lits.get(i), m.get_fact(args[j]))) {
                found = true;
                pf_args.push_back(args[j]);
                break;
            }
        }
        if (!found) {pf_fact.push_back(lits.get(i));}
    }

    // unit resolution got reduced to noop
    if (pf_args.size() == 1) {
        // XXX pin just in case
        m_pinned.push_back(arg0);

        return arg0;
    }

    // make unit resolution proof step
    // expr_ref tmp(m);
    // tmp = mk_or(m, pf_fact.size(), pf_fact.c_ptr());
    // proof* res = m.mk_unit_resolution(pf_args.size(), pf_args.c_ptr(), tmp);
    proof *res = m.mk_unit_resolution(pf_args.size(), pf_args.c_ptr());
    m_pinned.push_back(res);

    return res;
}

proof* hypothesis_reducer::mk_proof_core(proof* old, ptr_buffer<proof>& args) {
    // if any of the literals are false, we don't need a step
    for (unsigned i = 0; i < args.size(); ++i) {
        if (m.is_false(m.get_fact(args[i]))) {
            // XXX just in case
            m_pinned.push_back(args[i]);
            return args[i];
        }
    }

    // otherwise build step
    // BUG: I guess this doesn't work with quantifiers (since they are no apps)
    args.push_back(to_app(m.get_fact(old)));

    SASSERT(old->get_decl()->get_arity() == args.size());

    proof* res = m.mk_app(old->get_decl(), args.size(),
                          (expr * const*)args.c_ptr());
    m_pinned.push_back(res);
    return res;
}

};
