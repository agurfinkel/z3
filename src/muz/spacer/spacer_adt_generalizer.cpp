/*++
Copyright (c) 2020 Arie Gurfinkel

Module Name:

  spacer_adt_generalizer.cpp

Abstract:

  generalize adts
Author:

  Hari Govind V K
  Arie Gurfinkel


--*/
#include "muz/spacer/spacer_adt_generalizer.h"
#include "ast/for_each_expr.h"
#include "ast/rewriter/rewriter.h"
#include "ast/rewriter/rewriter_def.h"
namespace {
namespace has_adt_proc_ns {
struct found {};
struct has_adt_proc {
    ast_manager &m;
    datatype_util m_dt;
    has_adt_proc(ast_manager &a_m) : m(a_m), m_dt(m) {}
    void operator()(expr *n) const {}
    void operator()(app *n) {
        if (m_dt.is_accessor(n)) throw found();
    }
};
} // namespace has_adt_proc_ns
bool has_adt(expr_ref &c) {
    ast_manager &m = c.get_manager();
    has_adt_proc_ns::has_adt_proc t(m);
    try {
        for_each_expr(t, c);
        return false;
    } catch (const has_adt_proc_ns::found &) { return true; }
}
} // namespace

namespace spacer {

adt_generalizer::adt_generalizer(context &ctx)
    : lemma_generalizer(ctx), m(ctx.get_ast_manager()), m_dt(m) {}

void adt_generalizer::operator()(lemma_ref &lemma) {
    expr_ref_vector cube = lemma->get_cube();
    expr_ref res(m), lit(m);
    for (unsigned i = 0, n = cube.size(); i < n; i++) {
        lit = cube.get(i);
        if (!has_adt(lit)) continue;
        wrap_accessors(lit, res);
        cube[i] = res;
    }
    lemma->update_cube(lemma->get_pob(), cube);
}

struct wrap_accessor_cfg : public default_rewriter_cfg {
    ast_manager &m;
    datatype_util m_dt;
    wrap_accessor_cfg(ast_manager &a_m) : m(a_m), m_dt(m) {}
    br_status reduce_app(func_decl *f, unsigned num, expr *const *args,
                         expr_ref &result, proof_ref &result_pr) {
        if (m.is_ite(f)) return BR_DONE;
        expr_ref_buffer new_args(m);
        expr_ref kid(m), cond(m), def(m);
        func_decl *c_decl, *is_decl;
        for (unsigned i = 0; i < num; i++) {
            if (m_dt.is_accessor(args[i])) {
                app *a = to_app(args[i]);
                if (a->get_num_args() != 1) { NOT_IMPLEMENTED_YET(); }
                kid = a->get_arg(0);
                c_decl = m_dt.get_accessor_constructor(a->get_decl());
                if (is_uninterp_const(kid)) {
                    is_decl = m_dt.get_constructor_is(c_decl);
                    cond = m.mk_app(is_decl, kid);
                    def = m.get_some_value(a->get_decl()->get_range());
                    kid = m.mk_ite(cond, args[i], def);
                    new_args.push_back(kid);
                    continue;
                }
            }
            new_args.push_back(args[i]);
        }
        TRACE("adt_gen", tout << "rewritting " << f->get_name();
              for (unsigned i = 0; i < num; i++) tout << mk_pp(args[i], m) << " ";
              tout << "\n";);

        result = m.mk_app(f, num, new_args.c_ptr());
        TRACE("adt_gen", tout << "to " << result << "\n";);
        return BR_DONE;
    }
};

void adt_generalizer::wrap_accessors(expr_ref &lit, expr_ref &res) {
    wrap_accessor_cfg dt_rw(m);
    rewriter_tpl<wrap_accessor_cfg> rw(m, false, dt_rw);
    rw(lit, res);
}
} // namespace spacer
template class rewriter_tpl<spacer::wrap_accessor_cfg>;
