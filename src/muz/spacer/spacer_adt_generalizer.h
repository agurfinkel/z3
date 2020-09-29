#pragma once
/*++
  Copyright (c) 2020 Arie Gurfinkel

  Module Name:

  spacer_adt_generalizer.h

  Abstract:

  Generalize lemmas containing ADTs

  Author:

  Hari Govind V K
  Arie Gurfinkel


  --*/

#include "ast/datatype_decl_plugin.h"
#include "muz/spacer/spacer_context.h"

namespace spacer {

class adt_generalizer : public lemma_generalizer {
    ast_manager &m;
    datatype_util m_dt;

    void wrap_accessors(expr_ref &lit, expr_ref &res);

  public:
    adt_generalizer(context &ctx);
    ~adt_generalizer() override {}

    void operator()(lemma_ref &lemma) override;
};

} // namespace spacer
