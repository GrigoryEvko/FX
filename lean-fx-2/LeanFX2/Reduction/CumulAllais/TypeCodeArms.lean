import LeanFX2.Reduction.CumulAllais.ClosedArms

/-! # LeanFX2.Reduction.CumulAllais.TypeCodeArms

Allais arms for the ten CUMUL-2.4 typed type-code constructors:
`arrowCode`, `piTyCode`, `sigmaTyCode`, `productCode`, `sumCode`,
`listCode`, `optionCode`, `eitherCode`, `idCode`, `equivCode`.

All ten ctors are VALUE-shaped (schematic raw payloads, no recursive
typed subterms).  Their `substHet` arms in `Term/SubstHet.lean`
depend ONLY on `sigma`/`sigma.forRaw`/`sigma.forRaw.lift` — never on
the TermSubst values themselves.  Both `termSubstA` and `termSubstB`
share the same `sigma`, so both sides reduce to the SAME substituted
ctor application; `ConvCumul.refl` discharges.

Mirror of `subst_compatible_funextIntroHet_allais` in
`ClosedArms.lean`.

## Root status

Layer 3 cumulativity-via-Allais helper. -/

namespace LeanFX2

/-! ## CUMUL-2.4 typed type-code constructors — Allais helpers.

All ten new ctors are VALUE-shaped (schematic raw payloads, no
recursive typed subterms).  Their `substHet` arms in
`Term/SubstHet.lean` depend ONLY on `sigma`/`sigma.forRaw`/
`sigma.forRaw.lift` — never on the TermSubst values themselves.
Both `termSubstA` and `termSubstB` share the same `sigma`, so both
sides reduce to the SAME substituted ctor application; `ConvCumul.refl`
discharges.  Mirror of `subst_compatible_funextIntroHet_allais`. -/

theorem ConvCumul.subst_compatible_arrowCode_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ sourceLevel)
    (domainCodeRaw codomainCodeRaw : RawTerm sourceScope) :
    ConvCumul ((Term.arrowCode (context := sourceCtx)
                               outerLevel levelLe
                               domainCodeRaw codomainCodeRaw).substHet termSubstA)
              ((Term.arrowCode (context := sourceCtx)
                               outerLevel levelLe
                               domainCodeRaw codomainCodeRaw).substHet termSubstB) :=
  ConvCumul.refl _

theorem ConvCumul.subst_compatible_piTyCode_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ sourceLevel)
    (domainCodeRaw : RawTerm sourceScope)
    (codomainCodeRaw : RawTerm (sourceScope + 1)) :
    ConvCumul ((Term.piTyCode (context := sourceCtx)
                              outerLevel levelLe
                              domainCodeRaw codomainCodeRaw).substHet termSubstA)
              ((Term.piTyCode (context := sourceCtx)
                              outerLevel levelLe
                              domainCodeRaw codomainCodeRaw).substHet termSubstB) :=
  ConvCumul.refl _

theorem ConvCumul.subst_compatible_sigmaTyCode_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ sourceLevel)
    (domainCodeRaw : RawTerm sourceScope)
    (codomainCodeRaw : RawTerm (sourceScope + 1)) :
    ConvCumul ((Term.sigmaTyCode (context := sourceCtx)
                                 outerLevel levelLe
                                 domainCodeRaw codomainCodeRaw).substHet termSubstA)
              ((Term.sigmaTyCode (context := sourceCtx)
                                 outerLevel levelLe
                                 domainCodeRaw codomainCodeRaw).substHet termSubstB) :=
  ConvCumul.refl _

theorem ConvCumul.subst_compatible_productCode_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ sourceLevel)
    (firstCodeRaw secondCodeRaw : RawTerm sourceScope) :
    ConvCumul ((Term.productCode (context := sourceCtx)
                                 outerLevel levelLe
                                 firstCodeRaw secondCodeRaw).substHet termSubstA)
              ((Term.productCode (context := sourceCtx)
                                 outerLevel levelLe
                                 firstCodeRaw secondCodeRaw).substHet termSubstB) :=
  ConvCumul.refl _

theorem ConvCumul.subst_compatible_sumCode_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ sourceLevel)
    (leftCodeRaw rightCodeRaw : RawTerm sourceScope) :
    ConvCumul ((Term.sumCode (context := sourceCtx)
                             outerLevel levelLe
                             leftCodeRaw rightCodeRaw).substHet termSubstA)
              ((Term.sumCode (context := sourceCtx)
                             outerLevel levelLe
                             leftCodeRaw rightCodeRaw).substHet termSubstB) :=
  ConvCumul.refl _

theorem ConvCumul.subst_compatible_listCode_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ sourceLevel)
    (elementCodeRaw : RawTerm sourceScope) :
    ConvCumul ((Term.listCode (context := sourceCtx)
                              outerLevel levelLe
                              elementCodeRaw).substHet termSubstA)
              ((Term.listCode (context := sourceCtx)
                              outerLevel levelLe
                              elementCodeRaw).substHet termSubstB) :=
  ConvCumul.refl _

theorem ConvCumul.subst_compatible_optionCode_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ sourceLevel)
    (elementCodeRaw : RawTerm sourceScope) :
    ConvCumul ((Term.optionCode (context := sourceCtx)
                                outerLevel levelLe
                                elementCodeRaw).substHet termSubstA)
              ((Term.optionCode (context := sourceCtx)
                                outerLevel levelLe
                                elementCodeRaw).substHet termSubstB) :=
  ConvCumul.refl _

theorem ConvCumul.subst_compatible_eitherCode_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ sourceLevel)
    (leftCodeRaw rightCodeRaw : RawTerm sourceScope) :
    ConvCumul ((Term.eitherCode (context := sourceCtx)
                                outerLevel levelLe
                                leftCodeRaw rightCodeRaw).substHet termSubstA)
              ((Term.eitherCode (context := sourceCtx)
                                outerLevel levelLe
                                leftCodeRaw rightCodeRaw).substHet termSubstB) :=
  ConvCumul.refl _

theorem ConvCumul.subst_compatible_idCode_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ sourceLevel)
    (typeCodeRaw leftRaw rightRaw : RawTerm sourceScope) :
    ConvCumul ((Term.idCode (context := sourceCtx)
                            outerLevel levelLe
                            typeCodeRaw leftRaw rightRaw).substHet termSubstA)
              ((Term.idCode (context := sourceCtx)
                            outerLevel levelLe
                            typeCodeRaw leftRaw rightRaw).substHet termSubstB) :=
  ConvCumul.refl _

theorem ConvCumul.subst_compatible_equivCode_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ sourceLevel)
    (leftTypeCodeRaw rightTypeCodeRaw : RawTerm sourceScope) :
    ConvCumul ((Term.equivCode (context := sourceCtx)
                               outerLevel levelLe
                               leftTypeCodeRaw rightTypeCodeRaw).substHet termSubstA)
              ((Term.equivCode (context := sourceCtx)
                               outerLevel levelLe
                               leftTypeCodeRaw rightTypeCodeRaw).substHet termSubstB) :=
  ConvCumul.refl _

end LeanFX2
