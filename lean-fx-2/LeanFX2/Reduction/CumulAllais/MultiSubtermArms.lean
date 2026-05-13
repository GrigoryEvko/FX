import LeanFX2.Reduction.CumulAllais.RecordSessionArms

/-! # LeanFX2.Reduction.CumulAllais.MultiSubtermArms

Allais arms for the parametric closed-payload + single-subterm
pair-projection + multi-subterm Term ctors:

* Parametric closed-payload (carry no scope-dep substituents):
  `listNil`, `optionNone`, `refl`.
* Single-subterm pair projections: `fst`, `snd`.
* Multi-subterm cong arms: `app`, `appPi`, `pair`, `listCons`,
  `idJ`, `oeqRefl`, `oeqJ`, `oeqFunext`, `idStrictRefl`,
  `idStrictRec`, `boolElim`.

The `appPi` / `pair` / `snd` / `oeqFunext` / `boolElim` arms use
`ConvCumul.cast_eq_both_benton` to peel BHKM-style
`Ty.subst0_substHet_commute` casts produced by `Term.substHet`.

## Root status

Layer 3 cumulativity-via-Allais helper. -/

namespace LeanFX2

/-! ### Allais closed-payload arms (parametric data + refl)

Like `unit` / `boolTrue`, these ctors carry no scope-dependent
substituents.  Both `Term.substHet` calls produce identical
output → `ConvCumul.refl _`. -/

/-- Allais arm for `listNil`: closed-payload, refl. -/
theorem ConvCumul.subst_compatible_listNil_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma)
    (elementType : Ty sourceLevel sourceScope) :
    ConvCumul ((Term.listNil (context := sourceCtx)
                             (elementType := elementType)).substHet termSubstA)
              ((Term.listNil (context := sourceCtx)
                             (elementType := elementType)).substHet termSubstB) :=
  ConvCumul.refl _

/-- Allais arm for `optionNone`: closed-payload, refl. -/
theorem ConvCumul.subst_compatible_optionNone_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma)
    (elementType : Ty sourceLevel sourceScope) :
    ConvCumul ((Term.optionNone (context := sourceCtx)
                                (elementType := elementType)).substHet termSubstA)
              ((Term.optionNone (context := sourceCtx)
                                (elementType := elementType)).substHet termSubstB) :=
  ConvCumul.refl _

/-- Allais arm for `refl` (identity-type witness): closed-payload
because `Term.refl` carries only Ty + RawTerm payload, no typed
subterms.  Both substituted sides produce the same `Term.refl`. -/
theorem ConvCumul.subst_compatible_refl_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma)
    (carrier : Ty sourceLevel sourceScope)
    (rawWitness : RawTerm sourceScope) :
    ConvCumul ((Term.refl (context := sourceCtx) carrier rawWitness).substHet termSubstA)
              ((Term.refl (context := sourceCtx) carrier rawWitness).substHet termSubstB) :=
  ConvCumul.refl _

/-! ### Allais single-subterm pair-projection arms

Term ctors that take a single Σ-pair as substituent.  Recurse
into pair compat, apply matching projection cong rule. -/

/-- Allais arm for `fst`: single-subterm cong via `fstCong`. -/
theorem ConvCumul.subst_compatible_fst_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    {firstType : Ty sourceLevel sourceScope}
    {secondType : Ty sourceLevel (sourceScope + 1)}
    {pairRaw : RawTerm sourceScope}
    (pairTerm : Term sourceCtx (Ty.sigmaTy firstType secondType) pairRaw)
    (pairCompat :
      ConvCumul (pairTerm.substHet termSubstA)
                (pairTerm.substHet termSubstB)) :
    ConvCumul ((Term.fst pairTerm).substHet termSubstA)
              ((Term.fst pairTerm).substHet termSubstB) :=
  ConvCumul.fstCong pairCompat

/-- Allais arm for `snd`: single-subterm cong via `sndCong` plus
BHKM cast handling.

`Term.substHet`'s `snd` arm wraps the result in
`(Ty.subst0_substHet_commute ...).symm ▸ Term.snd (...)`.  We
peel the cast via `ConvCumul.cast_eq_both_benton` (defined in
the Benton section below). -/
theorem ConvCumul.subst_compatible_snd_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    {firstType : Ty sourceLevel sourceScope}
    {secondType : Ty sourceLevel (sourceScope + 1)}
    {pairRaw : RawTerm sourceScope}
    (pairTerm : Term sourceCtx (Ty.sigmaTy firstType secondType) pairRaw)
    (pairCompat :
      ConvCumul (pairTerm.substHet termSubstA)
                (pairTerm.substHet termSubstB)) :
    ConvCumul ((Term.snd pairTerm).substHet termSubstA)
              ((Term.snd pairTerm).substHet termSubstB) :=
  ConvCumul.cast_eq_both_benton _
    (ConvCumul.sndCong pairCompat)

/-! ### Allais multi-subterm cong arms

Term ctors with two or more substituent subterms.  Recurse into
each inner ConvCumul witness; apply multi-arg cong rule. -/

/-- Allais arm for `app`: two-subterm cong via `appCong`. -/
theorem ConvCumul.subst_compatible_app_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    {domainType codomainType : Ty sourceLevel sourceScope}
    {functionRaw argumentRaw : RawTerm sourceScope}
    (functionTerm : Term sourceCtx (Ty.arrow domainType codomainType) functionRaw)
    (argumentTerm : Term sourceCtx domainType argumentRaw)
    (functionCompat :
      ConvCumul (functionTerm.substHet termSubstA)
                (functionTerm.substHet termSubstB))
    (argumentCompat :
      ConvCumul (argumentTerm.substHet termSubstA)
                (argumentTerm.substHet termSubstB)) :
    ConvCumul ((Term.app functionTerm argumentTerm).substHet termSubstA)
              ((Term.app functionTerm argumentTerm).substHet termSubstB) :=
  ConvCumul.appCong functionCompat argumentCompat

/-- Allais arm for `appPi`: two-subterm cong via `appPiCong` plus
BHKM cast handling.

`Term.substHet`'s `appPi` arm wraps the result in
`(Ty.subst0_substHet_commute ...).symm ▸ Term.appPi ...`.  Same
cast on both sides → `cast_eq_both_benton` peels it. -/
theorem ConvCumul.subst_compatible_appPi_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    {domainType : Ty sourceLevel sourceScope}
    {codomainType : Ty sourceLevel (sourceScope + 1)}
    {functionRaw argumentRaw : RawTerm sourceScope}
    (functionTerm :
      Term sourceCtx (Ty.piTy domainType codomainType) functionRaw)
    (argumentTerm : Term sourceCtx domainType argumentRaw)
    (functionCompat :
      ConvCumul (functionTerm.substHet termSubstA)
                (functionTerm.substHet termSubstB))
    (argumentCompat :
      ConvCumul (argumentTerm.substHet termSubstA)
                (argumentTerm.substHet termSubstB)) :
    ConvCumul ((Term.appPi functionTerm argumentTerm).substHet termSubstA)
              ((Term.appPi functionTerm argumentTerm).substHet termSubstB) :=
  ConvCumul.cast_eq_both_benton _
    (ConvCumul.appPiCong functionCompat argumentCompat)

/-- Allais arm for `pair`: two-subterm cong via `pairCong` plus
BHKM cast handling on the second component.

`Term.substHet`'s `pair` arm wraps the second component in
`Ty.subst0_substHet_commute ... ▸ ...`.  We use
`cast_eq_both_benton` to bridge the cast on the second component;
the first component is straight subst.

Construction strategy: the substituted output is
`Term.pair (firstValue.substHet ...) (cast ▸ secondValue.substHet ...)`.
Compose `pairCong` with cast_eq_both. -/
theorem ConvCumul.subst_compatible_pair_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    {firstType : Ty sourceLevel sourceScope}
    {secondType : Ty sourceLevel (sourceScope + 1)}
    {firstRaw secondRaw : RawTerm sourceScope}
    (firstValue : Term sourceCtx firstType firstRaw)
    (secondValue : Term sourceCtx (secondType.subst0 firstType firstRaw) secondRaw)
    (firstCompat :
      ConvCumul (firstValue.substHet termSubstA)
                (firstValue.substHet termSubstB))
    (secondCompat :
      ConvCumul (secondValue.substHet termSubstA)
                (secondValue.substHet termSubstB)) :
    ConvCumul ((Term.pair firstValue secondValue).substHet termSubstA)
              ((Term.pair firstValue secondValue).substHet termSubstB) :=
  ConvCumul.pairCong firstCompat
    (ConvCumul.cast_eq_both_benton _ secondCompat)

/-- Allais arm for `listCons`: two-subterm cong via `listConsCong`. -/
theorem ConvCumul.subst_compatible_listCons_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    {elementType : Ty sourceLevel sourceScope}
    {headRaw tailRaw : RawTerm sourceScope}
    (headTerm : Term sourceCtx elementType headRaw)
    (tailTerm : Term sourceCtx (Ty.listType elementType) tailRaw)
    (headCompat :
      ConvCumul (headTerm.substHet termSubstA)
                (headTerm.substHet termSubstB))
    (tailCompat :
      ConvCumul (tailTerm.substHet termSubstA)
                (tailTerm.substHet termSubstB)) :
    ConvCumul ((Term.listCons headTerm tailTerm).substHet termSubstA)
              ((Term.listCons headTerm tailTerm).substHet termSubstB) :=
  ConvCumul.listConsCong headCompat tailCompat

/-- Allais arm for `idJ`: two-subterm cong via `idJCong`. -/
theorem ConvCumul.subst_compatible_idJ_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    {carrier : Ty sourceLevel sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {motiveType : Ty sourceLevel sourceScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    (baseCase : Term sourceCtx motiveType baseRaw)
    (witness : Term sourceCtx (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw)
    (baseCompat :
      ConvCumul (baseCase.substHet termSubstA)
                (baseCase.substHet termSubstB))
    (witnessCompat :
      ConvCumul (witness.substHet termSubstA)
                (witness.substHet termSubstB)) :
    ConvCumul ((Term.idJ baseCase witness).substHet termSubstA)
              ((Term.idJ baseCase witness).substHet termSubstB) :=
  ConvCumul.idJCong baseCompat witnessCompat

/-- Allais arm for OEq refl.  The raw witness is substituted through
the shared `sigma`, so both sides are definitionally equal. -/
theorem ConvCumul.subst_compatible_oeqRefl_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma)
    (carrier : Ty sourceLevel sourceScope)
    (rawWitness : RawTerm sourceScope) :
    ConvCumul ((Term.oeqRefl (context := sourceCtx)
                  carrier rawWitness).substHet termSubstA)
              ((Term.oeqRefl (context := sourceCtx)
                  carrier rawWitness).substHet termSubstB) :=
  ConvCumul.refl _

/-- Allais arm for `oeqJ`: two-subterm cong via `oeqJCong`. -/
theorem ConvCumul.subst_compatible_oeqJ_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    {carrier : Ty sourceLevel sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {motiveType : Ty sourceLevel sourceScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    (baseCase : Term sourceCtx motiveType baseRaw)
    (witness :
      Term sourceCtx (Ty.oeq carrier leftEndpoint rightEndpoint)
        witnessRaw)
    (baseCompat :
      ConvCumul (baseCase.substHet termSubstA)
                (baseCase.substHet termSubstB))
    (witnessCompat :
      ConvCumul (witness.substHet termSubstA)
                (witness.substHet termSubstB)) :
    ConvCumul ((Term.oeqJ baseCase witness).substHet termSubstA)
              ((Term.oeqJ baseCase witness).substHet termSubstB) :=
  ConvCumul.oeqJCong baseCompat witnessCompat

/-- Allais arm for OEq funext: one-subterm cong through the pointwise
equality proof function. -/
theorem ConvCumul.subst_compatible_oeqFunext_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    (domainType codomainType : Ty sourceLevel sourceScope)
    (leftFunctionRaw rightFunctionRaw : RawTerm sourceScope)
    {pointwiseRaw : RawTerm sourceScope}
    (pointwiseProof :
      Term sourceCtx
        (oeqFunextPointwiseType domainType codomainType
          leftFunctionRaw rightFunctionRaw)
        pointwiseRaw)
    (pointwiseCompat :
      ConvCumul (pointwiseProof.substHet termSubstA)
                (pointwiseProof.substHet termSubstB)) :
    ConvCumul
      ((Term.oeqFunext domainType codomainType
        leftFunctionRaw rightFunctionRaw pointwiseProof).substHet termSubstA)
      ((Term.oeqFunext domainType codomainType
        leftFunctionRaw rightFunctionRaw pointwiseProof).substHet termSubstB) :=
  ConvCumul.oeqFunextCong
    (domainType.substHet sigma) (codomainType.substHet sigma)
    (leftFunctionRaw.subst sigma.forRaw)
    (rightFunctionRaw.subst sigma.forRaw)
    (ConvCumul.cast_eq_both_benton _ pointwiseCompat)

/-- Allais arm for strict identity refl.  The raw witness is substituted
through the shared `sigma`, so both sides are definitionally equal. -/
theorem ConvCumul.subst_compatible_idStrictRefl_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (modeIsStrict : mode = Mode.strict)
    (termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma)
    (carrier : Ty sourceLevel sourceScope)
    (rawWitness : RawTerm sourceScope) :
    ConvCumul ((Term.idStrictRefl (context := sourceCtx)
                  modeIsStrict carrier rawWitness).substHet termSubstA)
              ((Term.idStrictRefl (context := sourceCtx)
                  modeIsStrict carrier rawWitness).substHet termSubstB) :=
  ConvCumul.refl _

/-- Allais arm for strict identity recursor: two-subterm congruence. -/
theorem ConvCumul.subst_compatible_idStrictRec_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    (modeIsStrict : mode = Mode.strict)
    {carrier : Ty sourceLevel sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {motiveType : Ty sourceLevel sourceScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    (baseCase : Term sourceCtx motiveType baseRaw)
    (witness :
      Term sourceCtx (Ty.idStrict carrier leftEndpoint rightEndpoint)
        witnessRaw)
    (baseCompat :
      ConvCumul (baseCase.substHet termSubstA)
                (baseCase.substHet termSubstB))
    (witnessCompat :
      ConvCumul (witness.substHet termSubstA)
                (witness.substHet termSubstB)) :
    ConvCumul ((Term.idStrictRec modeIsStrict baseCase witness).substHet termSubstA)
              ((Term.idStrictRec modeIsStrict baseCase witness).substHet termSubstB) :=
  ConvCumul.idStrictRecCong modeIsStrict baseCompat witnessCompat

/-- Allais arm for `boolElim`: three-subterm cong via `boolElimCong`. -/
theorem ConvCumul.subst_compatible_boolElim_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    {motiveType : Ty sourceLevel (sourceScope + 1)}
    {scrutineeRaw thenRaw elseRaw : RawTerm sourceScope}
    (scrutinee : Term sourceCtx Ty.bool scrutineeRaw)
    (thenBranch :
      Term sourceCtx (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRaw)
    (elseBranch :
      Term sourceCtx (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRaw)
    (scrutineeCompat :
      ConvCumul (scrutinee.substHet termSubstA)
                (scrutinee.substHet termSubstB))
    (thenCompat :
      ConvCumul (thenBranch.substHet termSubstA)
                (thenBranch.substHet termSubstB))
    (elseCompat :
      ConvCumul (elseBranch.substHet termSubstA)
                (elseBranch.substHet termSubstB)) :
    ConvCumul ((Term.boolElim scrutinee thenBranch elseBranch).substHet termSubstA)
              ((Term.boolElim scrutinee thenBranch elseBranch).substHet termSubstB) :=
  ConvCumul.cast_eq_both_benton
    (Ty.subst0_substHet_commute motiveType Ty.bool scrutineeRaw sigma).symm
    (ConvCumul.boolElimCong scrutineeCompat
      (ConvCumul.cast_eq_both_benton
        (Ty.subst0_substHet_commute motiveType Ty.bool RawTerm.boolTrue sigma)
        thenCompat)
      (ConvCumul.cast_eq_both_benton
        (Ty.subst0_substHet_commute motiveType Ty.bool RawTerm.boolFalse sigma)
        elseCompat))

end LeanFX2
