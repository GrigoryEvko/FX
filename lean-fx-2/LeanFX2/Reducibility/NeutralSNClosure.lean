import LeanFX2.Reducibility.NeutralSNIntro

/-! # LeanFX2.Reducibility.NeutralSNClosure — K12.20.C closure + record/refine

Part 4 of K12.20.C.  Covers the type-code summary closure
(`RawTerm.isStronglyNormalizing_of_typeCode`), record / refine
destructor + intro cascade, and the universe-code Term wrapper
SN.

## What ships

* `RawTerm.isStronglyNormalizing_of_typeCode` — summary: every
  type-code Term is SN.  Dispatch over the 11 type-code kinds.
* `Term.universeCode_isStronglyNormalizing` — typed universe-code
  wrapper SN.
* `RawTerm.recordIntro_isStronglyNormalizing` /
  `Term.recordIntro_isStronglyNormalizing` — record intro SN.
* `RawTerm.recordProj_recordIntro_isStronglyNormalizing` —
  record β-firing SN.
* `RawTerm.recordProj_isStronglyNormalizing` —
  recordProj-stuck-on-non-record-intro SN preservation.
* `RawTerm.refineElim_refineIntro_isStronglyNormalizing` —
  refine β-firing SN.
* `RawTerm.refineElim_isStronglyNormalizing` —
  refineElim-stuck-on-non-refine-intro SN preservation.

## Root status

Layer 3 metatheory leaf.  Final part of the K12.20.C cascade.
Consumed by the typed-CR2 cascade. -/

namespace LeanFX2


/-- A type-code tree carrying the explicit K12.27 payload frontier is
strongly normalizing at the raw layer. -/
theorem RawTerm.isStronglyNormalizing_of_typeCode
    {scope : Nat} {codeRaw : RawTerm scope}
    (codeIsTypeCode : RawTerm.IsStronglyNormalizingTypeCode codeRaw) :
    RawTerm.isStronglyNormalizing codeRaw := by
  induction codeIsTypeCode with
  | universeCode innerLevel =>
      exact RawTerm.universeCode_isStronglyNormalizing innerLevel
  | arrowCode _ _ domainIH codomainIH =>
      exact RawTerm.arrowCode_isStronglyNormalizing domainIH codomainIH
  | piTyCode _ _ domainIH codomainIH =>
      exact RawTerm.piTyCode_isStronglyNormalizing domainIH codomainIH
  | sigmaTyCode _ _ domainIH codomainIH =>
      exact RawTerm.sigmaTyCode_isStronglyNormalizing domainIH codomainIH
  | productCode _ _ firstIH secondIH =>
      exact RawTerm.productCode_isStronglyNormalizing firstIH secondIH
  | sumCode _ _ leftIH rightIH =>
      exact RawTerm.sumCode_isStronglyNormalizing leftIH rightIH
  | listCode _ elementIH =>
      exact RawTerm.listCode_isStronglyNormalizing elementIH
  | optionCode _ elementIH =>
      exact RawTerm.optionCode_isStronglyNormalizing elementIH
  | eitherCode _ _ leftIH rightIH =>
      exact RawTerm.eitherCode_isStronglyNormalizing leftIH rightIH
  | idCode _ leftEndpointIsSN rightEndpointIsSN typeIH =>
      exact RawTerm.idCode_isStronglyNormalizing
        typeIH leftEndpointIsSN rightEndpointIsSN
  | equivCode _ _ leftIH rightIH =>
      exact RawTerm.equivCode_isStronglyNormalizing leftIH rightIH

/-- Direct M04 SN endpoint for universe code. -/
theorem Term.universeCode_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
    (levelLe : outerLevel.toNat + 1 ≤ level) :
    Term.isStronglyNormalizing
      (Term.universeCode (context := sourceCtx)
        innerLevel outerLevel cumulOk levelLe) :=
  RawTerm.universeCode_isStronglyNormalizing innerLevel.toNat

/-- Direct M04 SN endpoint for arrow type code with explicit payload SN. -/
theorem Term.arrowCode_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {domainCodeRaw codomainCodeRaw : RawTerm scope}
    (domainCodeIsSN : RawTerm.isStronglyNormalizing domainCodeRaw)
    (codomainCodeIsSN : RawTerm.isStronglyNormalizing codomainCodeRaw) :
    Term.isStronglyNormalizing
      (Term.arrowCode (context := sourceCtx)
        outerLevel levelLe domainCodeRaw codomainCodeRaw) :=
  RawTerm.arrowCode_isStronglyNormalizing
    domainCodeIsSN codomainCodeIsSN

/-- Direct M04 SN endpoint for dependent Pi type code with explicit
payload SN. -/
theorem Term.piTyCode_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {domainCodeRaw : RawTerm scope}
    {codomainCodeRaw : RawTerm (scope + 1)}
    (domainCodeIsSN : RawTerm.isStronglyNormalizing domainCodeRaw)
    (codomainCodeIsSN : RawTerm.isStronglyNormalizing codomainCodeRaw) :
    Term.isStronglyNormalizing
      (Term.piTyCode (context := sourceCtx)
        outerLevel levelLe domainCodeRaw codomainCodeRaw) :=
  RawTerm.piTyCode_isStronglyNormalizing
    domainCodeIsSN codomainCodeIsSN

/-- Direct M04 SN endpoint for dependent Sigma type code with explicit
payload SN. -/
theorem Term.sigmaTyCode_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {domainCodeRaw : RawTerm scope}
    {codomainCodeRaw : RawTerm (scope + 1)}
    (domainCodeIsSN : RawTerm.isStronglyNormalizing domainCodeRaw)
    (codomainCodeIsSN : RawTerm.isStronglyNormalizing codomainCodeRaw) :
    Term.isStronglyNormalizing
      (Term.sigmaTyCode (context := sourceCtx)
        outerLevel levelLe domainCodeRaw codomainCodeRaw) :=
  RawTerm.sigmaTyCode_isStronglyNormalizing
    domainCodeIsSN codomainCodeIsSN

/-- Direct M04 SN endpoint for product type code with explicit payload SN. -/
theorem Term.productCode_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {firstCodeRaw secondCodeRaw : RawTerm scope}
    (firstCodeIsSN : RawTerm.isStronglyNormalizing firstCodeRaw)
    (secondCodeIsSN : RawTerm.isStronglyNormalizing secondCodeRaw) :
    Term.isStronglyNormalizing
      (Term.productCode (context := sourceCtx)
        outerLevel levelLe firstCodeRaw secondCodeRaw) :=
  RawTerm.productCode_isStronglyNormalizing
    firstCodeIsSN secondCodeIsSN

/-- Direct M04 SN endpoint for sum type code with explicit payload SN. -/
theorem Term.sumCode_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {leftCodeRaw rightCodeRaw : RawTerm scope}
    (leftCodeIsSN : RawTerm.isStronglyNormalizing leftCodeRaw)
    (rightCodeIsSN : RawTerm.isStronglyNormalizing rightCodeRaw) :
    Term.isStronglyNormalizing
      (Term.sumCode (context := sourceCtx)
        outerLevel levelLe leftCodeRaw rightCodeRaw) :=
  RawTerm.sumCode_isStronglyNormalizing
    leftCodeIsSN rightCodeIsSN

/-- Direct M04 SN endpoint for either type code with explicit payload SN. -/
theorem Term.eitherCode_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {leftCodeRaw rightCodeRaw : RawTerm scope}
    (leftCodeIsSN : RawTerm.isStronglyNormalizing leftCodeRaw)
    (rightCodeIsSN : RawTerm.isStronglyNormalizing rightCodeRaw) :
    Term.isStronglyNormalizing
      (Term.eitherCode (context := sourceCtx)
        outerLevel levelLe leftCodeRaw rightCodeRaw) :=
  RawTerm.eitherCode_isStronglyNormalizing
    leftCodeIsSN rightCodeIsSN

/-- Direct M04 SN endpoint for equivalence type code with explicit
payload SN. -/
theorem Term.equivCode_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {leftTypeCodeRaw rightTypeCodeRaw : RawTerm scope}
    (leftTypeCodeIsSN :
      RawTerm.isStronglyNormalizing leftTypeCodeRaw)
    (rightTypeCodeIsSN :
      RawTerm.isStronglyNormalizing rightTypeCodeRaw) :
    Term.isStronglyNormalizing
      (Term.equivCode (context := sourceCtx)
        outerLevel levelLe leftTypeCodeRaw rightTypeCodeRaw) :=
  RawTerm.equivCode_isStronglyNormalizing
    leftTypeCodeIsSN rightTypeCodeIsSN

/-- Direct M04 SN endpoint for list type code with explicit payload SN. -/
theorem Term.listCode_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {elementCodeRaw : RawTerm scope}
    (elementCodeIsSN : RawTerm.isStronglyNormalizing elementCodeRaw) :
    Term.isStronglyNormalizing
      (Term.listCode (context := sourceCtx)
        outerLevel levelLe elementCodeRaw) :=
  RawTerm.listCode_isStronglyNormalizing elementCodeIsSN

/-- Direct M04 SN endpoint for option type code with explicit payload SN. -/
theorem Term.optionCode_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {elementCodeRaw : RawTerm scope}
    (elementCodeIsSN : RawTerm.isStronglyNormalizing elementCodeRaw) :
    Term.isStronglyNormalizing
      (Term.optionCode (context := sourceCtx)
        outerLevel levelLe elementCodeRaw) :=
  RawTerm.optionCode_isStronglyNormalizing elementCodeIsSN

/-- Direct M04 SN endpoint for identity type code with explicit payload SN. -/
theorem Term.idCode_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {typeCodeRaw leftRaw rightRaw : RawTerm scope}
    (typeCodeIsSN : RawTerm.isStronglyNormalizing typeCodeRaw)
    (leftIsSN : RawTerm.isStronglyNormalizing leftRaw)
    (rightIsSN : RawTerm.isStronglyNormalizing rightRaw) :
    Term.isStronglyNormalizing
      (Term.idCode (context := sourceCtx)
        outerLevel levelLe typeCodeRaw leftRaw rightRaw) :=
  RawTerm.idCode_isStronglyNormalizing
    typeCodeIsSN leftIsSN rightIsSN

/-- Identity-substitution form of
`RawTerm.isStronglyNormalizing_of_typeCode`, matching the direct M04
route through `TermSubst.identity`. -/
theorem RawTerm.subst_identity_isStronglyNormalizing_of_typeCode
    {level scope : Nat} {codeRaw : RawTerm scope}
    (codeIsTypeCode : RawTerm.IsStronglyNormalizingTypeCode codeRaw) :
    RawTerm.isStronglyNormalizing
      (codeRaw.subst (@Subst.identity level scope).forRaw) := by
  rw [RawTerm.subst_identity codeRaw]
  exact RawTerm.isStronglyNormalizing_of_typeCode codeIsTypeCode

/-- **K12.27 schematic raw-payload evidence for M04**.

Most `Term` constructors expose every raw component through recursive
typed children, so the eventual fundamental induction can obtain raw SN
from those children.  A small frontier of value-shaped constructors keeps
schematic `RawTerm` fields directly in the raw projection.  This predicate
names exactly those residual M04 obligations.

Fields that occur only in the static type are intentionally omitted: M04 is
strong normalization of the projected raw term, not reduction inside type
annotations. -/
def Term.HasStronglyNormalizingRawPayloads
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {sourceType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (sourceTerm : Term context sourceType sourceRaw) : Prop :=
  match sourceTerm with
  | Term.var _ => True
  | Term.unit => True
  | Term.lam body =>
      Term.HasStronglyNormalizingRawPayloads body
  | Term.app functionTerm argumentTerm =>
      Term.HasStronglyNormalizingRawPayloads functionTerm ∧
      Term.HasStronglyNormalizingRawPayloads argumentTerm
  | Term.lamPi body =>
      Term.HasStronglyNormalizingRawPayloads body
  | Term.appPi functionTerm argumentTerm =>
      Term.HasStronglyNormalizingRawPayloads functionTerm ∧
      Term.HasStronglyNormalizingRawPayloads argumentTerm
  | Term.pair firstValue secondValue =>
      Term.HasStronglyNormalizingRawPayloads firstValue ∧
      Term.HasStronglyNormalizingRawPayloads secondValue
  | Term.fst pairTerm =>
      Term.HasStronglyNormalizingRawPayloads pairTerm
  | Term.snd pairTerm =>
      Term.HasStronglyNormalizingRawPayloads pairTerm
  | Term.boolTrue => True
  | Term.boolFalse => True
  | Term.boolElim scrutinee thenBranch elseBranch =>
      Term.HasStronglyNormalizingRawPayloads scrutinee ∧
      Term.HasStronglyNormalizingRawPayloads thenBranch ∧
      Term.HasStronglyNormalizingRawPayloads elseBranch
  | Term.natZero => True
  | Term.natSucc predecessor =>
      Term.HasStronglyNormalizingRawPayloads predecessor
  | Term.natElim scrutinee zeroBranch succBranch =>
      Term.HasStronglyNormalizingRawPayloads scrutinee ∧
      Term.HasStronglyNormalizingRawPayloads zeroBranch ∧
      Term.HasStronglyNormalizingRawPayloads succBranch
  | Term.natRec scrutinee zeroBranch succBranch =>
      Term.HasStronglyNormalizingRawPayloads scrutinee ∧
      Term.HasStronglyNormalizingRawPayloads zeroBranch ∧
      Term.HasStronglyNormalizingRawPayloads succBranch
  | Term.listNil => True
  | Term.listCons headTerm tailTerm =>
      Term.HasStronglyNormalizingRawPayloads headTerm ∧
      Term.HasStronglyNormalizingRawPayloads tailTerm
  | Term.listElim scrutinee nilBranch consBranch =>
      Term.HasStronglyNormalizingRawPayloads scrutinee ∧
      Term.HasStronglyNormalizingRawPayloads nilBranch ∧
      Term.HasStronglyNormalizingRawPayloads consBranch
  | Term.optionNone => True
  | Term.optionSome valueTerm =>
      Term.HasStronglyNormalizingRawPayloads valueTerm
  | Term.optionMatch scrutinee noneBranch someBranch =>
      Term.HasStronglyNormalizingRawPayloads scrutinee ∧
      Term.HasStronglyNormalizingRawPayloads noneBranch ∧
      Term.HasStronglyNormalizingRawPayloads someBranch
  | Term.eitherInl valueTerm =>
      Term.HasStronglyNormalizingRawPayloads valueTerm
  | Term.eitherInr valueTerm =>
      Term.HasStronglyNormalizingRawPayloads valueTerm
  | Term.eitherMatch scrutinee leftBranch rightBranch =>
      Term.HasStronglyNormalizingRawPayloads scrutinee ∧
      Term.HasStronglyNormalizingRawPayloads leftBranch ∧
      Term.HasStronglyNormalizingRawPayloads rightBranch
  | Term.refl _ rawWitness =>
      RawTerm.isStronglyNormalizing rawWitness
  | Term.idJ baseCase witness =>
      Term.HasStronglyNormalizingRawPayloads baseCase ∧
      Term.HasStronglyNormalizingRawPayloads witness
  | Term.oeqRefl _ rawWitness =>
      RawTerm.isStronglyNormalizing rawWitness
  | Term.oeqJ baseCase witness =>
      Term.HasStronglyNormalizingRawPayloads baseCase ∧
      Term.HasStronglyNormalizingRawPayloads witness
  | Term.oeqFunext _ _ _ _ pointwiseProof =>
      Term.HasStronglyNormalizingRawPayloads pointwiseProof
  | Term.idStrictRefl _ _ rawWitness =>
      RawTerm.isStronglyNormalizing rawWitness
  | Term.idStrictRec _ baseCase witness =>
      Term.HasStronglyNormalizingRawPayloads baseCase ∧
      Term.HasStronglyNormalizingRawPayloads witness
  | Term.modIntro innerTerm =>
      Term.HasStronglyNormalizingRawPayloads innerTerm
  | Term.modElim innerTerm =>
      Term.HasStronglyNormalizingRawPayloads innerTerm
  | Term.subsume innerTerm =>
      Term.HasStronglyNormalizingRawPayloads innerTerm
  | Term.interval0 => True
  | Term.interval1 => True
  | Term.intervalOpp innerValue =>
      Term.HasStronglyNormalizingRawPayloads innerValue
  | Term.intervalMeet leftValue rightValue =>
      Term.HasStronglyNormalizingRawPayloads leftValue ∧
      Term.HasStronglyNormalizingRawPayloads rightValue
  | Term.intervalJoin leftValue rightValue =>
      Term.HasStronglyNormalizingRawPayloads leftValue ∧
      Term.HasStronglyNormalizingRawPayloads rightValue
  | Term.pathLam _ _ _ _ body =>
      Term.HasStronglyNormalizingRawPayloads body
  | Term.pathApp _ pathTerm intervalTerm =>
      Term.HasStronglyNormalizingRawPayloads pathTerm ∧
      Term.HasStronglyNormalizingRawPayloads intervalTerm
  | Term.glueIntro _ _ _ baseValue partialValue =>
      Term.HasStronglyNormalizingRawPayloads baseValue ∧
      Term.HasStronglyNormalizingRawPayloads partialValue
  | Term.glueElim _ gluedValue =>
      Term.HasStronglyNormalizingRawPayloads gluedValue
  | Term.transp _ _ _ _ _ _ _ typePath sourceValue =>
      Term.HasStronglyNormalizingRawPayloads typePath ∧
      Term.HasStronglyNormalizingRawPayloads sourceValue
  | Term.hcomp _ sidesValue capValue =>
      Term.HasStronglyNormalizingRawPayloads sidesValue ∧
      Term.HasStronglyNormalizingRawPayloads capValue
  | Term.recordIntro firstField =>
      Term.HasStronglyNormalizingRawPayloads firstField
  | Term.recordProj recordValue =>
      Term.HasStronglyNormalizingRawPayloads recordValue
  | Term.refineIntro _ baseValue predicateProof =>
      Term.HasStronglyNormalizingRawPayloads baseValue ∧
      Term.HasStronglyNormalizingRawPayloads predicateProof
  | Term.refineElim refinedValue =>
      Term.HasStronglyNormalizingRawPayloads refinedValue
  | Term.codataUnfold initialState transition =>
      Term.HasStronglyNormalizingRawPayloads initialState ∧
      Term.HasStronglyNormalizingRawPayloads transition
  | Term.codataDest codataValue =>
      Term.HasStronglyNormalizingRawPayloads codataValue
  | Term.sessionSend _ channel payload =>
      Term.HasStronglyNormalizingRawPayloads channel ∧
      Term.HasStronglyNormalizingRawPayloads payload
  | Term.sessionRecv channel =>
      Term.HasStronglyNormalizingRawPayloads channel
  | Term.effectPerform _ _ _ _ operationTag arguments =>
      Term.HasStronglyNormalizingRawPayloads operationTag ∧
      Term.HasStronglyNormalizingRawPayloads arguments
  | Term.universeCode _ _ _ _ => True
  | Term.cumulUp _ _ _ _ _ typeCode =>
      Term.HasStronglyNormalizingRawPayloads typeCode
  | Term.equivReflId _ => True
  | Term.funextRefl _ _ applyRaw =>
      RawTerm.isStronglyNormalizing applyRaw
  | Term.equivReflIdAtId _ _ _ _ => True
  | Term.funextReflAtId _ _ applyRaw =>
      RawTerm.isStronglyNormalizing applyRaw
  | Term.equivIntroHet forward backward leftInv rightInv =>
      Term.HasStronglyNormalizingRawPayloads forward ∧
      Term.HasStronglyNormalizingRawPayloads backward ∧
      Term.HasStronglyNormalizingRawPayloads leftInv ∧
      Term.HasStronglyNormalizingRawPayloads rightInv
  | Term.equivApp equivTerm argumentTerm =>
      Term.HasStronglyNormalizingRawPayloads equivTerm ∧
      Term.HasStronglyNormalizingRawPayloads argumentTerm
  | Term.uaIntroHet _ _ _ _ equivWitness =>
      Term.HasStronglyNormalizingRawPayloads equivWitness
  | Term.funextIntroHet _ _ applyARaw _ =>
      RawTerm.isStronglyNormalizing applyARaw
  | Term.arrowCode _ _ domainCodeRaw codomainCodeRaw =>
      RawTerm.IsStronglyNormalizingTypeCode domainCodeRaw ∧
      RawTerm.IsStronglyNormalizingTypeCode codomainCodeRaw
  | Term.piTyCode _ _ domainCodeRaw codomainCodeRaw =>
      RawTerm.IsStronglyNormalizingTypeCode domainCodeRaw ∧
      RawTerm.IsStronglyNormalizingTypeCode codomainCodeRaw
  | Term.sigmaTyCode _ _ domainCodeRaw codomainCodeRaw =>
      RawTerm.IsStronglyNormalizingTypeCode domainCodeRaw ∧
      RawTerm.IsStronglyNormalizingTypeCode codomainCodeRaw
  | Term.productCode _ _ firstCodeRaw secondCodeRaw =>
      RawTerm.IsStronglyNormalizingTypeCode firstCodeRaw ∧
      RawTerm.IsStronglyNormalizingTypeCode secondCodeRaw
  | Term.sumCode _ _ leftCodeRaw rightCodeRaw =>
      RawTerm.IsStronglyNormalizingTypeCode leftCodeRaw ∧
      RawTerm.IsStronglyNormalizingTypeCode rightCodeRaw
  | Term.listCode _ _ elementCodeRaw =>
      RawTerm.IsStronglyNormalizingTypeCode elementCodeRaw
  | Term.optionCode _ _ elementCodeRaw =>
      RawTerm.IsStronglyNormalizingTypeCode elementCodeRaw
  | Term.eitherCode _ _ leftCodeRaw rightCodeRaw =>
      RawTerm.IsStronglyNormalizingTypeCode leftCodeRaw ∧
      RawTerm.IsStronglyNormalizingTypeCode rightCodeRaw
  | Term.idCode _ _ typeCodeRaw leftRaw rightRaw =>
      RawTerm.IsStronglyNormalizingTypeCode typeCodeRaw ∧
      RawTerm.isStronglyNormalizing leftRaw ∧
      RawTerm.isStronglyNormalizing rightRaw
  | Term.equivCode _ _ leftTypeCodeRaw rightTypeCodeRaw =>
      RawTerm.IsStronglyNormalizingTypeCode leftTypeCodeRaw ∧
      RawTerm.IsStronglyNormalizingTypeCode rightTypeCodeRaw
  | Term.uaToEquiv _ _ _ _ _ _ proof =>
      Term.HasStronglyNormalizingRawPayloads proof
  | Term.equivApply equivTerm argumentTerm =>
      Term.HasStronglyNormalizingRawPayloads equivTerm ∧
      Term.HasStronglyNormalizingRawPayloads argumentTerm

/-- **K12.20.AN.1 interval0 fundamental case** — cubical interval
zero endpoint.  `Ty.interval` is closed (no scope dependence) so
`Ty.interval.subst sigma = Ty.interval`; `Term.subst` on the
nullary intro reduces to itself
(`LeanFX2/Term/Subst.lean:306`); `Reducible Ty.interval _`
unfolds to `Term.isStronglyNormalizing _`
(`LeanFX2/Reducibility.lean:329`).  Closes the nullary-intro
quartet alongside K12.19.B unit / boolTrue / boolFalse / natZero
with the same one-liner template. -/
theorem Reducible.fundamental_interval0
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma} :
    Reducible ((Ty.interval : Ty level scope).subst sigma)
              (Term.subst termSubst
                (Term.interval0 (context := sourceCtx))) :=
  RawTerm.interval0_isStronglyNormalizing

/-- Interval zero is stable under future-world renamings. -/
theorem Reducible.fundamental_interval0_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma} :
    IsRenamingStableReducible ((Ty.interval : Ty level scope).subst sigma)
      (Term.subst termSubst
        (Term.interval0 (context := sourceCtx))) := by
  intro _renamedScope _renamedCtx _rho _rhoIsInjective _termRenaming
  exact RawTerm.interval0_isStronglyNormalizing

/-- **K12.20.AN.2 interval1 fundamental case** — cubical interval
one endpoint.  Same closed-leaf intro shape as `interval0`. -/
theorem Reducible.fundamental_interval1
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma} :
    Reducible ((Ty.interval : Ty level scope).subst sigma)
              (Term.subst termSubst
                (Term.interval1 (context := sourceCtx))) :=
  RawTerm.interval1_isStronglyNormalizing

/-- Interval one is stable under future-world renamings. -/
theorem Reducible.fundamental_interval1_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma} :
    IsRenamingStableReducible ((Ty.interval : Ty level scope).subst sigma)
      (Term.subst termSubst
        (Term.interval1 (context := sourceCtx))) := by
  intro _renamedScope _renamedCtx _rho _rhoIsInjective _termRenaming
  exact RawTerm.interval1_isStronglyNormalizing

/-- **K12.20.AF.1 intervalOpp SN preservation** — cubical interval
negation.  Unary cong over the interval term; intervalOpp_inv
discharges each par step. -/
theorem RawTerm.intervalOpp_isStronglyNormalizing {scope : Nat}
    {intervalTerm : RawTerm scope}
    (intervalIsSN : RawTerm.isStronglyNormalizing intervalTerm) :
    RawTerm.isStronglyNormalizing (RawTerm.intervalOpp intervalTerm) := by
  induction intervalIsSN with
  | intro currentInterval _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.intervalOpp currentInterval) ?_
    intro target progressStep
    obtain ⟨intervalTarget, targetEq, intervalStep⟩ :=
      RawStep.par.intervalOpp_inv progressStep.1
    subst targetEq
    have intervalDistinct :
        currentInterval ≠ intervalTarget := fun intervalEq =>
      progressStep.2 (congrArg RawTerm.intervalOpp intervalEq)
    exact inductiveHypothesis intervalTarget
      ⟨intervalStep, intervalDistinct⟩

/-- **K12.20.AF.2 intervalMeet SN preservation** — cubical interval
meet (∧).  Binary cong; uses the universal-in-conclusion trick
to keep the second-argument IH universal during induction on the
first SN witness. -/
theorem RawTerm.intervalMeet_isStronglyNormalizing {scope : Nat}
    {leftInterval : RawTerm scope}
    (leftIsSN : RawTerm.isStronglyNormalizing leftInterval) :
    ∀ {rightInterval : RawTerm scope},
      RawTerm.isStronglyNormalizing rightInterval →
      RawTerm.isStronglyNormalizing
        (RawTerm.intervalMeet leftInterval rightInterval) := by
  induction leftIsSN with
  | intro currentLeft _ leftIH =>
    intro rightInterval rightIsSN
    induction rightIsSN with
    | intro currentRight rightClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.intervalMeet currentLeft currentRight) ?_
      intro target progressStep
      obtain ⟨leftTarget, rightTarget, targetEq, leftStep, rightStep⟩ :=
        RawStep.par.intervalMeet_inv progressStep.1
      subst targetEq
      by_cases leftEq : currentLeft = leftTarget
      · subst leftEq
        have rightDistinct : currentRight ≠ rightTarget := fun rightEq =>
          progressStep.2 (congrArg (RawTerm.intervalMeet currentLeft) rightEq)
        exact innerIH rightTarget ⟨rightStep, rightDistinct⟩
      · have leftProgress : RawStep.parProgress currentLeft leftTarget :=
          ⟨leftStep, leftEq⟩
        by_cases rightEq : currentRight = rightTarget
        · subst rightEq
          exact leftIH leftTarget leftProgress
            (RawTerm.isStronglyNormalizing.intro currentRight rightClosure)
        · exact leftIH leftTarget leftProgress
            (rightClosure rightTarget ⟨rightStep, rightEq⟩)

/-- **K12.20.AF.3 intervalJoin SN preservation** — cubical interval
join (∨).  Sister to intervalMeet; same binary cong shape. -/
theorem RawTerm.intervalJoin_isStronglyNormalizing {scope : Nat}
    {leftInterval : RawTerm scope}
    (leftIsSN : RawTerm.isStronglyNormalizing leftInterval) :
    ∀ {rightInterval : RawTerm scope},
      RawTerm.isStronglyNormalizing rightInterval →
      RawTerm.isStronglyNormalizing
        (RawTerm.intervalJoin leftInterval rightInterval) := by
  induction leftIsSN with
  | intro currentLeft _ leftIH =>
    intro rightInterval rightIsSN
    induction rightIsSN with
    | intro currentRight rightClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.intervalJoin currentLeft currentRight) ?_
      intro target progressStep
      obtain ⟨leftTarget, rightTarget, targetEq, leftStep, rightStep⟩ :=
        RawStep.par.intervalJoin_inv progressStep.1
      subst targetEq
      by_cases leftEq : currentLeft = leftTarget
      · subst leftEq
        have rightDistinct : currentRight ≠ rightTarget := fun rightEq =>
          progressStep.2 (congrArg (RawTerm.intervalJoin currentLeft) rightEq)
        exact innerIH rightTarget ⟨rightStep, rightDistinct⟩
      · have leftProgress : RawStep.parProgress currentLeft leftTarget :=
          ⟨leftStep, leftEq⟩
        by_cases rightEq : currentRight = rightTarget
        · subst rightEq
          exact leftIH leftTarget leftProgress
            (RawTerm.isStronglyNormalizing.intro currentRight rightClosure)
        · exact leftIH leftTarget leftProgress
            (rightClosure rightTarget ⟨rightStep, rightEq⟩)

/-- **K12.20.AG pathLam SN preservation** — cubical path lambda
binder.  Sister to lam helper — body lives in `RawTerm (scope+1)`,
induction on body's SN witness discharges each par step via
pathLam_inv + congrArg-based parProgress disequality. -/
theorem RawTerm.pathLam_isStronglyNormalizing {scope : Nat}
    {body : RawTerm (scope + 1)}
    (bodyIsSN : RawTerm.isStronglyNormalizing body) :
    RawTerm.isStronglyNormalizing (RawTerm.pathLam body) := by
  induction bodyIsSN with
  | intro currentBody _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.pathLam currentBody) ?_
    intro target progressStep
    obtain ⟨bodyTarget, targetEq, bodyStep⟩ :=
      RawStep.par.pathLam_inv progressStep.1
    subst targetEq
    have bodyDistinct : currentBody ≠ bodyTarget := fun bodyEq =>
      progressStep.2 (congrArg RawTerm.pathLam bodyEq)
    exact inductiveHypothesis bodyTarget ⟨bodyStep, bodyDistinct⟩

/-- Typed wrapper for cubical path-lambda SN preservation.

This packages the raw binder SN fact for `Term.pathLam`.  It is only
the SN half of the cubical path-introduction case; the full Reducible
closure still needs the interval-application endpoint. -/
theorem Term.pathLam_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (carrierType : Ty level scope)
    (leftEndpoint rightEndpoint : RawTerm scope)
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
      Term (context.cons Ty.interval) carrierType.weaken bodyRaw}
    (bodyIsSN : Term.isStronglyNormalizing bodyTerm) :
    Term.isStronglyNormalizing
      (Term.pathLam modeIsUnivalent carrierType leftEndpoint rightEndpoint
        bodyTerm) :=
  RawTerm.pathLam_isStronglyNormalizing bodyIsSN

/-- **K12.20.AI.1 uaToEquiv SN preservation** — univalence-to-
equivalence converter (D3.6 ua_β infrastructure).  Pure unary
cong over its proof witness; uaToEquiv_inv discharges. -/
theorem RawTerm.uaToEquiv_isStronglyNormalizing {scope : Nat}
    {proof : RawTerm scope}
    (proofIsSN : RawTerm.isStronglyNormalizing proof) :
    RawTerm.isStronglyNormalizing (RawTerm.uaToEquiv proof) := by
  induction proofIsSN with
  | intro currentProof _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.uaToEquiv currentProof) ?_
    intro target progressStep
    obtain ⟨proofTarget, targetEq, proofStep⟩ :=
      RawStep.par.uaToEquiv_inv progressStep.1
    subst targetEq
    have proofDistinct :
        currentProof ≠ proofTarget := fun proofEq =>
      progressStep.2 (congrArg RawTerm.uaToEquiv proofEq)
    exact inductiveHypothesis proofTarget
      ⟨proofStep, proofDistinct⟩

/-- **K12.20.AI.2 oeqFunext SN preservation** — observational
equality functional extensionality intro.  Pure unary cong over
the pointwise-equality witness. -/
theorem RawTerm.oeqFunext_isStronglyNormalizing {scope : Nat}
    {pointwiseEquality : RawTerm scope}
    (pointwiseIsSN : RawTerm.isStronglyNormalizing pointwiseEquality) :
    RawTerm.isStronglyNormalizing
      (RawTerm.oeqFunext pointwiseEquality) := by
  induction pointwiseIsSN with
  | intro currentPointwise _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.oeqFunext currentPointwise) ?_
    intro target progressStep
    obtain ⟨pointwiseTarget, targetEq, pointwiseStep⟩ :=
      RawStep.par.oeqFunext_inv progressStep.1
    subst targetEq
    have pointwiseDistinct :
        currentPointwise ≠ pointwiseTarget := fun pointwiseEq =>
      progressStep.2 (congrArg RawTerm.oeqFunext pointwiseEq)
    exact inductiveHypothesis pointwiseTarget
      ⟨pointwiseStep, pointwiseDistinct⟩

/-- **K12.20.AJ.1 recordIntro SN preservation** — record value
introduction (currently single-field representative; multi-field
records desugar to nested pairs).  Pure unary cong over the
first-field witness. -/
theorem RawTerm.recordIntro_isStronglyNormalizing {scope : Nat}
    {firstField : RawTerm scope}
    (firstFieldIsSN : RawTerm.isStronglyNormalizing firstField) :
    RawTerm.isStronglyNormalizing (RawTerm.recordIntro firstField) := by
  induction firstFieldIsSN with
  | intro currentField _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.recordIntro currentField) ?_
    intro target progressStep
    obtain ⟨firstTarget, targetEq, firstStep⟩ :=
      RawStep.par.recordIntro_inv progressStep.1
    subst targetEq
    have firstDistinct :
        currentField ≠ firstTarget := fun firstEq =>
      progressStep.2 (congrArg RawTerm.recordIntro firstEq)
    exact inductiveHypothesis firstTarget
      ⟨firstStep, firstDistinct⟩

/-- Typed wrapper for single-field record introduction SN preservation. -/
theorem Term.recordIntro_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {singleFieldType : Ty level scope}
    {firstRaw : RawTerm scope}
    {firstField : Term context singleFieldType firstRaw}
    (firstFieldIsSN : Term.isStronglyNormalizing firstField) :
    Term.isStronglyNormalizing (Term.recordIntro firstField) :=
  RawTerm.recordIntro_isStronglyNormalizing firstFieldIsSN

/-- Head-β SN expansion for single-field record projection.

If the field is strongly normalizing, then
`recordProj (recordIntro field)` is strongly normalizing.  Congruence
reducts recurse through the record field; β reducts land on a reduct
of the field. -/
theorem RawTerm.recordProj_recordIntro_isStronglyNormalizing
    {scope : Nat}
    {firstField : RawTerm scope}
    (firstFieldIsSN : RawTerm.isStronglyNormalizing firstField) :
    RawTerm.isStronglyNormalizing
      (RawTerm.recordProj (RawTerm.recordIntro firstField)) := by
  induction firstFieldIsSN with
  | intro currentField fieldClosure fieldIH =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.recordProj (RawTerm.recordIntro currentField)) ?_
    intro target progressStep
    rcases RawStep.par.recordProj_inv progressStep.1 with
      ⟨_recordTarget, targetEq, recordStep⟩
      | ⟨firstTarget, targetEq, recordStep⟩
    · obtain ⟨firstTarget, recordTargetEq, firstStep⟩ :=
        RawStep.par.recordIntro_inv recordStep
      subst recordTargetEq
      subst targetEq
      by_cases firstEq : currentField = firstTarget
      · subst firstEq
        exact False.elim (progressStep.2 rfl)
      · exact fieldIH firstTarget ⟨firstStep, firstEq⟩
    · obtain ⟨recordFirstTarget, recordTargetEq, firstStep⟩ :=
        RawStep.par.recordIntro_inv recordStep
      injection recordTargetEq with _scopeEq firstTargetEq
      rw [targetEq]
      have firstStepToTarget : RawStep.par currentField firstTarget := by
        rw [firstTargetEq]
        exact firstStep
      by_cases firstEq : currentField = firstTarget
      · subst firstEq
        exact RawTerm.isStronglyNormalizing.intro
          currentField fieldClosure
      · exact fieldClosure firstTarget ⟨firstStepToTarget, firstEq⟩

/-- Typed wrapper for `recordProj (recordIntro field)` SN expansion.

This is an SN bridge only.  The full record-intro reducibility theorem
still requires typed backward closure at the projected field type. -/
theorem Term.recordProj_recordIntro_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {singleFieldType : Ty level scope}
    {firstRaw : RawTerm scope}
    {firstField : Term context singleFieldType firstRaw}
    (firstFieldIsSN : Term.isStronglyNormalizing firstField) :
    Term.isStronglyNormalizing
      (Term.recordProj (Term.recordIntro firstField)) :=
  RawTerm.recordProj_recordIntro_isStronglyNormalizing firstFieldIsSN

/-- Generic record-projection SN preservation.

Congruent reducts recurse through the record term.  A β reduct first
develops the record into a `recordIntro`; the projected field is SN by
the record-intro field inversion lemma. -/
theorem RawTerm.recordProj_isStronglyNormalizing {scope : Nat}
    {recordRaw : RawTerm scope}
    (recordIsSN : RawTerm.isStronglyNormalizing recordRaw) :
    RawTerm.isStronglyNormalizing (RawTerm.recordProj recordRaw) := by
  induction recordIsSN with
  | intro currentRecord recordClosure recordIH =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.recordProj currentRecord) ?_
    intro target progressStep
    rcases RawStep.par.recordProj_inv progressStep.1 with
      ⟨recordTarget, targetEq, recordStep⟩
      | ⟨firstTarget, targetEq, recordStep⟩
    · subst targetEq
      by_cases recordEq : currentRecord = recordTarget
      · subst recordEq
        exact (progressStep.2 rfl).elim
      · exact recordIH recordTarget ⟨recordStep, recordEq⟩
    · rw [targetEq]
      have developedRecordIsSN :
          RawTerm.isStronglyNormalizing
            (RawTerm.recordIntro firstTarget) := by
        by_cases recordEq : currentRecord = RawTerm.recordIntro firstTarget
        · rw [← recordEq]
          exact RawTerm.isStronglyNormalizing.intro
            currentRecord recordClosure
        · exact recordClosure (RawTerm.recordIntro firstTarget)
            ⟨recordStep, recordEq⟩
      exact RawTerm.recordIntro_field_isStronglyNormalizing
        developedRecordIsSN

/-- Direct M04 SN case for projection from any SN record term. -/
theorem Term.recordProj_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {singleFieldType : Ty level scope}
    {recordRaw : RawTerm scope}
    {recordValue : Term context (Ty.record singleFieldType) recordRaw}
    (recordIsSN : Term.isStronglyNormalizing recordValue) :
    Term.isStronglyNormalizing (Term.recordProj recordValue) :=
  RawTerm.recordProj_isStronglyNormalizing recordIsSN

/-- Head-β SN expansion for refinement elimination.

If the refined value payload and its erased proof payload are strongly
normalizing, then `refineElim (refineIntro value proof)` is strongly
normalizing.  Congruence reducts recurse through both payloads; β reducts
land on a reduct of the value payload. -/
theorem RawTerm.refineElim_refineIntro_isStronglyNormalizing
    {scope : Nat}
    {rawValue : RawTerm scope}
    (valueIsSN : RawTerm.isStronglyNormalizing rawValue) :
    ∀ {predicateProof : RawTerm scope},
      RawTerm.isStronglyNormalizing predicateProof →
      RawTerm.isStronglyNormalizing
        (RawTerm.refineElim
          (RawTerm.refineIntro rawValue predicateProof)) := by
  induction valueIsSN with
  | intro currentValue valueClosure valueIH =>
    intro predicateProof proofIsSN
    induction proofIsSN with
    | intro currentProof proofClosure proofIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.refineElim
          (RawTerm.refineIntro currentValue currentProof)) ?_
      intro target progressStep
      rcases RawStep.par.refineElim_inv progressStep.1 with
        ⟨refinedTarget, targetEq, refinedStep⟩
        | ⟨valueTarget, proofTarget, targetEq, refinedStep⟩
      · obtain ⟨valueTarget, proofTarget, refinedTargetEq,
            valueStep, proofStep⟩ :=
          RawStep.par.refineIntro_inv refinedStep
        subst refinedTargetEq
        subst targetEq
        by_cases valueEq : currentValue = valueTarget
        · subst valueEq
          by_cases proofEq : currentProof = proofTarget
          · subst proofEq
            exact False.elim (progressStep.2 rfl)
          · exact proofIH proofTarget ⟨proofStep, proofEq⟩
        · have valueProgress :
              RawStep.parProgress currentValue valueTarget :=
            ⟨valueStep, valueEq⟩
          by_cases proofEq : currentProof = proofTarget
          · subst proofEq
            exact valueIH valueTarget valueProgress
              (RawTerm.isStronglyNormalizing.intro currentProof
                proofClosure)
          · exact valueIH valueTarget valueProgress
              (proofClosure proofTarget ⟨proofStep, proofEq⟩)
      · obtain ⟨refinedValueTarget, _refinedProofTarget,
            refinedTargetEq, valueStep, _proofStep⟩ :=
          RawStep.par.refineIntro_inv refinedStep
        injection refinedTargetEq with _scopeEq valueTargetEq
          _proofTargetEq
        rw [targetEq]
        have valueStepToTarget :
            RawStep.par currentValue valueTarget := by
          rw [valueTargetEq]
          exact valueStep
        by_cases valueEq : currentValue = valueTarget
        · subst valueEq
          exact RawTerm.isStronglyNormalizing.intro
            currentValue valueClosure
        · exact valueClosure valueTarget
            ⟨valueStepToTarget, valueEq⟩

/-- Typed wrapper for `refineElim (refineIntro value proof)` SN expansion.

This is an SN bridge only.  It does not claim the full `Reducible`
backward closure for refinement introduction. -/
theorem Term.refineElim_refineIntro_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    {predicate : RawTerm (scope + 1)}
    {valueRaw proofRaw : RawTerm scope}
    {baseValue : Term context baseType valueRaw}
    {predicateProof : Term context Ty.unit proofRaw}
    (valueIsSN : Term.isStronglyNormalizing baseValue)
    (proofIsSN : Term.isStronglyNormalizing predicateProof) :
    Term.isStronglyNormalizing
      (Term.refineElim
        (Term.refineIntro predicate baseValue predicateProof)) :=
  RawTerm.refineElim_refineIntro_isStronglyNormalizing
    valueIsSN proofIsSN

/-- Generic refinement-elimination SN preservation.

Congruent reducts recurse through the refined term.  A β reduct first
develops the refined term into a `refineIntro`; the extracted value is
SN by the refinement-intro value inversion lemma. -/
theorem RawTerm.refineElim_isStronglyNormalizing {scope : Nat}
    {refinedRaw : RawTerm scope}
    (refinedIsSN : RawTerm.isStronglyNormalizing refinedRaw) :
    RawTerm.isStronglyNormalizing (RawTerm.refineElim refinedRaw) := by
  induction refinedIsSN with
  | intro currentRefined refinedClosure refinedIH =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.refineElim currentRefined) ?_
    intro target progressStep
    rcases RawStep.par.refineElim_inv progressStep.1 with
      ⟨refinedTarget, targetEq, refinedStep⟩
      | ⟨valueTarget, proofTarget, targetEq, refinedStep⟩
    · subst targetEq
      by_cases refinedEq : currentRefined = refinedTarget
      · subst refinedEq
        exact (progressStep.2 rfl).elim
      · exact refinedIH refinedTarget ⟨refinedStep, refinedEq⟩
    · rw [targetEq]
      have developedRefinedIsSN :
          RawTerm.isStronglyNormalizing
            (RawTerm.refineIntro valueTarget proofTarget) := by
        by_cases refinedEq :
            currentRefined =
              RawTerm.refineIntro valueTarget proofTarget
        · rw [← refinedEq]
          exact RawTerm.isStronglyNormalizing.intro
            currentRefined refinedClosure
        · exact refinedClosure
            (RawTerm.refineIntro valueTarget proofTarget)
            ⟨refinedStep, refinedEq⟩
      exact RawTerm.refineIntro_value_isStronglyNormalizing
        developedRefinedIsSN

/-- Direct M04 SN case for refinement elimination from any SN refined
term. -/
theorem Term.refineElim_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    {predicate : RawTerm (scope + 1)}
    {refinedRaw : RawTerm scope}
    {refinedValue : Term context (Ty.refine baseType predicate) refinedRaw}
    (refinedIsSN : Term.isStronglyNormalizing refinedValue) :
    Term.isStronglyNormalizing (Term.refineElim refinedValue) :=
  RawTerm.refineElim_isStronglyNormalizing refinedIsSN

/-- **K12.20.AJ.2 refineIntro SN preservation** — refinement-type
intro packs a value with a proof of its refinement predicate.
Binary cong; uses the pair-style universal-in-conclusion pattern. -/
theorem RawTerm.refineIntro_isStronglyNormalizing {scope : Nat}
    {rawValue : RawTerm scope}
    (valueIsSN : RawTerm.isStronglyNormalizing rawValue) :
    ∀ {predicateProof : RawTerm scope},
      RawTerm.isStronglyNormalizing predicateProof →
      RawTerm.isStronglyNormalizing
        (RawTerm.refineIntro rawValue predicateProof) := by
  induction valueIsSN with
  | intro currentValue _ valueIH =>
    intro predicateProof proofIsSN
    induction proofIsSN with
    | intro currentProof proofClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.refineIntro currentValue currentProof) ?_
      intro target progressStep
      obtain ⟨valueTarget, proofTarget, targetEq,
              valueStep, proofStep⟩ :=
        RawStep.par.refineIntro_inv progressStep.1
      subst targetEq
      by_cases valueEq : currentValue = valueTarget
      · subst valueEq
        have proofDistinct :
            currentProof ≠ proofTarget := fun proofEq =>
          progressStep.2
            (congrArg (RawTerm.refineIntro currentValue) proofEq)
        exact innerIH proofTarget ⟨proofStep, proofDistinct⟩
      · have valueProgress :
            RawStep.parProgress currentValue valueTarget :=
          ⟨valueStep, valueEq⟩
        by_cases proofEq : currentProof = proofTarget
        · subst proofEq
          exact valueIH valueTarget valueProgress
            (RawTerm.isStronglyNormalizing.intro currentProof
              proofClosure)
        · exact valueIH valueTarget valueProgress
            (proofClosure proofTarget ⟨proofStep, proofEq⟩)

/-- Typed wrapper for refinement introduction SN preservation. -/
theorem Term.refineIntro_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    {predicate : RawTerm (scope + 1)}
    {valueRaw proofRaw : RawTerm scope}
    {baseValue : Term context baseType valueRaw}
    {predicateProof : Term context Ty.unit proofRaw}
    (valueIsSN : Term.isStronglyNormalizing baseValue)
    (proofIsSN : Term.isStronglyNormalizing predicateProof) :
    Term.isStronglyNormalizing
      (Term.refineIntro predicate baseValue predicateProof) :=
  RawTerm.refineIntro_isStronglyNormalizing valueIsSN proofIsSN

/-- **K12.20.AJ.3 codataUnfold SN preservation** — codata
corecursive unfold bundles an initial state with a transition
function.  Binary cong; pair-style universal-in-conclusion. -/
theorem RawTerm.codataUnfold_isStronglyNormalizing {scope : Nat}
    {initialState : RawTerm scope}
    (stateIsSN : RawTerm.isStronglyNormalizing initialState) :
    ∀ {transition : RawTerm scope},
      RawTerm.isStronglyNormalizing transition →
      RawTerm.isStronglyNormalizing
        (RawTerm.codataUnfold initialState transition) := by
  induction stateIsSN with
  | intro currentState _ stateIH =>
    intro transition transitionIsSN
    induction transitionIsSN with
    | intro currentTransition transitionClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.codataUnfold currentState currentTransition) ?_
      intro target progressStep
      obtain ⟨stateTarget, transitionTarget, targetEq,
              stateStep, transitionStep⟩ :=
        RawStep.par.codataUnfold_inv progressStep.1
      subst targetEq
      by_cases stateEq : currentState = stateTarget
      · subst stateEq
        have transitionDistinct :
            currentTransition ≠ transitionTarget :=
          fun transitionEq =>
            progressStep.2
              (congrArg (RawTerm.codataUnfold currentState)
                transitionEq)
        exact innerIH transitionTarget
          ⟨transitionStep, transitionDistinct⟩
      · have stateProgress :
            RawStep.parProgress currentState stateTarget :=
          ⟨stateStep, stateEq⟩
        by_cases transitionEq : currentTransition = transitionTarget
        · subst transitionEq
          exact stateIH stateTarget stateProgress
            (RawTerm.isStronglyNormalizing.intro currentTransition
              transitionClosure)
        · exact stateIH stateTarget stateProgress
            (transitionClosure transitionTarget
              ⟨transitionStep, transitionEq⟩)

/-- Typed wrapper for codata unfold SN preservation. -/
theorem Term.codataUnfold_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stateType outputType : Ty level scope}
    {stateRaw transitionRaw : RawTerm scope}
    {initialState : Term context stateType stateRaw}
    {transition : Term context (Ty.arrow stateType outputType) transitionRaw}
    (stateIsSN : Term.isStronglyNormalizing initialState)
    (transitionIsSN : Term.isStronglyNormalizing transition) :
    Term.isStronglyNormalizing
      (Term.codataUnfold initialState transition) :=
  RawTerm.codataUnfold_isStronglyNormalizing stateIsSN transitionIsSN

/-- **K12.20.AK.1 pathCompose SN preservation** — cubical path
composition.  Pure binary cong over two path witnesses;
pair-style universal-in-conclusion. -/
theorem RawTerm.pathCompose_isStronglyNormalizing {scope : Nat}
    {leftPath : RawTerm scope}
    (leftIsSN : RawTerm.isStronglyNormalizing leftPath) :
    ∀ {rightPath : RawTerm scope},
      RawTerm.isStronglyNormalizing rightPath →
      RawTerm.isStronglyNormalizing
        (RawTerm.pathCompose leftPath rightPath) := by
  induction leftIsSN with
  | intro currentLeft _ leftIH =>
    intro rightPath rightIsSN
    induction rightIsSN with
    | intro currentRight rightClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.pathCompose currentLeft currentRight) ?_
      intro target progressStep
      obtain ⟨leftTarget, rightTarget, targetEq,
              leftStep, rightStep⟩ :=
        RawStep.par.pathCompose_inv progressStep.1
      subst targetEq
      by_cases leftEq : currentLeft = leftTarget
      · subst leftEq
        have rightDistinct :
            currentRight ≠ rightTarget := fun rightEq =>
          progressStep.2
            (congrArg (RawTerm.pathCompose currentLeft) rightEq)
        exact innerIH rightTarget ⟨rightStep, rightDistinct⟩
      · have leftProgress :
            RawStep.parProgress currentLeft leftTarget :=
          ⟨leftStep, leftEq⟩
        by_cases rightEq : currentRight = rightTarget
        · subst rightEq
          exact leftIH leftTarget leftProgress
            (RawTerm.isStronglyNormalizing.intro currentRight
              rightClosure)
        · exact leftIH leftTarget leftProgress
            (rightClosure rightTarget ⟨rightStep, rightEq⟩)

/-- **K12.20.AK.2 oeqTrans SN preservation** — observational
equality transitivity.  Pure binary cong over two proof
witnesses. -/
theorem RawTerm.oeqTrans_isStronglyNormalizing {scope : Nat}
    {firstProof : RawTerm scope}
    (firstIsSN : RawTerm.isStronglyNormalizing firstProof) :
    ∀ {secondProof : RawTerm scope},
      RawTerm.isStronglyNormalizing secondProof →
      RawTerm.isStronglyNormalizing
        (RawTerm.oeqTrans firstProof secondProof) := by
  induction firstIsSN with
  | intro currentFirst _ firstIH =>
    intro secondProof secondIsSN
    induction secondIsSN with
    | intro currentSecond secondClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.oeqTrans currentFirst currentSecond) ?_
      intro target progressStep
      obtain ⟨firstTarget, secondTarget, targetEq,
              firstStep, secondStep⟩ :=
        RawStep.par.oeqTrans_inv progressStep.1
      subst targetEq
      by_cases firstEq : currentFirst = firstTarget
      · subst firstEq
        have secondDistinct :
            currentSecond ≠ secondTarget := fun secondEq =>
          progressStep.2
            (congrArg (RawTerm.oeqTrans currentFirst) secondEq)
        exact innerIH secondTarget ⟨secondStep, secondDistinct⟩
      · have firstProgress :
            RawStep.parProgress currentFirst firstTarget :=
          ⟨firstStep, firstEq⟩
        by_cases secondEq : currentSecond = secondTarget
        · subst secondEq
          exact firstIH firstTarget firstProgress
            (RawTerm.isStronglyNormalizing.intro currentSecond
              secondClosure)
        · exact firstIH firstTarget firstProgress
            (secondClosure secondTarget ⟨secondStep, secondEq⟩)

/-- **K12.20.AK.3 equivCompose SN preservation** — equivalence
composition.  Pure binary cong over two equivalence witnesses. -/
theorem RawTerm.equivCompose_isStronglyNormalizing {scope : Nat}
    {firstEquiv : RawTerm scope}
    (firstIsSN : RawTerm.isStronglyNormalizing firstEquiv) :
    ∀ {secondEquiv : RawTerm scope},
      RawTerm.isStronglyNormalizing secondEquiv →
      RawTerm.isStronglyNormalizing
        (RawTerm.equivCompose firstEquiv secondEquiv) := by
  induction firstIsSN with
  | intro currentFirst _ firstIH =>
    intro secondEquiv secondIsSN
    induction secondIsSN with
    | intro currentSecond secondClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.equivCompose currentFirst currentSecond) ?_
      intro target progressStep
      obtain ⟨firstTarget, secondTarget, targetEq,
              firstStep, secondStep⟩ :=
        RawStep.par.equivCompose_inv progressStep.1
      subst targetEq
      by_cases firstEq : currentFirst = firstTarget
      · subst firstEq
        have secondDistinct :
            currentSecond ≠ secondTarget := fun secondEq =>
          progressStep.2
            (congrArg (RawTerm.equivCompose currentFirst) secondEq)
        exact innerIH secondTarget ⟨secondStep, secondDistinct⟩
      · have firstProgress :
            RawStep.parProgress currentFirst firstTarget :=
          ⟨firstStep, firstEq⟩
        by_cases secondEq : currentSecond = secondTarget
        · subst secondEq
          exact firstIH firstTarget firstProgress
            (RawTerm.isStronglyNormalizing.intro currentSecond
              secondClosure)
        · exact firstIH firstTarget firstProgress
            (secondClosure secondTarget ⟨secondStep, secondEq⟩)

/-- **K12.20.AL.1 sessionRecv SN preservation** — session-type
receive operation.  Pure unary cong over the channel witness. -/
theorem RawTerm.sessionRecv_isStronglyNormalizing {scope : Nat}
    {channel : RawTerm scope}
    (channelIsSN : RawTerm.isStronglyNormalizing channel) :
    RawTerm.isStronglyNormalizing (RawTerm.sessionRecv channel) := by
  induction channelIsSN with
  | intro currentChannel _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.sessionRecv currentChannel) ?_
    intro target progressStep
    obtain ⟨channelTarget, targetEq, channelStep⟩ :=
      RawStep.par.sessionRecv_inv progressStep.1
    subst targetEq
    have channelDistinct :
        currentChannel ≠ channelTarget := fun channelEq =>
      progressStep.2 (congrArg RawTerm.sessionRecv channelEq)
    exact inductiveHypothesis channelTarget
      ⟨channelStep, channelDistinct⟩

/-- **K12.20.AL.2 sessionSend SN preservation** — session-type
send operation bundles a channel with a payload.  Pure binary
cong; pair-style universal-in-conclusion. -/
theorem RawTerm.sessionSend_isStronglyNormalizing {scope : Nat}
    {channel : RawTerm scope}
    (channelIsSN : RawTerm.isStronglyNormalizing channel) :
    ∀ {payload : RawTerm scope},
      RawTerm.isStronglyNormalizing payload →
      RawTerm.isStronglyNormalizing
        (RawTerm.sessionSend channel payload) := by
  induction channelIsSN with
  | intro currentChannel _ channelIH =>
    intro payload payloadIsSN
    induction payloadIsSN with
    | intro currentPayload payloadClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.sessionSend currentChannel currentPayload) ?_
      intro target progressStep
      obtain ⟨channelTarget, payloadTarget, targetEq,
              channelStep, payloadStep⟩ :=
        RawStep.par.sessionSend_inv progressStep.1
      subst targetEq
      by_cases channelEq : currentChannel = channelTarget
      · subst channelEq
        have payloadDistinct :
            currentPayload ≠ payloadTarget := fun payloadEq =>
          progressStep.2
            (congrArg (RawTerm.sessionSend currentChannel) payloadEq)
        exact innerIH payloadTarget ⟨payloadStep, payloadDistinct⟩
      · have channelProgress :
            RawStep.parProgress currentChannel channelTarget :=
          ⟨channelStep, channelEq⟩
        by_cases payloadEq : currentPayload = payloadTarget
        · subst payloadEq
          exact channelIH channelTarget channelProgress
            (RawTerm.isStronglyNormalizing.intro currentPayload
              payloadClosure)
        · exact channelIH channelTarget channelProgress
            (payloadClosure payloadTarget
              ⟨payloadStep, payloadEq⟩)

/-- **K12.20.AL.3 effectPerform SN preservation** — algebraic
effect operation invocation bundles an operation tag with its
arguments.  Pure binary cong; pair-style universal-in-conclusion. -/
theorem RawTerm.effectPerform_isStronglyNormalizing {scope : Nat}
    {operationTag : RawTerm scope}
    (operationIsSN : RawTerm.isStronglyNormalizing operationTag) :
    ∀ {arguments : RawTerm scope},
      RawTerm.isStronglyNormalizing arguments →
      RawTerm.isStronglyNormalizing
        (RawTerm.effectPerform operationTag arguments) := by
  induction operationIsSN with
  | intro currentOperation _ operationIH =>
    intro arguments argumentsIsSN
    induction argumentsIsSN with
    | intro currentArguments argumentsClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.effectPerform currentOperation currentArguments) ?_
      intro target progressStep
      obtain ⟨operationTarget, argumentsTarget, targetEq,
              operationStep, argumentsStep⟩ :=
        RawStep.par.effectPerform_inv progressStep.1
      subst targetEq
      by_cases operationEq : currentOperation = operationTarget
      · subst operationEq
        have argumentsDistinct :
            currentArguments ≠ argumentsTarget := fun argumentsEq =>
          progressStep.2
            (congrArg (RawTerm.effectPerform currentOperation)
              argumentsEq)
        exact innerIH argumentsTarget
          ⟨argumentsStep, argumentsDistinct⟩
      · have operationProgress :
            RawStep.parProgress currentOperation operationTarget :=
          ⟨operationStep, operationEq⟩
        by_cases argumentsEq : currentArguments = argumentsTarget
        · subst argumentsEq
          exact operationIH operationTarget operationProgress
            (RawTerm.isStronglyNormalizing.intro currentArguments
              argumentsClosure)
        · exact operationIH operationTarget operationProgress
            (argumentsClosure argumentsTarget
              ⟨argumentsStep, argumentsEq⟩)

/-- **K12.20.AM glueIntro SN preservation** — cubical Glue
introduction bundles a base value with a partial-element witness.
Pure binary cong; pair-style universal-in-conclusion.  Closes
the cubical/HoTT intro slice of the SN-helper rail. -/
theorem RawTerm.glueIntro_isStronglyNormalizing {scope : Nat}
    {baseValue : RawTerm scope}
    (baseIsSN : RawTerm.isStronglyNormalizing baseValue) :
    ∀ {partialValue : RawTerm scope},
      RawTerm.isStronglyNormalizing partialValue →
      RawTerm.isStronglyNormalizing
        (RawTerm.glueIntro baseValue partialValue) := by
  induction baseIsSN with
  | intro currentBase _ baseIH =>
    intro partialValue partialIsSN
    induction partialIsSN with
    | intro currentPartial partialClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.glueIntro currentBase currentPartial) ?_
      intro target progressStep
      obtain ⟨baseTarget, partialTarget, targetEq,
              baseStep, partialStep⟩ :=
        RawStep.par.glueIntro_inv progressStep.1
      subst targetEq
      by_cases baseEq : currentBase = baseTarget
      · subst baseEq
        have partialDistinct :
            currentPartial ≠ partialTarget := fun partialEq =>
          progressStep.2
            (congrArg (RawTerm.glueIntro currentBase) partialEq)
        exact innerIH partialTarget ⟨partialStep, partialDistinct⟩
      · have baseProgress :
            RawStep.parProgress currentBase baseTarget :=
          ⟨baseStep, baseEq⟩
        by_cases partialEq : currentPartial = partialTarget
        · subst partialEq
          exact baseIH baseTarget baseProgress
            (RawTerm.isStronglyNormalizing.intro currentPartial
              partialClosure)
        · exact baseIH baseTarget baseProgress
            (partialClosure partialTarget
              ⟨partialStep, partialEq⟩)

/-- Typed wrapper for cubical Glue-introduction SN preservation.

This exposes SN for `Term.glueIntro` from SN of its base and partial
payloads.  It deliberately does not claim the full Glue Reducible
introduction closure. -/
theorem Term.glueIntro_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (baseType : Ty level scope)
    (boundaryWitness : RawTerm scope)
    {baseRaw partialRaw : RawTerm scope}
    {baseValue : Term context baseType baseRaw}
    {partialValue : Term context baseType partialRaw}
    (baseIsSN : Term.isStronglyNormalizing baseValue)
    (partialIsSN : Term.isStronglyNormalizing partialValue) :
    Term.isStronglyNormalizing
      (Term.glueIntro modeIsUnivalent baseType boundaryWitness
        baseValue partialValue) :=
  RawTerm.glueIntro_isStronglyNormalizing baseIsSN partialIsSN

/-- Head-β SN expansion for cubical Glue elimination.

If the Glue base value and partial value are strongly normalizing, then
`glueElim (glueIntro base partial)` is strongly normalizing.  Congruence
reducts recurse through both payloads; β reducts land on a reduct of the
base payload. -/
theorem RawTerm.glueElim_glueIntro_isStronglyNormalizing
    {scope : Nat}
    {baseValue : RawTerm scope}
    (baseIsSN : RawTerm.isStronglyNormalizing baseValue) :
    ∀ {partialValue : RawTerm scope},
      RawTerm.isStronglyNormalizing partialValue →
      RawTerm.isStronglyNormalizing
        (RawTerm.glueElim
          (RawTerm.glueIntro baseValue partialValue)) := by
  induction baseIsSN with
  | intro currentBase baseClosure baseIH =>
    intro partialValue partialIsSN
    induction partialIsSN with
    | intro currentPartial partialClosure partialIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.glueElim
          (RawTerm.glueIntro currentBase currentPartial)) ?_
      intro target progressStep
      rcases RawStep.par.glueElim_inv progressStep.1 with
        ⟨gluedTarget, targetEq, gluedStep⟩
        | ⟨baseTarget, partialTarget, targetEq, gluedStep⟩
      · obtain ⟨baseTarget, partialTarget, gluedTargetEq,
            baseStep, partialStep⟩ :=
          RawStep.par.glueIntro_inv gluedStep
        subst gluedTargetEq
        subst targetEq
        by_cases baseEq : currentBase = baseTarget
        · subst baseEq
          by_cases partialEq : currentPartial = partialTarget
          · subst partialEq
            exact False.elim (progressStep.2 rfl)
          · exact partialIH partialTarget
              ⟨partialStep, partialEq⟩
        · have baseProgress :
              RawStep.parProgress currentBase baseTarget :=
            ⟨baseStep, baseEq⟩
          by_cases partialEq : currentPartial = partialTarget
          · subst partialEq
            exact baseIH baseTarget baseProgress
              (RawTerm.isStronglyNormalizing.intro currentPartial
                partialClosure)
          · exact baseIH baseTarget baseProgress
              (partialClosure partialTarget
                ⟨partialStep, partialEq⟩)
      · obtain ⟨gluedBaseTarget, _gluedPartialTarget,
            gluedTargetEq, baseStep, _partialStep⟩ :=
          RawStep.par.glueIntro_inv gluedStep
        injection gluedTargetEq with _scopeEq baseTargetEq
          _partialTargetEq
        rw [targetEq]
        have baseStepToTarget :
            RawStep.par currentBase baseTarget := by
          rw [baseTargetEq]
          exact baseStep
        by_cases baseEq : currentBase = baseTarget
        · subst baseEq
          exact RawTerm.isStronglyNormalizing.intro
            currentBase baseClosure
        · exact baseClosure baseTarget
            ⟨baseStepToTarget, baseEq⟩

/-- Typed wrapper for `glueElim (glueIntro base partial)` SN expansion.

This is an SN bridge only.  It does not claim the full `Reducible`
backward closure for Glue introduction. -/
theorem Term.glueElim_glueIntro_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (baseType : Ty level scope)
    (boundaryWitness : RawTerm scope)
    {baseRaw partialRaw : RawTerm scope}
    {baseValue : Term context baseType baseRaw}
    {partialValue : Term context baseType partialRaw}
    (baseIsSN : Term.isStronglyNormalizing baseValue)
    (partialIsSN : Term.isStronglyNormalizing partialValue) :
    Term.isStronglyNormalizing
      (Term.glueElim modeIsUnivalent
        (Term.glueIntro modeIsUnivalent baseType boundaryWitness
          baseValue partialValue)) :=
  RawTerm.glueElim_glueIntro_isStronglyNormalizing
    baseIsSN partialIsSN

/-- Generic Glue-elimination SN preservation.

Congruent reducts recurse through the glued term.  A β reduct first
develops the glued term into a `glueIntro`; the eliminated base value is
SN by the Glue-intro base inversion lemma. -/
theorem RawTerm.glueElim_isStronglyNormalizing {scope : Nat}
    {gluedRaw : RawTerm scope}
    (gluedIsSN : RawTerm.isStronglyNormalizing gluedRaw) :
    RawTerm.isStronglyNormalizing (RawTerm.glueElim gluedRaw) := by
  induction gluedIsSN with
  | intro currentGlued gluedClosure gluedIH =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.glueElim currentGlued) ?_
    intro target progressStep
    rcases RawStep.par.glueElim_inv progressStep.1 with
      ⟨gluedTarget, targetEq, gluedStep⟩
      | ⟨baseTarget, partialTarget, targetEq, gluedStep⟩
    · subst targetEq
      by_cases gluedEq : currentGlued = gluedTarget
      · subst gluedEq
        exact (progressStep.2 rfl).elim
      · exact gluedIH gluedTarget ⟨gluedStep, gluedEq⟩
    · rw [targetEq]
      have developedGluedIsSN :
          RawTerm.isStronglyNormalizing
            (RawTerm.glueIntro baseTarget partialTarget) := by
        by_cases gluedEq :
            currentGlued =
              RawTerm.glueIntro baseTarget partialTarget
        · rw [← gluedEq]
          exact RawTerm.isStronglyNormalizing.intro
            currentGlued gluedClosure
        · exact gluedClosure
            (RawTerm.glueIntro baseTarget partialTarget)
            ⟨gluedStep, gluedEq⟩
      exact RawTerm.glueIntro_base_isStronglyNormalizing
        developedGluedIsSN

/-- Direct M04 SN case for Glue elimination from any SN glued term. -/
theorem Term.glueElim_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty level scope}
    {boundaryWitness gluedRaw : RawTerm scope}
    {gluedValue : Term context
        (Ty.glue baseType boundaryWitness) gluedRaw}
    (gluedIsSN : Term.isStronglyNormalizing gluedValue) :
    Term.isStronglyNormalizing
      (Term.glueElim modeIsUnivalent gluedValue) :=
  RawTerm.glueElim_isStronglyNormalizing gluedIsSN

/-- **K12.20.AH equivIntro SN preservation** — equivalence intro
bundles a forward and backward function.  Binary cong; uses the
pair-style universal-in-conclusion pattern to keep the backward
IH universal under outer induction on the forward SN witness. -/
theorem RawTerm.equivIntro_isStronglyNormalizing {scope : Nat}
    {forwardFn : RawTerm scope}
    (forwardIsSN : RawTerm.isStronglyNormalizing forwardFn) :
    ∀ {backwardFn : RawTerm scope},
      RawTerm.isStronglyNormalizing backwardFn →
      RawTerm.isStronglyNormalizing
        (RawTerm.equivIntro forwardFn backwardFn) := by
  induction forwardIsSN with
  | intro currentForward _ forwardIH =>
    intro backwardFn backwardIsSN
    induction backwardIsSN with
    | intro currentBackward backwardClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.equivIntro currentForward currentBackward) ?_
      intro target progressStep
      obtain ⟨forwardTarget, backwardTarget, targetEq,
              forwardStep, backwardStep⟩ :=
        RawStep.par.equivIntro_inv progressStep.1
      subst targetEq
      by_cases forwardEq : currentForward = forwardTarget
      · subst forwardEq
        have backwardDistinct :
            currentBackward ≠ backwardTarget := fun backwardEq =>
          progressStep.2
            (congrArg (RawTerm.equivIntro currentForward) backwardEq)
        exact innerIH backwardTarget ⟨backwardStep, backwardDistinct⟩
      · have forwardProgress :
            RawStep.parProgress currentForward forwardTarget :=
          ⟨forwardStep, forwardEq⟩
        by_cases backwardEq : currentBackward = backwardTarget
        · subst backwardEq
          exact forwardIH forwardTarget forwardProgress
            (RawTerm.isStronglyNormalizing.intro currentBackward
              backwardClosure)
        · exact forwardIH forwardTarget forwardProgress
            (backwardClosure backwardTarget ⟨backwardStep, backwardEq⟩)

/-- Typed wrapper for heterogeneous equivalence-introduction SN.

`Term.equivIntroHet` has raw shape `RawTerm.equivIntro forward backward`;
the proof witnesses are typed obligations and do not occur in the raw
computational payload.  Thus SN depends only on the forward and backward
functions.  This is an SN bridge, not the full `Ty.equiv` Reducible
introduction closure. -/
theorem Term.equivIntroHet_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierA carrierB : Ty level scope}
    {forwardRaw backwardRaw leftInvRaw rightInvRaw : RawTerm scope}
    {forward :
      Term context (Ty.arrow carrierA carrierB) forwardRaw}
    {backward :
      Term context (Ty.arrow carrierB carrierA) backwardRaw}
    {leftInv :
      Term context
        (equivIntroHetLeftInverseType carrierA forwardRaw backwardRaw)
        leftInvRaw}
    {rightInv :
      Term context
        (equivIntroHetRightInverseType carrierB forwardRaw backwardRaw)
        rightInvRaw}
    (forwardIsSN : Term.isStronglyNormalizing forward)
    (backwardIsSN : Term.isStronglyNormalizing backward) :
    Term.isStronglyNormalizing
      (Term.equivIntroHet forward backward leftInv rightInv) :=
  RawTerm.equivIntro_isStronglyNormalizing forwardIsSN backwardIsSN


end LeanFX2
