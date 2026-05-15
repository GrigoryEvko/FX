import LeanFX2.Reducibility.NeutralSNIntro.Codes

/-! # LeanFX2.Reducibility.NeutralSNClosure.TypeCodeSN

K12.20.AS raw + Term SN witnesses for type-code trees: the
`RawTerm.isStronglyNormalizing_of_typeCode` headline, the Term
wrappers for all 11 universe-code leaves (`universeCode` /
`arrowCode` / `piTyCode` / `sigmaTyCode` / `productCode` /
`sumCode` / `eitherCode` / `equivCode` / `listCode` /
`optionCode` / `idCode`), plus
`RawTerm.subst_identity_isStronglyNormalizing_of_typeCode`.

## Root status

Layer 3 metatheory leaf.  First slice of NeutralSNClosure. -/

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


end LeanFX2
