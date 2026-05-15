import LeanFX2.Term
import LeanFX2.Foundation.Polygraph.PolyTerm
import LeanFX2.Foundation.Polygraph.PolyTermRoundtrip

/-! # `Term.toPoly` — typed forward bijection from `Term` to `PolyTerm`.

K11.10-B (#1752): the typed-layer forward direction of the polygraph
bijection.  Structural recursion across all 77 `Term` constructors
mapping each typed kernel term to its `PolyTerm` mirror with identical
typing context and kernel type indices.  The raw payload converts via
`RawTerm.toRawPoly` (existing `@[reducible]` in `PolyTerm.lean`), so
the resulting `PolyTerm` carries `raw.toRawPoly` as its raw index by
definitional equality.

## Why forward direction needs the K11.12 roundtrip identity

For 11 Term constructors whose `Ty` indices embed a raw payload (either
via `Ty.subst0` or directly via `Ty.id`/`Ty.oeq`/`Ty.idStrict`/`Ty.piTy`),
the natural recursion produces a `PolyTerm` whose `Ty` index uses
`raw.toRawPoly.toRawTerm` while the function signature demands the `Ty`
index use `raw`.  K11.12's
`RawTerm.toRawPoly_toRawTerm : raw.toRawPoly.toRawTerm = raw` discharges
the gap via `Eq.rec` (propext-free).  Cast helper `PolyTerm.castTyIndex`
fixes the motive to act ONLY on the `Ty` index, leaving the
`RawPolyTerm` third index untouched.

## Architecture

* Indices `{mode level scope context targetType rawTerm}` are hoisted
  before the explicit `Term` argument per the match-arity rule
  (`feedback_lean_match_arity_axioms.md`).
* Each case mirrors the corresponding `PolyTerm` constructor exactly,
  recursing on every typed sub-`Term` argument.  Raw-only payloads
  carry through via `.toRawPoly` conversion.  The 11 ctors with
  raw-in-Ty signatures use `PolyTerm.castTyIndex` casts driven by
  K11.12.
* The function is structurally terminating on the Term argument
  — pure `def`, not `partial def`, not `noncomputable`.

## Audit

* `#print axioms Term.toPoly` reports "does not depend on any axioms"
* All `▸` casts derive from K11.12, which is itself zero-axiom. -/

namespace LeanFX2

open LeanFX2.Foundation.Polygraph

/-- Cast helper for raw-in-`Ty` ctors: rewrite the `Ty` index of a
`PolyTerm` along an equality between Ty values, leaving the
`RawPolyTerm` third index untouched.  Used by the 11 K11.12-driven
casts in `Term.toPoly`.  Propext-free — `▸` over a motive that fixes
the third index as a parameter. -/
@[inline] private def PolyTerm.castTyIndex {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {targetA targetB : Ty level scope}
    {rawPoly : RawPolyTerm scope}
    (typeEq : targetA = targetB)
    (term : PolyTerm context targetA rawPoly) :
    PolyTerm context targetB rawPoly :=
  typeEq ▸ term

/-- Local two-argument congruence helper (Lean 4 stdlib's `congrArg`
takes one argument; combining for two args avoids opening `Function`
or pulling in mathlib). -/
private theorem congrArg2 {α β γ : Sort _}
    {a₁ a₂ : α} {b₁ b₂ : β}
    (f : α → β → γ) (ha : a₁ = a₂) (hb : b₁ = b₂) :
    f a₁ b₁ = f a₂ b₂ :=
  congr (congrArg f ha) hb

/-- Typed forward bijection from `Term` to `PolyTerm`.  Structural
recursion mirrors each Term ctor to its PolyTerm counterpart; the raw
payload index converts via `RawTerm.toRawPoly` definitionally.  The
11 raw-in-Ty ctors use K11.12 `RawTerm.toRawPoly_toRawTerm` casts. -/
def Term.toPoly {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {targetType : Ty level scope}
    {rawTerm : RawTerm scope} :
    Term context targetType rawTerm →
    PolyTerm context targetType rawTerm.toRawPoly
  | .var position => .var position
  | .unit => .unit
  | .lam body => .lam body.toPoly
  | .app functionTerm argumentTerm =>
      .app functionTerm.toPoly argumentTerm.toPoly
  | .lamPi body => .lamPi body.toPoly
  | .appPi (domainType := domainType) (codomainType := codomainType)
      (argumentRaw := argumentRaw) functionTerm argumentTerm =>
      PolyTerm.castTyIndex
        (congrArg (codomainType.subst0 domainType)
          (RawTerm.toRawPoly_toRawTerm argumentRaw))
        (PolyTerm.appPi functionTerm.toPoly argumentTerm.toPoly)
  | .pair (firstType := firstType) (secondType := secondType)
      (firstRaw := firstRaw) firstValue secondValue =>
      PolyTerm.pair firstValue.toPoly
        (PolyTerm.castTyIndex
          (congrArg (secondType.subst0 firstType)
            (RawTerm.toRawPoly_toRawTerm firstRaw).symm)
          secondValue.toPoly)
  | .fst pairTerm => .fst pairTerm.toPoly
  | .snd (firstType := firstType) (secondType := secondType)
      (pairRaw := pairRaw) pairTerm =>
      PolyTerm.castTyIndex
        (congrArg (fun r => secondType.subst0 firstType (RawTerm.fst r))
          (RawTerm.toRawPoly_toRawTerm pairRaw))
        (PolyTerm.snd pairTerm.toPoly)
  | .boolTrue => .boolTrue
  | .boolFalse => .boolFalse
  | .boolElim (motiveType := motiveType) (scrutineeRaw := scrutineeRaw)
      scrutinee thenBranch elseBranch =>
      PolyTerm.castTyIndex
        (congrArg (motiveType.subst0 Ty.bool)
          (RawTerm.toRawPoly_toRawTerm scrutineeRaw))
        (PolyTerm.boolElim scrutinee.toPoly thenBranch.toPoly
          elseBranch.toPoly)
  | .natZero => .natZero
  | .natSucc predecessor => .natSucc predecessor.toPoly
  | .natElim scrutinee zeroBranch succBranch =>
      .natElim scrutinee.toPoly zeroBranch.toPoly succBranch.toPoly
  | .natRec scrutinee zeroBranch succBranch =>
      .natRec scrutinee.toPoly zeroBranch.toPoly succBranch.toPoly
  | .listNil => .listNil
  | .listCons headTerm tailTerm =>
      .listCons headTerm.toPoly tailTerm.toPoly
  | .listElim scrutinee nilBranch consBranch =>
      .listElim scrutinee.toPoly nilBranch.toPoly consBranch.toPoly
  | .optionNone => .optionNone
  | .optionSome valueTerm => .optionSome valueTerm.toPoly
  | .optionMatch scrutinee noneBranch someBranch =>
      .optionMatch scrutinee.toPoly noneBranch.toPoly someBranch.toPoly
  | .eitherInl valueTerm => .eitherInl valueTerm.toPoly
  | .eitherInr valueTerm => .eitherInr valueTerm.toPoly
  | .eitherMatch scrutinee leftBranch rightBranch =>
      .eitherMatch scrutinee.toPoly leftBranch.toPoly rightBranch.toPoly
  | .refl carrier rawWitness =>
      PolyTerm.castTyIndex
        (congrArg (fun r => Ty.id carrier r r)
          (RawTerm.toRawPoly_toRawTerm rawWitness))
        (PolyTerm.refl carrier rawWitness.toRawPoly)
  | .idJ baseCase witness =>
      .idJ baseCase.toPoly witness.toPoly
  | .oeqRefl carrier rawWitness =>
      PolyTerm.castTyIndex
        (congrArg (fun r => Ty.oeq carrier r r)
          (RawTerm.toRawPoly_toRawTerm rawWitness))
        (PolyTerm.oeqRefl carrier rawWitness.toRawPoly)
  | .oeqJ baseCase witness =>
      .oeqJ baseCase.toPoly witness.toPoly
  | .oeqFunext domainType codomainType leftFunctionRaw rightFunctionRaw
      pointwiseProof =>
      .oeqFunext domainType codomainType leftFunctionRaw rightFunctionRaw
        pointwiseProof.toPoly
  | .idStrictRefl modeIsStrict carrier rawWitness =>
      PolyTerm.castTyIndex
        (congrArg (fun r => Ty.idStrict carrier r r)
          (RawTerm.toRawPoly_toRawTerm rawWitness))
        (PolyTerm.idStrictRefl modeIsStrict carrier rawWitness.toRawPoly)
  | .idStrictRec modeIsStrict baseCase witness =>
      .idStrictRec modeIsStrict baseCase.toPoly witness.toPoly
  | .modIntro innerTerm => .modIntro innerTerm.toPoly
  | .modElim innerTerm => .modElim innerTerm.toPoly
  | .subsume innerTerm => .subsume innerTerm.toPoly
  | .interval0 => .interval0
  | .interval1 => .interval1
  | .intervalOpp innerValue => .intervalOpp innerValue.toPoly
  | .intervalMeet leftValue rightValue =>
      .intervalMeet leftValue.toPoly rightValue.toPoly
  | .intervalJoin leftValue rightValue =>
      .intervalJoin leftValue.toPoly rightValue.toPoly
  | .pathLam modeIsUnivalent carrierType leftEndpoint rightEndpoint body =>
      .pathLam modeIsUnivalent carrierType leftEndpoint rightEndpoint
        body.toPoly
  | .pathApp modeIsUnivalent pathTerm intervalTerm =>
      .pathApp modeIsUnivalent pathTerm.toPoly intervalTerm.toPoly
  | .glueIntro modeIsUnivalent baseType boundaryWitness
      baseValue partialValue =>
      .glueIntro modeIsUnivalent baseType boundaryWitness
        baseValue.toPoly partialValue.toPoly
  | .glueElim modeIsUnivalent gluedValue =>
      .glueElim modeIsUnivalent gluedValue.toPoly
  | .transp modeIsUnivalent universeLevel universeLevelLt
      sourceType targetType sourceTypeRaw targetTypeRaw
      typePath sourceValue =>
      .transp modeIsUnivalent universeLevel universeLevelLt
        sourceType targetType sourceTypeRaw targetTypeRaw
        typePath.toPoly sourceValue.toPoly
  | .hcomp modeIsUnivalent sidesValue capValue =>
      .hcomp modeIsUnivalent sidesValue.toPoly capValue.toPoly
  | .hcompPath modeIsUnivalent leftEndpoint rightEndpoint
      sidesPath capValue =>
      .hcompPath modeIsUnivalent leftEndpoint rightEndpoint
        sidesPath.toPoly capValue.toPoly
  | .recordIntro firstField => .recordIntro firstField.toPoly
  | .recordProj recordValue => .recordProj recordValue.toPoly
  | .refineIntro predicate baseValue predicateProof =>
      .refineIntro predicate baseValue.toPoly predicateProof.toPoly
  | .refineElim refinedValue => .refineElim refinedValue.toPoly
  | .codataUnfold initialState transition =>
      .codataUnfold initialState.toPoly transition.toPoly
  | .codataDest codataValue => .codataDest codataValue.toPoly
  | .sessionSend protocolStep channel payload =>
      .sessionSend protocolStep channel.toPoly payload.toPoly
  | .sessionRecv channel => .sessionRecv channel.toPoly
  | .effectPerform effectTag effectRow operationSignature
      canPerformOperation operationTag arguments =>
      .effectPerform effectTag effectRow operationSignature
        canPerformOperation operationTag.toPoly arguments.toPoly
  | .universeCode innerLevel outerLevel cumulOk levelLe =>
      .universeCode innerLevel outerLevel cumulOk levelLe
  | .cumulUp lowerLevel higherLevel cumulMonotone levelLeLow
      levelLeHigh typeCode =>
      .cumulUp lowerLevel higherLevel cumulMonotone levelLeLow
        levelLeHigh typeCode.toPoly
  | .equivReflId carrier => .equivReflId carrier
  | .funextRefl domainType codomainType applyRaw =>
      PolyTerm.castTyIndex
        (congrArg (fun r => Ty.piTy domainType
            (Ty.id codomainType.weaken r r))
          (RawTerm.toRawPoly_toRawTerm applyRaw))
        (PolyTerm.funextRefl domainType codomainType applyRaw.toRawPoly)
  | .equivReflIdAtId innerLevel innerLevelLt carrier carrierRaw =>
      .equivReflIdAtId innerLevel innerLevelLt carrier carrierRaw
  | .funextReflAtId domainType codomainType applyRaw =>
      PolyTerm.castTyIndex
        (congrArg (fun r => Ty.id (Ty.arrow domainType codomainType)
            (RawTerm.lam (RawTerm.refl r))
            (RawTerm.lam (RawTerm.refl r)))
          (RawTerm.toRawPoly_toRawTerm applyRaw))
        (PolyTerm.funextReflAtId domainType codomainType
          applyRaw.toRawPoly)
  | .equivIntroHet (carrierA := carrierA) (carrierB := carrierB)
      (forwardRaw := forwardRaw) (backwardRaw := backwardRaw)
      forward backward leftInv rightInv =>
      PolyTerm.equivIntroHet forward.toPoly backward.toPoly
        (PolyTerm.castTyIndex
          (congrArg2 (equivIntroHetLeftInverseType carrierA)
            (RawTerm.toRawPoly_toRawTerm forwardRaw).symm
            (RawTerm.toRawPoly_toRawTerm backwardRaw).symm)
          leftInv.toPoly)
        (PolyTerm.castTyIndex
          (congrArg2 (equivIntroHetRightInverseType carrierB)
            (RawTerm.toRawPoly_toRawTerm forwardRaw).symm
            (RawTerm.toRawPoly_toRawTerm backwardRaw).symm)
          rightInv.toPoly)
  | .equivApp equivTerm argument =>
      .equivApp equivTerm.toPoly argument.toPoly
  | .uaIntroHet innerLevel innerLevelLt carrierARaw carrierBRaw
      equivWitness =>
      .uaIntroHet innerLevel innerLevelLt carrierARaw carrierBRaw
        equivWitness.toPoly
  | .funextIntroHet domainType codomainType applyARaw applyBRaw =>
      PolyTerm.castTyIndex
        (congrArg2 (fun a b => Ty.id (Ty.arrow domainType codomainType)
            (RawTerm.lam a) (RawTerm.lam b))
          (RawTerm.toRawPoly_toRawTerm applyARaw)
          (RawTerm.toRawPoly_toRawTerm applyBRaw))
        (PolyTerm.funextIntroHet domainType codomainType
          applyARaw.toRawPoly applyBRaw.toRawPoly)
  | .arrowCode outerLevel levelLe domainCodeRaw codomainCodeRaw =>
      .arrowCode outerLevel levelLe
        domainCodeRaw.toRawPoly codomainCodeRaw.toRawPoly
  | .piTyCode outerLevel levelLe domainCodeRaw codomainCodeRaw =>
      .piTyCode outerLevel levelLe
        domainCodeRaw.toRawPoly codomainCodeRaw.toRawPoly
  | .sigmaTyCode outerLevel levelLe domainCodeRaw codomainCodeRaw =>
      .sigmaTyCode outerLevel levelLe
        domainCodeRaw.toRawPoly codomainCodeRaw.toRawPoly
  | .productCode outerLevel levelLe firstCodeRaw secondCodeRaw =>
      .productCode outerLevel levelLe
        firstCodeRaw.toRawPoly secondCodeRaw.toRawPoly
  | .sumCode outerLevel levelLe leftCodeRaw rightCodeRaw =>
      .sumCode outerLevel levelLe
        leftCodeRaw.toRawPoly rightCodeRaw.toRawPoly
  | .listCode outerLevel levelLe elementCodeRaw =>
      .listCode outerLevel levelLe elementCodeRaw.toRawPoly
  | .optionCode outerLevel levelLe elementCodeRaw =>
      .optionCode outerLevel levelLe elementCodeRaw.toRawPoly
  | .eitherCode outerLevel levelLe leftCodeRaw rightCodeRaw =>
      .eitherCode outerLevel levelLe
        leftCodeRaw.toRawPoly rightCodeRaw.toRawPoly
  | .idCode outerLevel levelLe typeCodeRaw leftRaw rightRaw =>
      .idCode outerLevel levelLe
        typeCodeRaw.toRawPoly leftRaw.toRawPoly rightRaw.toRawPoly
  | .equivCode outerLevel levelLe leftTypeCodeRaw rightTypeCodeRaw =>
      .equivCode outerLevel levelLe
        leftTypeCodeRaw.toRawPoly rightTypeCodeRaw.toRawPoly
  | .uaToEquiv innerLevel innerLevelLt leftTy rightTy
      leftTyRaw rightTyRaw proof =>
      .uaToEquiv innerLevel innerLevelLt leftTy rightTy
        leftTyRaw rightTyRaw proof.toPoly
  | .equivApply equivTerm argument =>
      .equivApply equivTerm.toPoly argument.toPoly

end LeanFX2
