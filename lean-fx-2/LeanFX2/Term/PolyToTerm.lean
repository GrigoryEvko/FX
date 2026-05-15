import LeanFX2.Term
import LeanFX2.Foundation.Polygraph.PolyTerm

/-! # `PolyTerm.toTerm` — typed backward bijection from `PolyTerm` to `Term`.

K11.11 (#1748): the typed-layer backward direction of the polygraph
bijection.  Structural recursion across all 77 `PolyTerm`
constructors mapping each typed polygraph term to its `Term` mirror
with identical typing context and kernel type indices.  The raw
payload index converts via `RawPolyTerm.toRawTerm` (existing
`@[reducible]` in `PolyTerm.lean`), so the resulting `Term` carries
`rawPoly.toRawTerm` as its raw index by definitional equality.

## Why backward direction is easier than forward

PolyTerm constructors that involve `Ty.subst0` of a raw payload (e.g.
`appPi`, `pair`, `snd`, `boolElim`, `natElim`, `natRec`, `pathApp`,
`transp`) encode the raw endpoint as `argumentPolyRaw.toRawTerm` in
their `Ty` indices.  Mapping `PolyTerm → Term` aligns naturally: the
Term constructor takes a `RawTerm`-valued endpoint, which is exactly
`argumentPolyRaw.toRawTerm`.  No roundtrip identity is needed.

The forward direction (`Term.toPoly`, K11.10-B) requires the K11.12
roundtrip theorem `RawTerm.toRawPoly_toRawTerm` to discharge an
analogous index mismatch — `argumentRaw.toRawPoly.toRawTerm =
argumentRaw` is NOT definitional and needs the K11.12 raw roundtrip
identity for term construction.

## Architecture

* Indices `{mode level scope context targetType rawPoly}` are hoisted
  before the explicit `PolyTerm` argument per the match-arity rule
  (`feedback_lean_match_arity_axioms.md`).
* Each case mirrors the corresponding `Term` constructor exactly,
  recursing on every typed sub-`PolyTerm` argument.  Raw-only payloads
  carry through unchanged because both sides reuse the same
  `RawTerm`-valued schematic carriers (e.g. `protocolStep` in
  `sessionSend`, `effectTag` in `effectPerform`).
* The function is structurally terminating on the PolyTerm argument
  — pure `def`, not `partial def`, not `noncomputable`.

## Audit

* `#print axioms PolyTerm.toTerm` reports "does not depend on any
  axioms"
* All `PolyTerm.toTerm_<ctor>` derived equations follow by `rfl`
  (the chosen constructors are mechanically aligned with their
  Term mirrors). -/

namespace LeanFX2

open LeanFX2.Foundation.Polygraph

/-- Typed backward bijection from `PolyTerm` to `Term`.  Structural
recursion mirrors each PolyTerm ctor to its Term counterpart; the raw
payload index converts via `RawPolyTerm.toRawTerm` definitionally. -/
def PolyTerm.toTerm {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {targetType : Ty level scope}
    {rawPoly : LeanFX2.Foundation.Polygraph.RawPolyTerm scope} :
    PolyTerm context targetType rawPoly →
    Term context targetType rawPoly.toRawTerm
  | .var position => .var position
  | .unit => .unit
  | .lam body => .lam body.toTerm
  | .app functionTerm argumentTerm =>
      .app functionTerm.toTerm argumentTerm.toTerm
  | .lamPi body => .lamPi body.toTerm
  | .appPi functionTerm argumentTerm =>
      .appPi functionTerm.toTerm argumentTerm.toTerm
  | .pair firstValue secondValue =>
      .pair firstValue.toTerm secondValue.toTerm
  | .fst pairTerm => .fst pairTerm.toTerm
  | .snd pairTerm => .snd pairTerm.toTerm
  | .boolTrue => .boolTrue
  | .boolFalse => .boolFalse
  | .boolElim scrutinee thenBranch elseBranch =>
      .boolElim scrutinee.toTerm thenBranch.toTerm elseBranch.toTerm
  | .natZero => .natZero
  | .natSucc predecessor => .natSucc predecessor.toTerm
  | .natElim scrutinee zeroBranch succBranch =>
      .natElim scrutinee.toTerm zeroBranch.toTerm succBranch.toTerm
  | .natRec scrutinee zeroBranch succBranch =>
      .natRec scrutinee.toTerm zeroBranch.toTerm succBranch.toTerm
  | .listNil => .listNil
  | .listCons headTerm tailTerm =>
      .listCons headTerm.toTerm tailTerm.toTerm
  | .listElim scrutinee nilBranch consBranch =>
      .listElim scrutinee.toTerm nilBranch.toTerm consBranch.toTerm
  | .optionNone => .optionNone
  | .optionSome valueTerm => .optionSome valueTerm.toTerm
  | .optionMatch scrutinee noneBranch someBranch =>
      .optionMatch scrutinee.toTerm noneBranch.toTerm someBranch.toTerm
  | .eitherInl valueTerm => .eitherInl valueTerm.toTerm
  | .eitherInr valueTerm => .eitherInr valueTerm.toTerm
  | .eitherMatch scrutinee leftBranch rightBranch =>
      .eitherMatch scrutinee.toTerm leftBranch.toTerm rightBranch.toTerm
  | .refl carrier rawWitness => .refl carrier rawWitness.toRawTerm
  | .idJ baseCase witness =>
      .idJ baseCase.toTerm witness.toTerm
  | .oeqRefl carrier rawWitness => .oeqRefl carrier rawWitness.toRawTerm
  | .oeqJ baseCase witness =>
      .oeqJ baseCase.toTerm witness.toTerm
  | .oeqFunext domainType codomainType leftFunctionRaw rightFunctionRaw
      pointwiseProof =>
      .oeqFunext domainType codomainType leftFunctionRaw rightFunctionRaw
        pointwiseProof.toTerm
  | .idStrictRefl modeIsStrict carrier rawWitness =>
      .idStrictRefl modeIsStrict carrier rawWitness.toRawTerm
  | .idStrictRec modeIsStrict baseCase witness =>
      .idStrictRec modeIsStrict baseCase.toTerm witness.toTerm
  | .modIntro innerTerm => .modIntro innerTerm.toTerm
  | .modElim innerTerm => .modElim innerTerm.toTerm
  | .subsume innerTerm => .subsume innerTerm.toTerm
  | .interval0 => .interval0
  | .interval1 => .interval1
  | .intervalOpp innerValue => .intervalOpp innerValue.toTerm
  | .intervalMeet leftValue rightValue =>
      .intervalMeet leftValue.toTerm rightValue.toTerm
  | .intervalJoin leftValue rightValue =>
      .intervalJoin leftValue.toTerm rightValue.toTerm
  | .pathLam modeIsUnivalent carrierType leftEndpoint rightEndpoint body =>
      .pathLam modeIsUnivalent carrierType leftEndpoint rightEndpoint
        body.toTerm
  | .pathApp modeIsUnivalent pathTerm intervalTerm =>
      .pathApp modeIsUnivalent pathTerm.toTerm intervalTerm.toTerm
  | .glueIntro modeIsUnivalent baseType boundaryWitness
      baseValue partialValue =>
      .glueIntro modeIsUnivalent baseType boundaryWitness
        baseValue.toTerm partialValue.toTerm
  | .glueElim modeIsUnivalent gluedValue =>
      .glueElim modeIsUnivalent gluedValue.toTerm
  | .transp modeIsUnivalent universeLevel universeLevelLt
      sourceType targetType sourceTypeRaw targetTypeRaw
      typePath sourceValue =>
      .transp modeIsUnivalent universeLevel universeLevelLt
        sourceType targetType sourceTypeRaw targetTypeRaw
        typePath.toTerm sourceValue.toTerm
  | .hcomp modeIsUnivalent sidesValue capValue =>
      .hcomp modeIsUnivalent sidesValue.toTerm capValue.toTerm
  | .hcompPath modeIsUnivalent leftEndpoint rightEndpoint
      sidesPath capValue =>
      .hcompPath modeIsUnivalent leftEndpoint rightEndpoint
        sidesPath.toTerm capValue.toTerm
  | .recordIntro firstField => .recordIntro firstField.toTerm
  | .recordProj recordValue => .recordProj recordValue.toTerm
  | .refineIntro predicate baseValue predicateProof =>
      .refineIntro predicate baseValue.toTerm predicateProof.toTerm
  | .refineElim refinedValue => .refineElim refinedValue.toTerm
  | .codataUnfold initialState transition =>
      .codataUnfold initialState.toTerm transition.toTerm
  | .codataDest codataValue => .codataDest codataValue.toTerm
  | .sessionSend protocolStep channel payload =>
      .sessionSend protocolStep channel.toTerm payload.toTerm
  | .sessionRecv channel => .sessionRecv channel.toTerm
  | .effectPerform effectTag effectRow operationSignature
      canPerformOperation operationTag arguments =>
      .effectPerform effectTag effectRow operationSignature
        canPerformOperation operationTag.toTerm arguments.toTerm
  | .universeCode innerLevel outerLevel cumulOk levelLe =>
      .universeCode innerLevel outerLevel cumulOk levelLe
  | .cumulUp lowerLevel higherLevel cumulMonotone levelLeLow
      levelLeHigh typeCode =>
      .cumulUp lowerLevel higherLevel cumulMonotone levelLeLow
        levelLeHigh typeCode.toTerm
  | .equivReflId carrier => .equivReflId carrier
  | .funextRefl domainType codomainType applyPolyRaw =>
      .funextRefl domainType codomainType applyPolyRaw.toRawTerm
  | .equivReflIdAtId innerLevel innerLevelLt carrier carrierRaw =>
      .equivReflIdAtId innerLevel innerLevelLt carrier carrierRaw
  | .funextReflAtId domainType codomainType applyPolyRaw =>
      .funextReflAtId domainType codomainType applyPolyRaw.toRawTerm
  | .equivIntroHet forward backward leftInv rightInv =>
      .equivIntroHet forward.toTerm backward.toTerm leftInv.toTerm
        rightInv.toTerm
  | .equivApp equivTerm argument =>
      .equivApp equivTerm.toTerm argument.toTerm
  | .uaIntroHet innerLevel innerLevelLt carrierARaw carrierBRaw
      equivWitness =>
      .uaIntroHet innerLevel innerLevelLt carrierARaw carrierBRaw
        equivWitness.toTerm
  | .funextIntroHet domainType codomainType applyAPolyRaw applyBPolyRaw =>
      .funextIntroHet domainType codomainType
        applyAPolyRaw.toRawTerm applyBPolyRaw.toRawTerm
  | .arrowCode outerLevel levelLe domainCodePolyRaw codomainCodePolyRaw =>
      .arrowCode outerLevel levelLe
        domainCodePolyRaw.toRawTerm codomainCodePolyRaw.toRawTerm
  | .piTyCode outerLevel levelLe domainCodePolyRaw codomainCodePolyRaw =>
      .piTyCode outerLevel levelLe
        domainCodePolyRaw.toRawTerm codomainCodePolyRaw.toRawTerm
  | .sigmaTyCode outerLevel levelLe domainCodePolyRaw codomainCodePolyRaw =>
      .sigmaTyCode outerLevel levelLe
        domainCodePolyRaw.toRawTerm codomainCodePolyRaw.toRawTerm
  | .productCode outerLevel levelLe firstCodePolyRaw secondCodePolyRaw =>
      .productCode outerLevel levelLe
        firstCodePolyRaw.toRawTerm secondCodePolyRaw.toRawTerm
  | .sumCode outerLevel levelLe leftCodePolyRaw rightCodePolyRaw =>
      .sumCode outerLevel levelLe
        leftCodePolyRaw.toRawTerm rightCodePolyRaw.toRawTerm
  | .listCode outerLevel levelLe elementCodePolyRaw =>
      .listCode outerLevel levelLe elementCodePolyRaw.toRawTerm
  | .optionCode outerLevel levelLe elementCodePolyRaw =>
      .optionCode outerLevel levelLe elementCodePolyRaw.toRawTerm
  | .eitherCode outerLevel levelLe leftCodePolyRaw rightCodePolyRaw =>
      .eitherCode outerLevel levelLe
        leftCodePolyRaw.toRawTerm rightCodePolyRaw.toRawTerm
  | .idCode outerLevel levelLe typeCodePolyRaw leftPolyRaw rightPolyRaw =>
      .idCode outerLevel levelLe
        typeCodePolyRaw.toRawTerm leftPolyRaw.toRawTerm rightPolyRaw.toRawTerm
  | .equivCode outerLevel levelLe leftTypeCodePolyRaw rightTypeCodePolyRaw =>
      .equivCode outerLevel levelLe
        leftTypeCodePolyRaw.toRawTerm rightTypeCodePolyRaw.toRawTerm
  | .uaToEquiv innerLevel innerLevelLt leftTy rightTy
      leftTyRaw rightTyRaw proof =>
      .uaToEquiv innerLevel innerLevelLt leftTy rightTy
        leftTyRaw rightTyRaw proof.toTerm
  | .equivApply equivTerm argument =>
      .equivApply equivTerm.toTerm argument.toTerm

end LeanFX2
