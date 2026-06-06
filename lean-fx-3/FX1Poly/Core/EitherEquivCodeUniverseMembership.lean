import FX1Poly.Core.StratifiedReducibleUniverseDecode
import FX1Poly.Core.StrongNormalizationConstructors

/-! # FX1Poly/Core/EitherEquivCodeUniverseMembership
    — either / equiv type codes are reducible members of their universe

`ListOptionIdCodeUniverseMembership` placed the one- and three-child data formers (`listCode`, `optionCode`,
`idCode`) in their universe at the STRATIFIED layer (`IsReducibleMemberAt (predLevel+1)` over a concrete
`gen_universeCode` classifier, the `dataFormerInUniverse` route used by the batch-1 `sigmaFormer`).  This file
finishes the universe-code family with the two remaining TWO-child formers — `eitherCode` (sum/either type
code) and `equivCode` (equivalence type code) — at that same stratified layer.

Both the `Step` inversions (`Step.from_eitherCode` / `Step.from_equivCode`, `StepInversion`) and the two-child
strong-normalization combinators (`eitherCode_isStronglyNormalizing_of_left_right` /
`equivCode_isStronglyNormalizing_of_source_target`, `StrongNormalizationConstructors`) are already shipped, so
this file is just the two `dataFormerInUniverse` instances — the stratified membership statement for the
two-child formers.  (The NON-indexed neutral-classifier form `IsReducibleMember.eitherFormerInNeutralUniverse` /
`equivFormerInNeutralUniverse` is the separate `ReducibleMemberNeutral` layer; this is the fuel-indexed
concrete-`gen_universeCode` twin.)

With this the entire universe-code-family stratified reducible-membership (arrow/product/sum +
list/option/either/id/equiv) is closed, fundamental-independent.

## Zero-axiom verification

Each is a single `dataFormerInUniverse` application fed the shipped two-child SN combinator, the uniform
weak-head-normal `cases iotaStep` (a type former has no root redex — only `rootIota` could unify), and two
`nomatch` root-distinctness proofs.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega` (verified by `#print axioms` in scratch before landing).  Per-declaration gated in
`FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation FX1Poly.Universe StepStar

/-- **`eitherCode leftCode rightCode` is a reducible member of its universe** when both summand codes are
strongly normalizing — a direct `dataFormerInUniverse` instance on the shipped two-child SN combinator
`eitherCode_isStronglyNormalizing_of_left_right`.  Stratified layer. -/
theorem eitherCode_isReducibleMemberOfUniverse {scope : Nat} {predLevel : Nat}
    (levelExpr : LevelExpr) (flag : UniverseFlag) {leftCode rightCode : RawTerm scope}
    (leftNormalizing : IsStronglyNormalizing leftCode)
    (rightNormalizing : IsStronglyNormalizing rightCode) :
    IsReducibleMemberAt (predLevel + 1)
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
      (.mkGen .gen_eitherCode () (.childCons leftCode (.childCons rightCode .childNil))) :=
  IsReducibleMemberAt.dataFormerInUniverse levelExpr flag
    (eitherCode_isStronglyNormalizing_of_left_right leftNormalizing rightNormalizing)
    (fun _reduct weakHeadStep => by cases weakHeadStep with | rootIota iotaStep => cases iotaStep)
    (fun rootEquation => nomatch rootEquation)
    (fun rootEquation => nomatch rootEquation)

/-- **`equivCode sourceType targetType` is a reducible member of its universe** when both endpoint types are
strongly normalizing — a direct `dataFormerInUniverse` instance on the shipped two-child SN combinator
`equivCode_isStronglyNormalizing_of_source_target`.  Completes the universe-code family at the
stratified layer. -/
theorem equivCode_isReducibleMemberOfUniverse {scope : Nat} {predLevel : Nat}
    (levelExpr : LevelExpr) (flag : UniverseFlag) {sourceType targetType : RawTerm scope}
    (sourceNormalizing : IsStronglyNormalizing sourceType)
    (targetNormalizing : IsStronglyNormalizing targetType) :
    IsReducibleMemberAt (predLevel + 1)
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
      (.mkGen .gen_equivCode () (.childCons sourceType (.childCons targetType .childNil))) :=
  IsReducibleMemberAt.dataFormerInUniverse levelExpr flag
    (equivCode_isStronglyNormalizing_of_source_target sourceNormalizing targetNormalizing)
    (fun _reduct weakHeadStep => by cases weakHeadStep with | rootIota iotaStep => cases iotaStep)
    (fun rootEquation => nomatch rootEquation)
    (fun rootEquation => nomatch rootEquation)

end FX1Poly.Core
