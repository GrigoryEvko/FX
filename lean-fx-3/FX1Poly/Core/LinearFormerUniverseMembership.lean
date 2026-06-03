import FX1Poly.Core.StratifiedReducibleUniverseDecode
import FX1Poly.Core.StrongNormalizationLinearFormers

/-! # FX1Poly/Core/LinearFormerUniverseMembership
    — linear-logic type formers (⊸ / ⊗) are reducible members of their universe

`ListOptionIdCodeUniverseMembership` and `EitherEquivCodeUniverseMembership` placed the intuitionistic
universe-code family (arrow / product / sum / list / option / either / id / equiv) in their universe at the
stratified layer.  This file extends that coverage to the LINEAR-LOGIC type formers — `linearArrow` (the
linear function space `⊸`) and `tensorProduct` (the multiplicative conjunction `⊗`) — which are likewise
two-child `.type` formers.

Linearity is a USAGE-dimension grade, orthogonal to the type-code-inhabits-universe fact: as a raw type code,
`A ⊸ B` / `A ⊗ B` are weak-head-normal non-Π non-universe formers, so the generic
`IsReducibleMemberAt.dataFormerInUniverse` classifies them in `Type@levelExpr` by strong normalization exactly
as the intuitionistic formers.  The shipped two-child SN combinators
(`linearArrow_isStronglyNormalizing_of_source_target` / `tensorProduct_isStronglyNormalizing_of_factors`,
`StrongNormalizationLinearFormers`) supply the SN witness, so this file is just the two `dataFormerInUniverse`
instances.

The one-child `bangModality` (`!A`) is the remaining linear former; it still needs its own `Step.from_*`
inversion and one-child SN combinator before its membership can be stated the same way — deferred.

## Zero-axiom verification

Each is a single `dataFormerInUniverse` application fed the shipped two-child SN combinator, the uniform
weak-head-normal `cases iotaStep` (a type former has no root redex — only `rootIota` could unify), and two
`nomatch` root-distinctness proofs.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega` (verified by `#print axioms` in scratch before landing).  Per-declaration gated in
`FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation FX1Poly.Universe StepStar

/-- **`linearArrow source target` (`source ⊸ target`) is a reducible member of its universe** when both the
source and target codes are strongly normalizing — a direct `dataFormerInUniverse` instance on the shipped
two-child SN combinator `linearArrow_isStronglyNormalizing_of_source_target`. -/
theorem linearArrow_isReducibleMemberOfUniverse {scope : Nat} {predLevel : Nat}
    (levelExpr : LevelExpr) (flag : UniverseFlag) {source target : RawTerm scope}
    (sourceNormalizing : IsStronglyNormalizing source)
    (targetNormalizing : IsStronglyNormalizing target) :
    IsReducibleMemberAt (predLevel + 1)
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
      (.mkGen .gen_linearArrow () (.childCons source (.childCons target .childNil))) :=
  IsReducibleMemberAt.dataFormerInUniverse levelExpr flag
    (linearArrow_isStronglyNormalizing_of_source_target sourceNormalizing targetNormalizing)
    (fun _reduct weakHeadStep => by cases weakHeadStep with | rootIota iotaStep => cases iotaStep)
    (fun rootEquation => nomatch rootEquation)
    (fun rootEquation => nomatch rootEquation)

/-- **`tensorProduct leftFactor rightFactor` (`leftFactor ⊗ rightFactor`) is a reducible member of its
universe** when both factor codes are strongly normalizing — a direct `dataFormerInUniverse` instance on the
shipped two-child SN combinator `tensorProduct_isStronglyNormalizing_of_factors`. -/
theorem tensorProduct_isReducibleMemberOfUniverse {scope : Nat} {predLevel : Nat}
    (levelExpr : LevelExpr) (flag : UniverseFlag) {leftFactor rightFactor : RawTerm scope}
    (leftNormalizing : IsStronglyNormalizing leftFactor)
    (rightNormalizing : IsStronglyNormalizing rightFactor) :
    IsReducibleMemberAt (predLevel + 1)
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
      (.mkGen .gen_tensorProduct () (.childCons leftFactor (.childCons rightFactor .childNil))) :=
  IsReducibleMemberAt.dataFormerInUniverse levelExpr flag
    (tensorProduct_isStronglyNormalizing_of_factors leftNormalizing rightNormalizing)
    (fun _reduct weakHeadStep => by cases weakHeadStep with | rootIota iotaStep => cases iotaStep)
    (fun rootEquation => nomatch rootEquation)
    (fun rootEquation => nomatch rootEquation)

end FX1Poly.Core
