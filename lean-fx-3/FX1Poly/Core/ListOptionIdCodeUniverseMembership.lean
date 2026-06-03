import FX1Poly.Core.StratifiedReducibleUniverseDecode
import FX1Poly.Core.StrongNormalizationCodeFormers

/-! # FX1Poly/Core/ListOptionIdCodeUniverseMembership
    — list / option / id type codes are reducible members of their universe (SN-071)

The two-child data formers `arrow` / `product` / `sum` codes were already shown reducible members of
`Type@levelExpr` (`sigmaFormer_isReducibleMemberOfUniverse` et al.).  This file extends that to the remaining
shipped one- and three-child formers: `listCode`, `optionCode`, `idCode`.  Each is a direct instance of the
generic
`IsReducibleMemberAt.dataFormerInUniverse` (the `genFormationPi` data-former arm of the fundamental theorem,
semantic form) — no per-former reducibility candidate, exactly as the general dispatch will work.

The generic lemma needs, per former:
* strong normalization — supplied by the shipped per-former SN combinators
  (`listCode_isStronglyNormalizing_of_element`, `optionCode_isStronglyNormalizing_of_element`,
  `idCode_isStronglyNormalizing_of_type_endpoints` from `StrongNormalizationCodeFormers`, #719);
* weak-head-normality — a type-code former has no root redex: the only `WeakHeadStep` arm that could unify is
  `rootIota`, and no ι-redex is a type former, so `cases iotaStep` closes it (the uniform former proof);
* root-distinctness from `gen_piTyCode` and `gen_universeCode` — `Generator` `noConfusion` (`nomatch`).

The two-child `eitherCode` / `equivCode` formers are the remaining SN-071 piece: they still need their own
`Step.from_eitherCode` / `Step.from_equivCode` inversions and two-child SN combinators (the `sumTyCode` /
`sigmaTyCode` two-child template), deferred to a follow-up.

## Zero-axiom verification

Each theorem is a single `dataFormerInUniverse` application fed the per-former SN combinator, the uniform
weak-head-normal `cases iotaStep`, and two `nomatch` root-distinctness proofs.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega` (verified by `#print axioms` in scratch before landing).
Per-declaration gated in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation FX1Poly.Universe StepStar

/-- **`listCode elementCode` is a reducible member of its universe.**  The one-child list type code, with a
strongly-normalizing element code, is a reducible member of `Type@levelExpr` at `predLevel + 1` via the generic
data-former-in-universe classifier.  SN-071. -/
theorem listCode_isReducibleMemberOfUniverse {scope : Nat} {predLevel : Nat}
    (levelExpr : LevelExpr) (flag : UniverseFlag) {elementCode : RawTerm scope}
    (elementNormalizing : IsStronglyNormalizing elementCode) :
    IsReducibleMemberAt (predLevel + 1)
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
      (.mkGen .gen_listCode () (.childCons elementCode .childNil)) :=
  IsReducibleMemberAt.dataFormerInUniverse levelExpr flag
    (listCode_isStronglyNormalizing_of_element elementNormalizing)
    (fun _reduct weakHeadStep => by cases weakHeadStep with | rootIota iotaStep => cases iotaStep)
    (fun rootEquation => nomatch rootEquation)
    (fun rootEquation => nomatch rootEquation)

/-- **`optionCode elementCode` is a reducible member of its universe.**  The one-child option type code analogue
of `listCode_isReducibleMemberOfUniverse`.  SN-071. -/
theorem optionCode_isReducibleMemberOfUniverse {scope : Nat} {predLevel : Nat}
    (levelExpr : LevelExpr) (flag : UniverseFlag) {elementCode : RawTerm scope}
    (elementNormalizing : IsStronglyNormalizing elementCode) :
    IsReducibleMemberAt (predLevel + 1)
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
      (.mkGen .gen_optionCode () (.childCons elementCode .childNil)) :=
  IsReducibleMemberAt.dataFormerInUniverse levelExpr flag
    (optionCode_isStronglyNormalizing_of_element elementNormalizing)
    (fun _reduct weakHeadStep => by cases weakHeadStep with | rootIota iotaStep => cases iotaStep)
    (fun rootEquation => nomatch rootEquation)
    (fun rootEquation => nomatch rootEquation)

/-- **`idCode typeCode leftRaw rightRaw` is a reducible member of its universe.**  The three-child identity type
code, with strongly-normalizing type code and both endpoint terms, is a reducible member of `Type@levelExpr` at
`predLevel + 1`.  SN-071. -/
theorem idCode_isReducibleMemberOfUniverse {scope : Nat} {predLevel : Nat}
    (levelExpr : LevelExpr) (flag : UniverseFlag) {typeCode leftRaw rightRaw : RawTerm scope}
    (typeNormalizing : IsStronglyNormalizing typeCode)
    (leftNormalizing : IsStronglyNormalizing leftRaw)
    (rightNormalizing : IsStronglyNormalizing rightRaw) :
    IsReducibleMemberAt (predLevel + 1)
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
      (.mkGen .gen_idCode ()
        (.childCons typeCode (.childCons leftRaw (.childCons rightRaw .childNil)))) :=
  IsReducibleMemberAt.dataFormerInUniverse levelExpr flag
    (idCode_isStronglyNormalizing_of_type_endpoints typeNormalizing leftNormalizing rightNormalizing)
    (fun _reduct weakHeadStep => by cases weakHeadStep with | rootIota iotaStep => cases iotaStep)
    (fun rootEquation => nomatch rootEquation)
    (fun rootEquation => nomatch rootEquation)

end FX1Poly.Core
