import LeanFX2.Term.StrengtheningImage.TargetTotalityUniversalDelta
import LeanFX2.Tools.DependencyAudit

/-! # Smoke/AuditTargetTotalityDelta

Reviewer-facing axiom gate for the 22 atomic-constructor
`IsAggregatorTotal` arms shipped in
`Term/StrengtheningImage/TargetTotalityUniversalDelta.lean`.

Each arm proves `IsAggregatorTotal sourceTerm` for one of the atomic
(non-recursive) Term constructors — the constructors whose
target-direction wrapper in `TargetImageTotality.lean` takes NO
`∀ subValue, isSome` inductive hypothesis, so the totality predicate is
provable directly from the `IsAggregatorTotal` type-side / raw-side
premises (discharged via the `Foundation/TyStrengthenInversion.lean` and
`Foundation/RawPartialRename/IsSomeInversion.lean` inversion lemmas).

The compound constructors (`app`, `appPi`, `pair`, `listCons`, the six
eliminators, binders, and the cubical builders) are NOT covered: their
wrappers demand a sub-type strengthening side that the source type
premise cannot recover (the sub-type is not a syntactic part of the
source type — see `ImageUnweaken.lean:496-499`), so a universal
`∀ sourceTerm, IsAggregatorTotal sourceTerm` under this predicate is
architecturally impossible.  The renaming-image API
(`strengthenTyped?_rename_isSome`, already shipped) is the universal
surface that downstream Block B work consumes.

Each `#assert_no_axioms` must elaborate successfully and each
`#print axioms` must report "does not depend on any axioms" — strict
Layer K gate. -/

namespace LeanFX2.Smoke.AuditTargetTotalityDelta

-- Machine-enforced per-decl axiom gates.
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_unit
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_boolTrue
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_boolFalse
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_natZero
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_interval0
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_interval1
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_var
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_listNil
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_optionNone
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_universeCode
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_refl
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_oeqRefl
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_idStrictRefl
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_arrowCode
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_productCode
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_sumCode
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_listCode
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_optionCode
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_eitherCode
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_piTyCode
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_sigmaTyCode
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_equivCode
#assert_no_axioms LeanFX2.Term.isAggregatorTotal_idCode

-- Reviewer-facing axiom prints.
#print axioms LeanFX2.Term.isAggregatorTotal_unit
#print axioms LeanFX2.Term.isAggregatorTotal_boolTrue
#print axioms LeanFX2.Term.isAggregatorTotal_boolFalse
#print axioms LeanFX2.Term.isAggregatorTotal_natZero
#print axioms LeanFX2.Term.isAggregatorTotal_interval0
#print axioms LeanFX2.Term.isAggregatorTotal_interval1
#print axioms LeanFX2.Term.isAggregatorTotal_var
#print axioms LeanFX2.Term.isAggregatorTotal_listNil
#print axioms LeanFX2.Term.isAggregatorTotal_optionNone
#print axioms LeanFX2.Term.isAggregatorTotal_universeCode
#print axioms LeanFX2.Term.isAggregatorTotal_refl
#print axioms LeanFX2.Term.isAggregatorTotal_oeqRefl
#print axioms LeanFX2.Term.isAggregatorTotal_idStrictRefl
#print axioms LeanFX2.Term.isAggregatorTotal_arrowCode
#print axioms LeanFX2.Term.isAggregatorTotal_productCode
#print axioms LeanFX2.Term.isAggregatorTotal_sumCode
#print axioms LeanFX2.Term.isAggregatorTotal_listCode
#print axioms LeanFX2.Term.isAggregatorTotal_optionCode
#print axioms LeanFX2.Term.isAggregatorTotal_eitherCode
#print axioms LeanFX2.Term.isAggregatorTotal_piTyCode
#print axioms LeanFX2.Term.isAggregatorTotal_sigmaTyCode
#print axioms LeanFX2.Term.isAggregatorTotal_equivCode
#print axioms LeanFX2.Term.isAggregatorTotal_idCode

end LeanFX2.Smoke.AuditTargetTotalityDelta
