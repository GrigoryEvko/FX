import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedFormationArityDispatch
import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeDescSubjectReduction
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationLeaves

/-! # FX1Poly/Typed/BaseTypeFormationEmptyMember
    — the emptyCode base-type formation FT member (TYTAB-4 step 4, the base-type arm's substantive case)

The first brick of the native `formationFundamental` discharge (TYTAB-4 step 4): the `baseType` sub-family's
**empty-code** case.  Under the union bundle `gen_emptyCode` carries a base-type formation row
(`fxTypingBundle.formationRule gen_emptyCode = some (.baseType …)`, output `Type@0`), so `emptyTypeCell` is a
SUBSTANTIVE type — and this lemma proves it is a bound-reducible MEMBER of `Type@0` under any closing
substitution.  It is the formation FT obligation for the very type whose uninhabitedness is the consistency
keystone of TYTAB-2-FT (#1697): the empty type must be a real, well-formed type AND uninhabited.

## Why this case sidesteps the telescope machinery

The base-type former is NULLARY: `gen_emptyCode.binderShifts = []`, so `children = .childNil` and the rule's
obligation list is `[]` (`FormationRule.obligations` on `.baseType _` is `[]`).  There are no children to
normalize and no per-obligation IHs to thread — the entire telescope / `foldChildren` / binder-crossing
apparatus the cumulative Π/Σ arm needs is absent here.  All that remains is:

  * the closing substitution is inert: `subst σ emptyTypeCell = emptyTypeCell` (`subst_emptyTypeCell`) and
    `subst σ (universeCodeCell lzero standard) = universeCodeCell lzero standard` (`subst_universeCodeCell`);
  * the cell is strongly normalizing: `gen_emptyCode` has no reducts (`Step.no_step_from_emptyCode`), so
    `isStronglyNormalizing_of_noStep` delivers SN directly;
  * the cell is reducible AS A TYPE at level `0`: the dedicated `ReducibleTypeStepBounded.dataEmpty` arm pins
    `emptyTypeCell` to `emptyTaitCandidate` (the empty type is NOT the `neutral` arm — that arm explicitly
    excludes `gen_emptyCode`);
  * the output level `lzero` denotes `0`, strictly below any positive `bound` (`boundPositive`), which the full
    arm reads off the formation level gate (`0 ≤ denote level env < bound`).

`universeMembershipIntroAtBounded` assembles these three (level bound + cell SN + reducible-as-type) into the
bound-reducible universe membership — the same intro the non-Π data formers use, here at the nullary base code.

## Zero-axiom verification

`subst` rewrites + `universeMembershipIntroAtBounded` + the `dataEmpty` reducibility arm + `noStep`-SN.  No
induction, no `funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The emptyCode base-type formation FT member (TYTAB-4 step 4).**  Under any closing substitution into
`targetScope + 1`, the substantive empty type `emptyTypeCell` is a bound-reducible member of `Type@0`
(`universeCodeCell lzero standard`), given only that the bound is positive (`0 < bound`, supplied by the
formation level gate in the full arm).  The `FundamentalConclusionAtBoundedSucc`-shaped formation obligation for
`gen_emptyCode`'s base-type row — the nullary base code sidesteps the telescope apparatus entirely.  The first
discharged case of the native `formationFundamental` premise of
`HasTypeUnionOver.fundamentalAtBoundedSuccFromTableArms`. -/
theorem fundamentalBaseTypeEmptyCodeAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope)
    (boundPositive : 0 < bound) :
    FundamentalConclusionAtBoundedSucc env bound context (emptyTypeCell (scope := scope))
      (universeCodeCell LevelExpr.lzero UniverseFlag.standard) := by
  intro targetScope substitution _envReducible
  rw [subst_universeCodeCell, subst_emptyTypeCell]
  exact universeMembershipIntroAtBounded env LevelExpr.lzero UniverseFlag.standard bound _
    boundPositive
    (StepStar.isStronglyNormalizing_of_noStep (fun _target step => Step.no_step_from_emptyCode step))
    ⟨emptyTaitCandidate, ReducibleTypeStepBounded.dataEmpty⟩

end FX1Poly.Typed
