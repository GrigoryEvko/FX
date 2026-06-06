import FX1Poly.Core.StrongNormalizationConstructors
import FX1Poly.Core.ReducibilityCandidate

/-! # FX1Poly/Core/CubicalPathAlgebraReducibility
    — cubical path-algebra (∞-groupoid) operator SN coverage, completing the cubical layer (SN-146), zero-axiom

The cubical layer's path ∞-groupoid structure ships five more operators beyond the Kan transport/composition
core (`CubicalOperatorReducibility` / `CubicalTransportReducibility`) and the eliminators
(`CubicalEliminatorReducibility`): path composition `gen_pathCompose` (two children: left/right paths), path
inversion `gen_pathInverse` (one child: the path value), left/right whiskering `gen_pathWhiskerLeft` /
`gen_pathWhiskerRight` (two children: path + whisker path), and the cubical composition `gen_compCubical` (two
children: path family + sides).  This file ships their SN coverage, COMPLETING the cubical layer's
congruence-only-stage strong-normalization coverage.

All five are congruence-only under `Step` (their groupoid/Kan computation rules await the cubical extension) and
non-neutral, so the SN candidate is the honest ceiling — exactly as for the Kan operators and eliminators.

## Contents (the load-bearing forward SN content per operator)

* `Step.from_*` — the inversions (only `cong` matches; a reduction descends to one child).
* `*_isStronglyNormalizing_of_child(ren)` — forward SN closures via the shipped one/two-child congruence
  closures.
* `*_isStronglyNormalizing_of_candidateMember(s)` — the reducibility-framing (candidate members → SN-candidate
  members).

The parent→child REFLECTIONS and biconditionals follow the established generic-lemma pattern (the SN-074
`isStronglyNormalizing_child_of_oneChildCong` per child slice, demonstrated in full for the Kan operators) and
are omitted here: the forward closure + candidate-framing is the load-bearing SN content the fundamental
theorem / canonicity machinery consumes.

## Zero-axiom verification

Inversions are `cases reduction` (only `cong`) + `cases childStep` down the (one/two)-child spine, empty tail by
`StepChildren.no_step_at_empty_spine`.  Forward closures are `isStronglyNormalizing_of_oneChildCong` /
`isStronglyNormalizing_of_twoChildCong`; candidate-framing composes them with the candidate's CR1 field.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

/-- **Inversion for `pathInverse`-rooted Step.**  One-child path inversion, congruence-only. -/
theorem Step.from_pathInverse
    {scope : Nat} {pathValue : RawTerm scope} {target : RawTerm scope}
    (reduction : Step (.mkGen .gen_pathInverse () (.childCons pathValue .childNil)) target) :
    ∃ (pathAfter : RawTerm scope),
      target = .mkGen .gen_pathInverse () (.childCons pathAfter .childNil) ∧
      Step pathValue pathAfter := by
  cases reduction with
  | cong _ _ childStep =>
      cases childStep with
      | here _ pathStep => rename_i pathAfter; exact ⟨pathAfter, rfl, pathStep⟩
      | there _ restStep => exact absurd restStep StepChildren.no_step_at_empty_spine

/-- **Inversion for `pathCompose`-rooted Step.**  Two-child path composition, congruence-only. -/
theorem Step.from_pathCompose
    {scope : Nat} {leftPath rightPath : RawTerm scope} {target : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_pathCompose () (.childCons leftPath (.childCons rightPath .childNil))) target) :
    (∃ (leftAfter : RawTerm scope),
        target = .mkGen .gen_pathCompose () (.childCons leftAfter (.childCons rightPath .childNil)) ∧
        Step leftPath leftAfter)
    ∨ (∃ (rightAfter : RawTerm scope),
        target = .mkGen .gen_pathCompose () (.childCons leftPath (.childCons rightAfter .childNil)) ∧
        Step rightPath rightAfter) := by
  cases reduction with
  | cong _ _ childStep =>
      cases childStep with
      | here _ leftStep => rename_i leftAfter; exact Or.inl ⟨leftAfter, rfl, leftStep⟩
      | there _ tailStep =>
          cases tailStep with
          | here _ rightStep => rename_i rightAfter; exact Or.inr ⟨rightAfter, rfl, rightStep⟩
          | there _ restStep => exact absurd restStep StepChildren.no_step_at_empty_spine

/-- **Inversion for `pathWhiskerLeft`-rooted Step.**  Two-child left-whiskering, congruence-only. -/
theorem Step.from_pathWhiskerLeft
    {scope : Nat} {pathValue whiskerPath : RawTerm scope} {target : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_pathWhiskerLeft ()
              (.childCons pathValue (.childCons whiskerPath .childNil))) target) :
    (∃ (pathAfter : RawTerm scope),
        target = .mkGen .gen_pathWhiskerLeft ()
          (.childCons pathAfter (.childCons whiskerPath .childNil)) ∧
        Step pathValue pathAfter)
    ∨ (∃ (whiskerAfter : RawTerm scope),
        target = .mkGen .gen_pathWhiskerLeft ()
          (.childCons pathValue (.childCons whiskerAfter .childNil)) ∧
        Step whiskerPath whiskerAfter) := by
  cases reduction with
  | cong _ _ childStep =>
      cases childStep with
      | here _ pathStep => rename_i pathAfter; exact Or.inl ⟨pathAfter, rfl, pathStep⟩
      | there _ tailStep =>
          cases tailStep with
          | here _ whiskerStep => rename_i whiskerAfter; exact Or.inr ⟨whiskerAfter, rfl, whiskerStep⟩
          | there _ restStep => exact absurd restStep StepChildren.no_step_at_empty_spine

/-- **Inversion for `pathWhiskerRight`-rooted Step.**  Two-child right-whiskering, congruence-only. -/
theorem Step.from_pathWhiskerRight
    {scope : Nat} {pathValue whiskerPath : RawTerm scope} {target : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_pathWhiskerRight ()
              (.childCons pathValue (.childCons whiskerPath .childNil))) target) :
    (∃ (pathAfter : RawTerm scope),
        target = .mkGen .gen_pathWhiskerRight ()
          (.childCons pathAfter (.childCons whiskerPath .childNil)) ∧
        Step pathValue pathAfter)
    ∨ (∃ (whiskerAfter : RawTerm scope),
        target = .mkGen .gen_pathWhiskerRight ()
          (.childCons pathValue (.childCons whiskerAfter .childNil)) ∧
        Step whiskerPath whiskerAfter) := by
  cases reduction with
  | cong _ _ childStep =>
      cases childStep with
      | here _ pathStep => rename_i pathAfter; exact Or.inl ⟨pathAfter, rfl, pathStep⟩
      | there _ tailStep =>
          cases tailStep with
          | here _ whiskerStep => rename_i whiskerAfter; exact Or.inr ⟨whiskerAfter, rfl, whiskerStep⟩
          | there _ restStep => exact absurd restStep StepChildren.no_step_at_empty_spine

/-- **Inversion for `compCubical`-rooted Step.**  Two-child cubical composition (path family + sides),
congruence-only. -/
theorem Step.from_compCubical
    {scope : Nat} {pathFamily sides : RawTerm scope} {target : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_compCubical () (.childCons pathFamily (.childCons sides .childNil))) target) :
    (∃ (familyAfter : RawTerm scope),
        target = .mkGen .gen_compCubical () (.childCons familyAfter (.childCons sides .childNil)) ∧
        Step pathFamily familyAfter)
    ∨ (∃ (sidesAfter : RawTerm scope),
        target = .mkGen .gen_compCubical () (.childCons pathFamily (.childCons sidesAfter .childNil)) ∧
        Step sides sidesAfter) := by
  cases reduction with
  | cong _ _ childStep =>
      cases childStep with
      | here _ familyStep => rename_i familyAfter; exact Or.inl ⟨familyAfter, rfl, familyStep⟩
      | there _ tailStep =>
          cases tailStep with
          | here _ sidesStep => rename_i sidesAfter; exact Or.inr ⟨sidesAfter, rfl, sidesStep⟩
          | there _ restStep => exact absurd restStep StepChildren.no_step_at_empty_spine

namespace StepStar

/-- **Path inversion is strongly normalizing when its child is.**  Via `isStronglyNormalizing_of_oneChildCong`. -/
theorem pathInverse_isStronglyNormalizing_of_child {scope : Nat} {pathValue : RawTerm scope}
    (pathTerminates : IsStronglyNormalizing pathValue) :
    IsStronglyNormalizing (.mkGen .gen_pathInverse () (.childCons pathValue .childNil) : RawTerm scope) :=
  isStronglyNormalizing_of_oneChildCong (childScope := scope) (parentScope := scope)
    (fun currentPath => (.mkGen .gen_pathInverse () (.childCons currentPath .childNil) : RawTerm scope))
    (fun parentStep => Step.from_pathInverse parentStep) pathTerminates

/-- **Path inversion sends candidate members to SN-candidate members.** -/
theorem pathInverse_isStronglyNormalizing_of_candidateMember {scope : Nat}
    {memberPredicate : RawTerm scope → Prop} (candidate : IsReducibilityCandidate memberPredicate)
    {pathValue : RawTerm scope} (member : memberPredicate pathValue) :
    IsStronglyNormalizing (.mkGen .gen_pathInverse () (.childCons pathValue .childNil) : RawTerm scope) :=
  pathInverse_isStronglyNormalizing_of_child (candidate.stronglyNormalizing member)

/-- **Path composition is strongly normalizing when both children are.**  Via
`isStronglyNormalizing_of_twoChildCong`. -/
theorem pathCompose_isStronglyNormalizing_of_children {scope : Nat} {leftPath rightPath : RawTerm scope}
    (leftTerminates : IsStronglyNormalizing leftPath) (rightTerminates : IsStronglyNormalizing rightPath) :
    IsStronglyNormalizing
      (.mkGen .gen_pathCompose () (.childCons leftPath (.childCons rightPath .childNil)) : RawTerm scope) :=
  isStronglyNormalizing_of_twoChildCong (firstScope := scope) (secondScope := scope) (parentScope := scope)
    (fun cl cr => (.mkGen .gen_pathCompose () (.childCons cl (.childCons cr .childNil)) : RawTerm scope))
    (fun parentStep => Step.from_pathCompose parentStep) leftTerminates rightTerminates

/-- **Path composition sends candidate members to SN-candidate members.** -/
theorem pathCompose_isStronglyNormalizing_of_candidateMembers {scope : Nat}
    {leftPredicate rightPredicate : RawTerm scope → Prop}
    (leftCandidate : IsReducibilityCandidate leftPredicate)
    (rightCandidate : IsReducibilityCandidate rightPredicate)
    {leftPath rightPath : RawTerm scope} (leftMember : leftPredicate leftPath)
    (rightMember : rightPredicate rightPath) :
    IsStronglyNormalizing
      (.mkGen .gen_pathCompose () (.childCons leftPath (.childCons rightPath .childNil)) : RawTerm scope) :=
  pathCompose_isStronglyNormalizing_of_children
    (leftCandidate.stronglyNormalizing leftMember) (rightCandidate.stronglyNormalizing rightMember)

/-- **Left whiskering is strongly normalizing when both children are.** -/
theorem pathWhiskerLeft_isStronglyNormalizing_of_children {scope : Nat}
    {pathValue whiskerPath : RawTerm scope}
    (pathTerminates : IsStronglyNormalizing pathValue)
    (whiskerTerminates : IsStronglyNormalizing whiskerPath) :
    IsStronglyNormalizing
      (.mkGen .gen_pathWhiskerLeft ()
        (.childCons pathValue (.childCons whiskerPath .childNil)) : RawTerm scope) :=
  isStronglyNormalizing_of_twoChildCong (firstScope := scope) (secondScope := scope) (parentScope := scope)
    (fun cp cw => (.mkGen .gen_pathWhiskerLeft () (.childCons cp (.childCons cw .childNil)) : RawTerm scope))
    (fun parentStep => Step.from_pathWhiskerLeft parentStep) pathTerminates whiskerTerminates

/-- **Left whiskering sends candidate members to SN-candidate members.** -/
theorem pathWhiskerLeft_isStronglyNormalizing_of_candidateMembers {scope : Nat}
    {pathPredicate whiskerPredicate : RawTerm scope → Prop}
    (pathCandidate : IsReducibilityCandidate pathPredicate)
    (whiskerCandidate : IsReducibilityCandidate whiskerPredicate)
    {pathValue whiskerPath : RawTerm scope} (pathMember : pathPredicate pathValue)
    (whiskerMember : whiskerPredicate whiskerPath) :
    IsStronglyNormalizing
      (.mkGen .gen_pathWhiskerLeft ()
        (.childCons pathValue (.childCons whiskerPath .childNil)) : RawTerm scope) :=
  pathWhiskerLeft_isStronglyNormalizing_of_children
    (pathCandidate.stronglyNormalizing pathMember) (whiskerCandidate.stronglyNormalizing whiskerMember)

/-- **Right whiskering is strongly normalizing when both children are.** -/
theorem pathWhiskerRight_isStronglyNormalizing_of_children {scope : Nat}
    {pathValue whiskerPath : RawTerm scope}
    (pathTerminates : IsStronglyNormalizing pathValue)
    (whiskerTerminates : IsStronglyNormalizing whiskerPath) :
    IsStronglyNormalizing
      (.mkGen .gen_pathWhiskerRight ()
        (.childCons pathValue (.childCons whiskerPath .childNil)) : RawTerm scope) :=
  isStronglyNormalizing_of_twoChildCong (firstScope := scope) (secondScope := scope) (parentScope := scope)
    (fun cp cw => (.mkGen .gen_pathWhiskerRight () (.childCons cp (.childCons cw .childNil)) : RawTerm scope))
    (fun parentStep => Step.from_pathWhiskerRight parentStep) pathTerminates whiskerTerminates

/-- **Right whiskering sends candidate members to SN-candidate members.** -/
theorem pathWhiskerRight_isStronglyNormalizing_of_candidateMembers {scope : Nat}
    {pathPredicate whiskerPredicate : RawTerm scope → Prop}
    (pathCandidate : IsReducibilityCandidate pathPredicate)
    (whiskerCandidate : IsReducibilityCandidate whiskerPredicate)
    {pathValue whiskerPath : RawTerm scope} (pathMember : pathPredicate pathValue)
    (whiskerMember : whiskerPredicate whiskerPath) :
    IsStronglyNormalizing
      (.mkGen .gen_pathWhiskerRight ()
        (.childCons pathValue (.childCons whiskerPath .childNil)) : RawTerm scope) :=
  pathWhiskerRight_isStronglyNormalizing_of_children
    (pathCandidate.stronglyNormalizing pathMember) (whiskerCandidate.stronglyNormalizing whiskerMember)

/-- **Cubical composition is strongly normalizing when both children are.** -/
theorem compCubical_isStronglyNormalizing_of_children {scope : Nat} {pathFamily sides : RawTerm scope}
    (familyTerminates : IsStronglyNormalizing pathFamily) (sidesTerminates : IsStronglyNormalizing sides) :
    IsStronglyNormalizing
      (.mkGen .gen_compCubical () (.childCons pathFamily (.childCons sides .childNil)) : RawTerm scope) :=
  isStronglyNormalizing_of_twoChildCong (firstScope := scope) (secondScope := scope) (parentScope := scope)
    (fun cf cs => (.mkGen .gen_compCubical () (.childCons cf (.childCons cs .childNil)) : RawTerm scope))
    (fun parentStep => Step.from_compCubical parentStep) familyTerminates sidesTerminates

/-- **Cubical composition sends candidate members to SN-candidate members.**  Completes the cubical layer's
congruence-only SN coverage. -/
theorem compCubical_isStronglyNormalizing_of_candidateMembers {scope : Nat}
    {familyPredicate sidesPredicate : RawTerm scope → Prop}
    (familyCandidate : IsReducibilityCandidate familyPredicate)
    (sidesCandidate : IsReducibilityCandidate sidesPredicate)
    {pathFamily sides : RawTerm scope} (familyMember : familyPredicate pathFamily)
    (sidesMember : sidesPredicate sides) :
    IsStronglyNormalizing
      (.mkGen .gen_compCubical () (.childCons pathFamily (.childCons sides .childNil)) : RawTerm scope) :=
  compCubical_isStronglyNormalizing_of_children
    (familyCandidate.stronglyNormalizing familyMember) (sidesCandidate.stronglyNormalizing sidesMember)

end StepStar
end FX1Poly.Core
