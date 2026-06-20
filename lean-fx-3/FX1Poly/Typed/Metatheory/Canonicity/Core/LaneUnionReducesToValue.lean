import FX1Poly.Typed.Engine.Union.HasTypeUnionCanonicalForms
import FX1Poly.Core.Metatheory.Reducibility.Candidates.DataTaitCandidate

/-! # FX1Poly/Typed/LaneUnionReducesToValue
    — the lane-GENERIC reduces-to-value form of canonicity over the single union judgment, parameterized
    on the deferred union SN/SR arc, zero-axiom

The shallow lane master `HasTypeUnion.closedNormalLaneCanonicalForms` classifies an ALREADY-normal closed
union-typed term as a head constructor value (`LaneValue target subject`) for EVERY data lane
(`IsLaneCode`: bool, nat, option, either, product, identity, pi, list).  This file lifts that head
classification across reduction at the reducibility-candidate level, uniformly in the lane — the lane-wide
twin of [[NatUnionReducesToNumeral]] (which carries the deep `IsNatNumeral` tower for the nat lane alone).

The head-expansion-closed candidate at the lane value predicate is

  `dataTaitCandidate (fun term => LaneValue target term) subject`

and membership assembles from exactly the deferred union SN/SR arc:

  * **`subjectStronglyNormalizing`** — union SN of the subject.
  * **`reachableNormalFormsTyped`** — union SR along reductions: every reachable normal form is union-typed
    at the same `classifier` and bridge-fragment-free.

plus the two lane parameters that do NOT vary along reduction (`laneTarget : IsLaneCode target` and
`classifierConvertsToLane : Conv classifier target`).  Each reachable normal form is then a head value via
`closedNormalLaneCanonicalForms`, so the subject is a candidate member; `closedReducesToValue` extracts the
reduces-to form.

## Honest scope

This is the lane-generic machine-checked REDUCTION of closed-data head canonicity to the deferred union
SN/SR arc, NOT the unconditional theorem: the two premises ARE the open arc (union SN is entirely absent
over `HasTypeUnion`; union SR is only partial — see `HasTypeUnionSubjectReduction`).  Once the arc lands,
`closedLaneReducesToValueFromNormalization` becomes premise-free across all eight lanes.  The classification
is SHALLOW (head constructor only); the nat lane additionally has the DEEP tower in
[[NatUnionReducesToNumeral]].  The `pathApp`/`pathLam` exclusion inside `reachableNormalFormsTyped` is the
honest core-`Step` fragment boundary inherited from the lane master.

## Zero-axiom

`dataTaitCandidate.closedReducesToValue` (per-term confluence over `Acc`) composed with the union shallow
lane master and a two-arm projection; `Fin 0 → False` is `Fin.elim0`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditLaneUnionReducesToValue.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

/-- **Closed lane data-candidate membership from normalization.**  Uniform in the data lane: a closed term
whose union-SN holds and whose every reachable normal form is union-typed at `classifier` is a member of
the head-expansion-closed lane candidate `dataTaitCandidate (LaneValue target ·)`.  Each reachable normal
form is classified as a head value via `closedNormalLaneCanonicalForms` (the neutral disjunct never
fires). -/
theorem HasTypeUnion.closedLaneDataCandidateFromNormalization {profile : PolyProfile}
    {subject classifier target : RawTerm 0}
    (laneTarget : IsLaneCode target)
    (classifierConvertsToLane : Conv classifier target)
    (subjectStronglyNormalizing : IsStronglyNormalizing subject)
    (reachableNormalFormsTyped :
      ∀ normalForm : RawTerm 0, StepStar subject normalForm →
        RawTerm.isStepNormalForm normalForm →
        HasTypeUnion profile (TypingContext.empty : TypingContext profile 0)
            normalForm classifier ∧
          RawTerm.containsGeneratorBool .gen_pathApp normalForm = false ∧
          RawTerm.containsGeneratorBool .gen_pathLam normalForm = false) :
    dataTaitCandidate (fun term => LaneValue target term) subject := by
  refine ⟨subjectStronglyNormalizing, ?_⟩
  intro normalForm reaches normalFormIsNormal
  obtain ⟨normalFormTyped, normalFormAppFree, normalFormLamFree⟩ :=
    reachableNormalFormsTyped normalForm reaches normalFormIsNormal
  exact Or.inl (HasTypeUnion.closedNormalLaneCanonicalForms normalFormTyped
    (fun emptyIndex => emptyIndex.elim0) normalFormIsNormal normalFormAppFree normalFormLamFree
    laneTarget classifierConvertsToLane)

/-- **★ Closed lane canonicity REDUCES-to-value over the single union judgment** (uniform in the lane).
Given union SN of the subject and along-reduction typing of its reachable normal forms, the subject reduces
to a head constructor value of its lane.  The lane-generic reduces-to form: membership
`closedLaneDataCandidateFromNormalization` fed to `dataTaitCandidate.closedReducesToValue`. -/
theorem HasTypeUnion.closedLaneReducesToValueFromNormalization {profile : PolyProfile}
    {subject classifier target : RawTerm 0}
    (laneTarget : IsLaneCode target)
    (classifierConvertsToLane : Conv classifier target)
    (subjectStronglyNormalizing : IsStronglyNormalizing subject)
    (reachableNormalFormsTyped :
      ∀ normalForm : RawTerm 0, StepStar subject normalForm →
        RawTerm.isStepNormalForm normalForm →
        HasTypeUnion profile (TypingContext.empty : TypingContext profile 0)
            normalForm classifier ∧
          RawTerm.containsGeneratorBool .gen_pathApp normalForm = false ∧
          RawTerm.containsGeneratorBool .gen_pathLam normalForm = false) :
    ∃ value : RawTerm 0, StepStar subject value ∧ LaneValue target value ∧
      RawTerm.isStepNormalForm value :=
  dataTaitCandidate.closedReducesToValue
    (HasTypeUnion.closedLaneDataCandidateFromNormalization (profile := profile)
      laneTarget classifierConvertsToLane subjectStronglyNormalizing reachableNormalFormsTyped)

end FX1Poly.Typed
