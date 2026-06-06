import FX1Poly.Core.SconingWitness
import FX1Poly.Core.WeakNormalization

/-! # FX1Poly/Core/ReducibilityNormalizationViaSconing
    — the general-reducibility NORMALIZATION sconing extraction (logical-predicate level)

`SconingWitness.lean` ships `reducibilityScone`: a reducibility candidate is a sconing witness for the
STRONG-NORMALIZATION canonicity statement (CR1 discharges extraction).  `DataMetatheoryViaSconing.lean`
bundles SN + reduces-to-a-value for the DATA axis (scope-0 `CanonicalFormsPredicate`).  Neither
delivers the genuine NORMALIZATION metatheorem — that a well-typed term REACHES A STRUCTURAL NORMAL FORM
(weak normalization), the second leg of the BKS "sconing is enough" thesis (FSCD 2023, §3.0.2 of polycell.md).

This file adds it, at the GENERAL reducibility-candidate level (any `IsReducibilityCandidate`, any scope —
not just the data axis): the SECOND concrete sconing witness, parallel to `reducibilityScone`, whose
extraction target is the weak-normalization predicate `reachesStepNormalForm`.  The extraction composes CR1
(candidate membership ⟹ strong normalization) with `exists_normalForm_of_isStronglyNormalizing`
(strong normalization ⟹ reaches a structural normal form, `WeakNormalization.lean`).  Both legs are
zero-axiom and fundamental-free; the only hard obligation is the shared `fundamental` (the fundamental theorem of
the logical relation).

So the SAME `(candidateIsReducibility, fundamental)` pair now discharges BOTH metatheorems — strong
normalization (`reducibilityScone`) AND weak normalization (`reducibilityNormalizationScone`) — each through
the one boilerplate-free `SconingWitness.canonicity` composition.  That is the "one fundamental ⟹ many
metatheorems" content of the sconing-is-enough thesis, realized at the general reducibility level
where `DataMetatheoryViaSconing` realizes the data-axis SN+canonicity slice.

## What lands here (all zero-axiom)

  * `reachesStepNormalForm` — the weak-normalization predicate: a term reaches a structural normal form.
  * `reducibilityNormalizationScone` — the normalization sconing witness (the general-reducibility
    NormalizationExtraction at the logical-predicate level).
  * `normalizationViaSconing` — its `canonicity`: every well-typed term reaches a structural normal form.
  * `ReducibilityMetatheory` / `reducibilityMetatheoryViaSconing` — the bundle: ONE fundamental obligation
    yields BOTH strong normalization AND weak normalization, the general-reducibility "sconing is enough"
    demonstration, strictly beyond the data-axis bundle's SN-only (`DataMetatheory`).

## Honest scope boundary

This is the LOGICAL-PREDICATE bundling, parametric in the `fundamental` obligation (the fundamental theorem
of the logical relation — discharged on the proven fragments).  It does
NOT flip the Tier-0 `SconingConstructionLevel.hasNormalizationTransferTheorem` ledger flag: that tracks the
CATEGORICAL `NormalizationExtraction` over `fxBaseRMC`, a different and unshipped obligation.

## Zero-axiom verification

Two record literals over `SconingWitness` and one structure literal, whose extraction fields compose
`IsReducibilityCandidate.stronglyNormalizing` (CR1) with `exists_normalForm_of_isStronglyNormalizing` (weak
normalization).  No induction, no `funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation StepStar

/-- **The weak-normalization predicate.**  A term `reachesStepNormalForm` when it `StepStar`-reduces to a
structural normal form — the extraction target of the normalization sconing witness. -/
def reachesStepNormalForm {scope : Nat} (term : RawTerm scope) : Prop :=
  ∃ normalForm : RawTerm scope, StepStar term normalForm ∧ RawTerm.isStepNormalForm normalForm

/-- **The general-reducibility normalization sconing witness.**  A reducibility candidate, sconed against
the weak-normalization predicate: the displayed computability is candidate membership (the same scone as
`reducibilityScone`), the fundamental obligation is the shared hypothesis, and the extraction composes CR1
(candidate ⟹ strong normalization) with `exists_normalForm_of_isStronglyNormalizing` (strong normalization
⟹ reaches a structural normal form).  The logical-predicate `NormalizationExtraction` over an arbitrary
reducibility candidate. -/
def reducibilityNormalizationScone {scope : Nat} {candidate : RawTerm scope → Prop}
    (candidateIsReducibility : IsReducibilityCandidate candidate)
    {isWellTyped : RawTerm scope → Prop}
    (fundamental : ∀ term : RawTerm scope, isWellTyped term → candidate term) :
    SconingWitness isWellTyped reachesStepNormalForm where
  computable := candidate
  fundamental := fundamental
  extraction := fun _term reducible =>
    exists_normalForm_of_isStronglyNormalizing (candidateIsReducibility.stronglyNormalizing reducible)

/-- **Normalization via sconing.**  Given a reducibility candidate and the fundamental obligation, every
well-typed term reaches a structural normal form — the BKS boilerplate-free derivation
(`SconingWitness.canonicity`) instantiated at the weak-normalization predicate.  The normalization
metatheorem from the one shared fundamental. -/
theorem normalizationViaSconing {scope : Nat} {candidate : RawTerm scope → Prop}
    (candidateIsReducibility : IsReducibilityCandidate candidate)
    {isWellTyped : RawTerm scope → Prop}
    (fundamental : ∀ term : RawTerm scope, isWellTyped term → candidate term)
    (term : RawTerm scope) (typed : isWellTyped term) :
    reachesStepNormalForm term :=
  (reducibilityNormalizationScone candidateIsReducibility fundamental).canonicity term typed

/-- **The general-reducibility metatheory bundle.**  Strong normalization (every well-typed term is
strongly normalizing) AND weak normalization (every well-typed term reaches a structural normal form). -/
structure ReducibilityMetatheory {scope : Nat} (isWellTyped : RawTerm scope → Prop) : Prop where
  /-- Strong normalization: every well-typed term admits no infinite reduction. -/
  stronglyNormalizing : ∀ term : RawTerm scope, isWellTyped term → IsStronglyNormalizing term
  /-- Weak normalization: every well-typed term reaches a structural normal form. -/
  reachesNormalForm : ∀ term : RawTerm scope, isWellTyped term → reachesStepNormalForm term

/-- **The "sconing is enough" demonstration at the general reducibility level.**  ONE
`(candidateIsReducibility, fundamental)` pair yields BOTH metatheorems — strong normalization via
`reducibilityScone`, weak normalization via `reducibilityNormalizationScone` — each through the single
boilerplate-free `SconingWitness.canonicity` composition.  The general-reducibility realization of "one
fundamental ⟹ many metatheorems", strictly beyond the data-axis bundle's SN-only (`DataMetatheory`). -/
def reducibilityMetatheoryViaSconing {scope : Nat} {candidate : RawTerm scope → Prop}
    (candidateIsReducibility : IsReducibilityCandidate candidate)
    {isWellTyped : RawTerm scope → Prop}
    (fundamental : ∀ term : RawTerm scope, isWellTyped term → candidate term) :
    ReducibilityMetatheory isWellTyped where
  stronglyNormalizing := (reducibilityScone candidateIsReducibility fundamental).canonicity
  reachesNormalForm := (reducibilityNormalizationScone candidateIsReducibility fundamental).canonicity

end FX1Poly.Core
