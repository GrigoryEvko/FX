import FX1Poly.Core.ReducibilityNormalizationViaSconing
import FX1Poly.Core.Normalize

/-! # FX1Poly/Core/ReducibilityConversionViaSconing
    — decidable conversion from a reducibility candidate + the full-metatheory capstone (the decidability FX
      wants most, derived from one fundamental)

`ReducibilityNormalizationViaSconing.lean` extracts strong normalization (`reducibilityScone`) and weak
normalization (`reducibilityNormalizationScone`) from a reducibility candidate.  The metatheorem FX itself
cares about most — the Milestone-A core — is DECIDABLE CONVERSION, and it is the next free extraction from the
same candidate: CR1 makes both sides strongly normalizing, and `Conv.decidableOfStronglyNormalizing`
(`Normalize.lean`) decides conversion on the strongly-normalizing fragment by normalizing each side and
comparing — no global confluence needed (each SN witness discharges its own).

So the SAME `(candidateIsReducibility, fundamental)` pair that gives SN and weak normalization ALSO gives
decidable conversion.  This file ships that extraction and bundles all three into the full decidable
metatheory package — the general-reducibility capstone of "one fundamental ⟹ the complete decidable
metatheory of the SN fragment".

## What lands here (all zero-axiom)

  * `conversionDecidableViaSconing` — decidable conversion of two well-typed terms (CR1 on both ⟹ both SN ⟹
    the SN-fragment decider).  The decidability extraction from the candidate.
  * `conversionIffNormalizeEqViaSconing` — the semantic NbE characterization: convertibility of two well-typed
    terms IS equality of their normal forms (`RawTerm.normalize`).  The core `conversionDecidableViaSconing`
    decides.
  * `ReducibilityFullMetatheory` / `reducibilityFullMetatheoryViaSconing` — the full package: strong
    normalization AND weak normalization AND decidable conversion, all from one fundamental obligation.
    `Type`-valued (decidable conversion is decision DATA) — the decidable-metatheory capstone, extending the
    `Prop`-valued `ReducibilityMetatheory` (SN + weak normalization) with the decision procedure.

## Honest scope boundary

Parametric in the `fundamental` obligation (the fundamental theorem of the logical relation —
discharged on the proven fragments).  This is the LOGICAL-PREDICATE capstone; it does not
construct the categorical decision procedure over `fxBaseRMC`.  It is also NOT the BKS parametricity leg
(genuine parametricity needs a BINARY logical relation, a separate construction the unary candidate cannot
supply); decidable conversion is a distinct, derived metatheorem (normalization + per-term confluence) that
the unary candidate DOES supply.

## Zero-axiom verification

`conversionDecidableViaSconing` applies `Conv.decidableOfStronglyNormalizing` to the two CR1 outputs;
`conversionIffNormalizeEqViaSconing` applies `Conv.iff_normalize_eq_of_isStronglyNormalizing`; the capstone is
a record literal over the two shipped sconing witnesses plus this decider.  No induction, no `funext`.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation StepStar

/-- **Decidable conversion via sconing.**  Two well-typed terms have decidable conversion: CR1 makes both
strongly normalizing, and `Conv.decidableOfStronglyNormalizing` decides — normalize each side, compare normal
forms.  The decidability metatheorem (the Milestone-A core) as a free extraction from the reducibility
candidate, on top of the SN and weak-normalization extractions. -/
def conversionDecidableViaSconing {scope : Nat} {candidate : RawTerm scope → Prop}
    (candidateIsReducibility : IsReducibilityCandidate candidate)
    {isWellTyped : RawTerm scope → Prop}
    (fundamental : ∀ term : RawTerm scope, isWellTyped term → candidate term)
    (leftTerm rightTerm : RawTerm scope)
    (leftTyped : isWellTyped leftTerm) (rightTyped : isWellTyped rightTerm) :
    Decidable (Conv leftTerm rightTerm) :=
  Conv.decidableOfStronglyNormalizing
    (candidateIsReducibility.stronglyNormalizing (fundamental leftTerm leftTyped))
    (candidateIsReducibility.stronglyNormalizing (fundamental rightTerm rightTyped))

/-- **The semantic core: conversion is normalize-equality.**  Two well-typed terms are convertible iff
`RawTerm.normalize` maps them to the same term — the NbE soundness+completeness characterization
`conversionDecidableViaSconing` decides over.  The normal forms ARE the normalizer's outputs at the candidate's
CR1 SN witnesses, so the right-hand side is a literal `RawTerm` equality. -/
theorem conversionIffNormalizeEqViaSconing {scope : Nat} {candidate : RawTerm scope → Prop}
    (candidateIsReducibility : IsReducibilityCandidate candidate)
    {isWellTyped : RawTerm scope → Prop}
    (fundamental : ∀ term : RawTerm scope, isWellTyped term → candidate term)
    (leftTerm rightTerm : RawTerm scope)
    (leftTyped : isWellTyped leftTerm) (rightTyped : isWellTyped rightTerm) :
    Conv leftTerm rightTerm ↔
      RawTerm.normalize leftTerm
          (candidateIsReducibility.stronglyNormalizing (fundamental leftTerm leftTyped)) =
        RawTerm.normalize rightTerm
          (candidateIsReducibility.stronglyNormalizing (fundamental rightTerm rightTyped)) :=
  Conv.iff_normalize_eq_of_isStronglyNormalizing
    (candidateIsReducibility.stronglyNormalizing (fundamental leftTerm leftTyped))
    (candidateIsReducibility.stronglyNormalizing (fundamental rightTerm rightTyped))

/-- **The full decidable-metatheory package.**  Strong normalization, weak normalization (reaches a structural
normal form), AND decidable conversion.  `Type`-valued because the conversion-decision field is decision
DATA. -/
structure ReducibilityFullMetatheory {scope : Nat} (isWellTyped : RawTerm scope → Prop) : Type where
  /-- Strong normalization: every well-typed term admits no infinite reduction. -/
  stronglyNormalizing : ∀ term : RawTerm scope, isWellTyped term → IsStronglyNormalizing term
  /-- Weak normalization: every well-typed term reaches a structural normal form. -/
  reachesNormalForm : ∀ term : RawTerm scope, isWellTyped term → reachesStepNormalForm term
  /-- Decidable conversion: conversion of two well-typed terms is decidable. -/
  conversionDecidable : ∀ leftTerm rightTerm : RawTerm scope,
    isWellTyped leftTerm → isWellTyped rightTerm → Decidable (Conv leftTerm rightTerm)

/-- **The decidable-metatheory capstone via sconing.**  ONE reducibility candidate with its fundamental
obligation yields strong normalization, weak normalization, AND decidable conversion — the complete decidable
metatheory of the SN fragment from a single logical relation.  The general-reducibility realization of "one
fundamental ⟹ the whole decidable metatheory", extending `reducibilityMetatheoryViaSconing` (SN + weak
normalization) with the decision procedure FX is ultimately after. -/
def reducibilityFullMetatheoryViaSconing {scope : Nat} {candidate : RawTerm scope → Prop}
    (candidateIsReducibility : IsReducibilityCandidate candidate)
    {isWellTyped : RawTerm scope → Prop}
    (fundamental : ∀ term : RawTerm scope, isWellTyped term → candidate term) :
    ReducibilityFullMetatheory isWellTyped where
  stronglyNormalizing := (reducibilityScone candidateIsReducibility fundamental).canonicity
  reachesNormalForm := (reducibilityNormalizationScone candidateIsReducibility fundamental).canonicity
  conversionDecidable := conversionDecidableViaSconing candidateIsReducibility fundamental

end FX1Poly.Core
