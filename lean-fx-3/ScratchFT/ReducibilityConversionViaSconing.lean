import FX1Poly.Core.ReducibilityNormalizationViaSconing
import FX1Poly.Core.Normalize

/-! Scratch probe: decidable conversion extracted from a reducibility candidate (the metatheorem FX cares
    about most) + the full-metatheory capstone (SN + reaches-NF + decidable-Conv from one fundamental). -/

namespace FX1Poly.Core

open FX1Poly.Foundation StepStar

/-- Decidable conversion via sconing: two well-typed terms have decidable conversion (CR1 on both ⟹ both
SN ⟹ the SN-fragment decider). -/
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

/-- The semantic core: convertibility of two well-typed terms is normalize-equality. -/
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

/-- The FULL metatheory package: strong normalization, weak normalization, AND decidable conversion. -/
structure ReducibilityFullMetatheory {scope : Nat} (isWellTyped : RawTerm scope → Prop) : Type where
  stronglyNormalizing : ∀ term : RawTerm scope, isWellTyped term → IsStronglyNormalizing term
  reachesNormalForm : ∀ term : RawTerm scope, isWellTyped term → reachesStepNormalForm term
  conversionDecidable : ∀ leftTerm rightTerm : RawTerm scope,
    isWellTyped leftTerm → isWellTyped rightTerm → Decidable (Conv leftTerm rightTerm)

/-- The capstone: ONE fundamental obligation yields strong normalization, weak normalization, AND decidable
conversion — the complete decidable metatheory of the SN fragment from one reducibility candidate. -/
def reducibilityFullMetatheoryViaSconing {scope : Nat} {candidate : RawTerm scope → Prop}
    (candidateIsReducibility : IsReducibilityCandidate candidate)
    {isWellTyped : RawTerm scope → Prop}
    (fundamental : ∀ term : RawTerm scope, isWellTyped term → candidate term) :
    ReducibilityFullMetatheory isWellTyped where
  stronglyNormalizing := (reducibilityScone candidateIsReducibility fundamental).canonicity
  reachesNormalForm := (reducibilityNormalizationScone candidateIsReducibility fundamental).canonicity
  conversionDecidable := conversionDecidableViaSconing candidateIsReducibility fundamental

end FX1Poly.Core

#print axioms FX1Poly.Core.conversionDecidableViaSconing
#print axioms FX1Poly.Core.conversionIffNormalizeEqViaSconing
#print axioms FX1Poly.Core.reducibilityFullMetatheoryViaSconing
