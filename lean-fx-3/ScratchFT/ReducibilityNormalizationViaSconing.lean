import FX1Poly.Core.SconingWitness
import FX1Poly.Core.WeakNormalization

/-! Scratch probe: the general-reducibility NORMALIZATION sconing extraction (SN-094 / SN-110 at the
    logical-predicate level) — the second concrete sconing witness, parallel to `reducibilityScone`. -/

namespace FX1Poly.Core

open FX1Poly.Foundation StepStar

/-- The weak-normalization predicate: a term reaches a structural normal form. -/
def reachesStepNormalForm {scope : Nat} (term : RawTerm scope) : Prop :=
  ∃ normalForm : RawTerm scope, StepStar term normalForm ∧ RawTerm.isStepNormalForm normalForm

/-- The general-reducibility NORMALIZATION sconing witness: a reducibility candidate sconed against the
weak-normalization predicate. -/
def reducibilityNormalizationScone {scope : Nat} {candidate : RawTerm scope → Prop}
    (candidateIsReducibility : IsReducibilityCandidate candidate)
    {isWellTyped : RawTerm scope → Prop}
    (fundamental : ∀ term : RawTerm scope, isWellTyped term → candidate term) :
    SconingWitness isWellTyped reachesStepNormalForm where
  computable := candidate
  fundamental := fundamental
  extraction := fun _term reducible =>
    exists_normalForm_of_isStronglyNormalizing (candidateIsReducibility.stronglyNormalizing reducible)

/-- Normalization via sconing: every well-typed term reaches a structural normal form. -/
theorem normalizationViaSconing {scope : Nat} {candidate : RawTerm scope → Prop}
    (candidateIsReducibility : IsReducibilityCandidate candidate)
    {isWellTyped : RawTerm scope → Prop}
    (fundamental : ∀ term : RawTerm scope, isWellTyped term → candidate term)
    (term : RawTerm scope) (typed : isWellTyped term) :
    reachesStepNormalForm term :=
  (reducibilityNormalizationScone candidateIsReducibility fundamental).canonicity term typed

/-- The general-reducibility metatheory bundle: strong normalization AND weak normalization. -/
structure ReducibilityMetatheory {scope : Nat} (isWellTyped : RawTerm scope → Prop) : Prop where
  stronglyNormalizing : ∀ term : RawTerm scope, isWellTyped term → IsStronglyNormalizing term
  reachesNormalForm : ∀ term : RawTerm scope, isWellTyped term → reachesStepNormalForm term

/-- The "sconing is enough" demonstration at the general reducibility level: ONE fundamental obligation
yields BOTH metatheorems via the boilerplate-free `SconingWitness.canonicity`. -/
def reducibilityMetatheoryViaSconing {scope : Nat} {candidate : RawTerm scope → Prop}
    (candidateIsReducibility : IsReducibilityCandidate candidate)
    {isWellTyped : RawTerm scope → Prop}
    (fundamental : ∀ term : RawTerm scope, isWellTyped term → candidate term) :
    ReducibilityMetatheory isWellTyped where
  stronglyNormalizing := (reducibilityScone candidateIsReducibility fundamental).canonicity
  reachesNormalForm := (reducibilityNormalizationScone candidateIsReducibility fundamental).canonicity

end FX1Poly.Core

#print axioms FX1Poly.Core.reducibilityNormalizationScone
#print axioms FX1Poly.Core.normalizationViaSconing
#print axioms FX1Poly.Core.reducibilityMetatheoryViaSconing
