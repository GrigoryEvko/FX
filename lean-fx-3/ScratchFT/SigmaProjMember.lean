import FX1Poly.Core.SigmaProjectionCanonicalComputation
import FX1Poly.Core.StrongNormalizationIotaRedexes
import FX1Poly.Core.CanonicalFormsWeakHeadExpansion

namespace FX1Poly.Core

open StepStar

theorem fstClosedIsMember_probe {isValue : RawTerm 0 → Prop} {scrutinee : RawTerm 0}
    (scrutineeMember : CanonicalFormsPredicate isPairValue scrutinee)
    (firstComponentMember : ∀ first second : RawTerm 0,
      StepStar scrutinee (pairCell first second) → CanonicalFormsPredicate isValue first) :
    CanonicalFormsPredicate isValue (.mkGen .gen_fst () (.childCons scrutinee .childNil)) := by
  have cellStronglyNormalizing :
      IsStronglyNormalizing (.mkGen .gen_fst () (.childCons scrutinee .childNil)) :=
    fst_isStronglyNormalizing_of_argument scrutineeMember.stronglyNormalizing
  obtain ⟨first, second, scrutineeToPair, fstReducesToFirst, _sndReducesToSecond⟩ :=
    pairCanonicalScrutineeProjectsToComponents scrutineeMember
  exact CanonicalFormsPredicate.ofStepStarReachingValue fstReducesToFirst
    cellStronglyNormalizing (firstComponentMember first second scrutineeToPair).closedReducesToValue

theorem sndClosedIsMember_probe {isValue : RawTerm 0 → Prop} {scrutinee : RawTerm 0}
    (scrutineeMember : CanonicalFormsPredicate isPairValue scrutinee)
    (secondComponentMember : ∀ first second : RawTerm 0,
      StepStar scrutinee (pairCell first second) → CanonicalFormsPredicate isValue second) :
    CanonicalFormsPredicate isValue (.mkGen .gen_snd () (.childCons scrutinee .childNil)) := by
  have cellStronglyNormalizing :
      IsStronglyNormalizing (.mkGen .gen_snd () (.childCons scrutinee .childNil)) :=
    snd_isStronglyNormalizing_of_argument scrutineeMember.stronglyNormalizing
  obtain ⟨first, second, scrutineeToPair, _fstReducesToFirst, sndReducesToSecond⟩ :=
    pairCanonicalScrutineeProjectsToComponents scrutineeMember
  exact CanonicalFormsPredicate.ofStepStarReachingValue sndReducesToSecond
    cellStronglyNormalizing (secondComponentMember first second scrutineeToPair).closedReducesToValue

end FX1Poly.Core

#print axioms FX1Poly.Core.fstClosedIsMember_probe
#print axioms FX1Poly.Core.sndClosedIsMember_probe
