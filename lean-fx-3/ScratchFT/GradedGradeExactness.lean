import FX1Poly.Modal.GradedTypingGeneric

/-! Probe v2: GRADE EXACTNESS / HONESTY. -/

namespace FX1Poly.Modal

theorem identityBinderGradeForcedOne {R : OrderedGradeSemiring} {binderGrade : R.Carrier}
    (typed : HasGradeOver R [] GradeVectorOver.nil (.lam (.var 0))
      (.arrow binderGrade GTypeOver.base GTypeOver.base)) :
    binderGrade = R.one := by
  obtain ⟨_bg, _dom, _cod, arrowEq, bodyTyped⟩ := HasGradeOver.invertLam typed
  obtain ⟨_lookupOk, gradesEq⟩ := HasGradeOver.invertVar bodyTyped
  injection arrowEq with bgEq
  dsimp only [List.length, GradeVectorOver.single, GradeVectorOver.zero] at gradesEq
  injection gradesEq with bgOneEq
  exact bgEq.trans bgOneEq

theorem kSecondBinderGradeForcedZero {R : OrderedGradeSemiring}
    {firstBinderGrade secondBinderGrade : R.Carrier}
    (typed : HasGradeOver R [] GradeVectorOver.nil (.lam (.lam (.var 1)))
      (.arrow firstBinderGrade GTypeOver.base
        (.arrow secondBinderGrade GTypeOver.base GTypeOver.base))) :
    secondBinderGrade = R.zero := by
  obtain ⟨_outerBg, _outerDom, outerCod, outerArrowEq, innerBodyTyped⟩ := HasGradeOver.invertLam typed
  injection outerArrowEq with _outerBgEq _outerDomEq outerCodEq
  subst outerCod
  obtain ⟨_innerBg, _innerDom, _innerCod, innerArrowEq, varTyped⟩ := HasGradeOver.invertLam innerBodyTyped
  injection innerArrowEq with innerBgEq
  obtain ⟨_lookupOk, gradesEq⟩ := HasGradeOver.invertVar varTyped
  dsimp only [List.length, GradeVectorOver.single, GradeVectorOver.zero] at gradesEq
  injection gradesEq with innerZeroEq
  exact innerBgEq.trans innerZeroEq

theorem usageIdentityNotDiscardable :
    ¬ HasGradeOver fxUsageSemiring [] GradeVectorOver.nil (.lam (.var 0))
        (.arrow fxUsageSemiring.zero GTypeOver.base GTypeOver.base) := by
  intro typed
  have gradeEq : fxUsageSemiring.zero = fxUsageSemiring.one := identityBinderGradeForcedOne typed
  exact UsageGrade.noConfusion gradeEq

end FX1Poly.Modal

#print axioms FX1Poly.Modal.identityBinderGradeForcedOne
#print axioms FX1Poly.Modal.kSecondBinderGradeForcedZero
#print axioms FX1Poly.Modal.usageIdentityNotDiscardable
