import FX1Poly.Modal.GradedEvaluation

/-! Probe: the VERIFIED NORMALIZER maps closed well-typed terms to λ-values, in every dimension,
plus typed evaluation determinism (convertible closed well-typed terms normalize to the SAME value). -/

namespace FX1Poly.Modal

open FX1Poly.Core (Joinable)

/-- The verified normalizer COMPUTES a `.lam` value for every closed well-typed term: `normalize` of a
closed `HasGradeOver R` term is a `.lam`.  (Firing-108 `closedReducesToLam` gave "SOME reduction reaches
a λ"; this characterizes the actual computed normal form of the executable `normalize` function.) -/
theorem closedNormalizesToLam {R : OrderedGradeSemiring} (lawful : IsLawfulOrderedGradeSemiring R)
    {grades : GradeVectorOver R} {term : GradedLambda} {resultType : GTypeOver R}
    (typed : HasGradeOver R [] grades term resultType)
    (sn : GradedLambda.IsStronglyNormalizing term) :
    ∃ body, GradedLambda.normalize term sn = .lam body := by
  have reachedStar := GradedLambda.normalize_reducesStar term sn
  have resultNormal : GradedLambda.IsNormalForm (GradedLambda.normalize term sn) :=
    GradedLambda.normalize_isNormalForm term sn
  have resultTyped := hasGradeOver_reducesStarPreservation lawful reachedStar typed
  exact closedNormalFormIsLam (GradedLambda.normalize term sn) resultTyped resultNormal

/-- Typed evaluation determinism: a closed well-typed term and any SN term CONVERTIBLE to it normalize
to the SAME `.lam` value.  Only ONE side needs typing — the value-ness propagates through
convertibility: `closedNormalizesToLam` makes the left a λ, and `joinable_iff_normalize_eq` (convertible
SN terms have equal normal forms) carries it to the right. -/
theorem closedConvertibleSameValue {R : OrderedGradeSemiring} (lawful : IsLawfulOrderedGradeSemiring R)
    {gradesLeft : GradeVectorOver R} {termLeft termRight : GradedLambda} {typeLeft : GTypeOver R}
    (typedLeft : HasGradeOver R [] gradesLeft termLeft typeLeft)
    (snLeft : GradedLambda.IsStronglyNormalizing termLeft)
    (snRight : GradedLambda.IsStronglyNormalizing termRight)
    (convertible : Joinable GradedLambda.Reduces termLeft termRight) :
    ∃ body, GradedLambda.normalize termLeft snLeft = .lam body ∧
      GradedLambda.normalize termRight snRight = .lam body := by
  obtain ⟨body, leftEq⟩ := closedNormalizesToLam lawful typedLeft snLeft
  refine ⟨body, leftEq, ?_⟩
  rw [← (GradedLambda.joinable_iff_normalize_eq snLeft snRight).mp convertible]
  exact leftEq

/-- Usage-dimension smoke: the normalizer evaluates the linear identity to a `.lam`. -/
theorem usageClosedNormalizesToLam :
    ∃ body, GradedLambda.normalize (.lam (.var 0))
      (linearIdentityOver_stronglyNormalizing fxUsageSemiring) = .lam body :=
  closedNormalizesToLam fxUsageSemiring_isLawful usageLinearIdentity_typedViaGeneric
    (linearIdentityOver_stronglyNormalizing fxUsageSemiring)

/-- Security-dimension smoke: the SAME normalizer evaluates the (security-typed) linear identity to a
`.lam` — the orthogonal-composition thesis at the evaluation layer (no per-dimension proof). -/
theorem securityClosedNormalizesToLam :
    ∃ body, GradedLambda.normalize (.lam (.var 0))
      (linearIdentityOver_stronglyNormalizing fxSecuritySemiring) = .lam body :=
  closedNormalizesToLam fxSecuritySemiring_isLawful securityLinearIdentity_typedViaGeneric
    (linearIdentityOver_stronglyNormalizing fxSecuritySemiring)

end FX1Poly.Modal

#print axioms FX1Poly.Modal.closedNormalizesToLam
#print axioms FX1Poly.Modal.closedConvertibleSameValue
#print axioms FX1Poly.Modal.usageClosedNormalizesToLam
#print axioms FX1Poly.Modal.securityClosedNormalizesToLam
