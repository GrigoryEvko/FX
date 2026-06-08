import FX1Poly.Core.MatchClosedMembership
import FX1Poly.Core.OptionCanonicalFormsCandidate
import FX1Poly.Core.EitherCanonicalFormsCandidate
import FX1Poly.Core.BoolCanonicalFormsCandidate
import FX1Poly.Core.StrongNormalizationRedexes
import FX1Poly.Core.StrongNormalizationConstructors
import FX1Poly.Core.StrongNormalizationLeaves
import FX1Poly.Core.WeakHeadStep

namespace FX1Poly.Core
open StepStar

/-- The constant lambda `λ_. boolTrue`. -/
abbrev constLamBoolTrueCell : RawTerm 0 :=
  .mkGen .gen_lam () (.childCons boolTrueCell .childNil)

-- the β-reduction of the constant lambda applied to any argument
theorem constLamBoolTrue_app_stepStar (value : RawTerm 0) :
    StepStar (applicationCell constLamBoolTrueCell value) boolTrueCell :=
  StepStar.trans (WeakHeadStep.beta (body := boolTrueCell) (argument := value)).toStep
    (StepStar.refl _)

-- the constant branch maps every SN value to a bool-candidate member
theorem constLamBoolTrue_respectsSN :
    ∀ value : RawTerm 0, IsStronglyNormalizing value →
      CanonicalFormsPredicate (boolIsValue (scope := 0))
        (applicationCell constLamBoolTrueCell value) :=
  fun value valueSN =>
    CanonicalFormsPredicate.ofStepStarReachingValue
      (constLamBoolTrue_app_stepStar value)
      (appLamBoolTrue_isStronglyNormalizing_of_argument valueSN)
      ⟨boolTrueCell, StepStar.refl _, Or.inl rfl⟩

-- optionMatch on `none` with constant some-branch
theorem optionMatchClosedMembershipSmoke :
    CanonicalFormsPredicate (boolIsValue (scope := 0))
      (.mkGen .gen_optionMatch ()
        (.childCons optionNoneCell
          (.childCons boolTrueCell (.childCons constLamBoolTrueCell .childNil)))) :=
  optionMatchClosedIsMember
    (isOptionValue_isMember (Or.inl rfl))
    boolTrueCell_isMember
    (lam_isStronglyNormalizing_of_body boolTrue_isStronglyNormalizing)
    constLamBoolTrue_respectsSN

-- eitherMatch on `inl boolTrue` with constant left/right branches
theorem eitherMatchClosedMembershipSmoke :
    CanonicalFormsPredicate (boolIsValue (scope := 0))
      (.mkGen .gen_eitherMatch ()
        (.childCons (eitherInlCell boolTrueCell)
          (.childCons constLamBoolTrueCell (.childCons constLamBoolTrueCell .childNil)))) :=
  eitherMatchClosedIsMember
    (isEitherValue_isMember (Or.inl ⟨boolTrueCell, rfl, by decide⟩))
    (lam_isStronglyNormalizing_of_body boolTrue_isStronglyNormalizing)
    (lam_isStronglyNormalizing_of_body boolTrue_isStronglyNormalizing)
    constLamBoolTrue_respectsSN
    constLamBoolTrue_respectsSN

#print axioms optionMatchClosedMembershipSmoke
#print axioms eitherMatchClosedMembershipSmoke

end FX1Poly.Core
