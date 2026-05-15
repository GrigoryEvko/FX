import LeanFX2.Reducibility.NeutralSNHott.NatRecAndOption

/-! # LeanFX2.Reducibility.NeutralSNIntro.Sums

`eitherInl` / `eitherInr` SN preservation plus the binary
`eitherMatch_eitherInl` / `eitherMatch_eitherInr` ι-witnesses
(raw + typed).  First slice of `NeutralSNIntro`.

## Root status

Layer 3 metatheory leaf.  K12.20.C ctor introduction SN preservation
for the either-sum family. -/

namespace LeanFX2




/-- **K12.20.X.1 eitherInl SN preservation**.  Sister to optionSome
helper — unary cong-only ctor at the left injection of Ty.eitherType. -/
theorem RawTerm.eitherInl_isStronglyNormalizing {scope : Nat}
    {valueTerm : RawTerm scope}
    (valueIsSN : RawTerm.isStronglyNormalizing valueTerm) :
    RawTerm.isStronglyNormalizing (RawTerm.eitherInl valueTerm) := by
  induction valueIsSN with
  | intro currentValue _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.eitherInl currentValue) ?_
    intro target progressStep
    obtain ⟨valueTarget, targetEq, valueStep⟩ :=
      RawStep.par.eitherInl_inv progressStep.1
    subst targetEq
    have valueDistinct :
        currentValue ≠ valueTarget := fun valueEq =>
      progressStep.2 (congrArg RawTerm.eitherInl valueEq)
    exact inductiveHypothesis valueTarget
      ⟨valueStep, valueDistinct⟩

/-- Either-left ι SN expansion for the eliminator.

For a canonical `inl` scrutinee, `eitherMatch` reduces to the left
branch applied to the carried value.  The right branch remains in the
statement because congruent reductions may still step under it before
the ι rule fires. -/
theorem RawTerm.eitherMatch_eitherInl_isStronglyNormalizing
    {scope : Nat}
    {valueTerm : RawTerm scope}
    (valueIsSN : RawTerm.isStronglyNormalizing valueTerm) :
    ∀ {leftBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing leftBranch →
    ∀ {rightBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing rightBranch →
      RawTerm.isStronglyNormalizing
        (RawTerm.app leftBranch valueTerm) →
      RawTerm.isStronglyNormalizing
        (RawTerm.eitherMatch
          (RawTerm.eitherInl valueTerm) leftBranch rightBranch) := by
  induction valueIsSN with
  | intro currentValue valueClosure valueIH =>
    intro leftBranch leftIsSN
    induction leftIsSN with
    | intro currentLeft leftClosure leftIH =>
      intro rightBranch rightIsSN leftAppIsSN
      induction rightIsSN with
      | intro currentRight rightClosure rightIH =>
        refine RawTerm.isStronglyNormalizing.intro
          (RawTerm.eitherMatch
            (RawTerm.eitherInl currentValue) currentLeft currentRight) ?_
        intro target progressStep
        rcases RawStep.par.eitherMatch_inv progressStep.1 with
          ⟨scrutineeTarget, leftTarget, rightTarget, targetEq,
            scrutineeStep, leftStep, rightStep⟩
          | ⟨valueTarget, leftTarget, targetEq, scrutineeStep, leftStep⟩
          | ⟨valueTarget, rightTarget, targetEq, scrutineeStep, rightStep⟩
        · obtain ⟨valueTarget, scrutineeTargetEq, valueStep⟩ :=
            RawStep.par.eitherInl_inv scrutineeStep
          subst scrutineeTargetEq
          subst targetEq
          by_cases valueEq : currentValue = valueTarget
          · subst valueEq
            by_cases leftEq : currentLeft = leftTarget
            · subst leftEq
              by_cases rightEq : currentRight = rightTarget
              · subst rightEq
                exact (progressStep.2 rfl).elim
              · exact rightIH rightTarget ⟨rightStep, rightEq⟩
            · have rightTargetIsSN :
                  RawTerm.isStronglyNormalizing rightTarget := by
                by_cases rightEq : currentRight = rightTarget
                · subst rightEq
                  exact RawTerm.isStronglyNormalizing.intro
                    currentRight rightClosure
                · exact rightClosure rightTarget ⟨rightStep, rightEq⟩
              have leftAppTargetIsSN :
                  RawTerm.isStronglyNormalizing
                    (RawTerm.app leftTarget currentValue) := by
                by_cases appEq :
                    RawTerm.app currentLeft currentValue =
                      RawTerm.app leftTarget currentValue
                · rw [← appEq]
                  exact leftAppIsSN
                · exact RawTerm.isStronglyNormalizing.step_preserves
                    leftAppIsSN
                    ⟨RawStep.par.app leftStep
                      (RawStep.par.refl currentValue), appEq⟩
              exact leftIH leftTarget ⟨leftStep, leftEq⟩
                rightTargetIsSN leftAppTargetIsSN
          · have leftTargetIsSN :
                RawTerm.isStronglyNormalizing leftTarget := by
              by_cases leftEq : currentLeft = leftTarget
              · subst leftEq
                exact RawTerm.isStronglyNormalizing.intro
                  currentLeft leftClosure
              · exact leftClosure leftTarget ⟨leftStep, leftEq⟩
            have rightTargetIsSN :
                RawTerm.isStronglyNormalizing rightTarget := by
              by_cases rightEq : currentRight = rightTarget
              · subst rightEq
                exact RawTerm.isStronglyNormalizing.intro
                  currentRight rightClosure
              · exact rightClosure rightTarget ⟨rightStep, rightEq⟩
            have leftAppTargetIsSN :
                RawTerm.isStronglyNormalizing
                  (RawTerm.app leftTarget valueTarget) := by
              by_cases appEq :
                  RawTerm.app currentLeft currentValue =
                    RawTerm.app leftTarget valueTarget
              · rw [← appEq]
                exact leftAppIsSN
              · exact RawTerm.isStronglyNormalizing.step_preserves
                  leftAppIsSN
                  ⟨RawStep.par.app leftStep valueStep, appEq⟩
            exact valueIH valueTarget ⟨valueStep, valueEq⟩
              leftTargetIsSN rightTargetIsSN leftAppTargetIsSN
        · obtain ⟨valueTargetFromScrutinee, eitherInlEq, valueStep⟩ :=
            RawStep.par.eitherInl_inv scrutineeStep
          injection eitherInlEq with _scopeEq valueTargetEq
          subst targetEq
          have valueStepToTarget :
              RawStep.par currentValue valueTarget := by
            rw [valueTargetEq]
            exact valueStep
          have leftAppTargetIsSN :
              RawTerm.isStronglyNormalizing
                (RawTerm.app leftTarget valueTarget) := by
            by_cases appEq :
                RawTerm.app currentLeft currentValue =
                  RawTerm.app leftTarget valueTarget
            · rw [← appEq]
              exact leftAppIsSN
            · exact RawTerm.isStronglyNormalizing.step_preserves
                leftAppIsSN
                ⟨RawStep.par.app leftStep valueStepToTarget, appEq⟩
          exact leftAppTargetIsSN
        · obtain ⟨valueTargetFromScrutinee, eitherInlEq, _valueStep⟩ :=
            RawStep.par.eitherInl_inv scrutineeStep
          nomatch eitherInlEq

/-- Typed either-left ι SN expansion for `Term.eitherMatch`. -/
theorem Term.eitherMatch_eitherInl_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftType rightType motiveType : Ty level scope}
    {valueRaw leftRaw rightRaw : RawTerm scope}
    {valueTerm : Term context leftType valueRaw}
    {leftBranch : Term context (Ty.arrow leftType motiveType) leftRaw}
    {rightBranch : Term context (Ty.arrow rightType motiveType) rightRaw}
    (valueIsSN : Term.isStronglyNormalizing valueTerm)
    (leftIsSN : Term.isStronglyNormalizing leftBranch)
    (rightIsSN : Term.isStronglyNormalizing rightBranch)
    (leftAppIsSN :
      Term.isStronglyNormalizing (Term.app leftBranch valueTerm)) :
    Term.isStronglyNormalizing
      (Term.eitherMatch (Term.eitherInl valueTerm) leftBranch rightBranch) :=
  RawTerm.eitherMatch_eitherInl_isStronglyNormalizing
    valueIsSN leftIsSN rightIsSN leftAppIsSN

/-- Either-right ι SN expansion for the eliminator.

For a canonical `inr` scrutinee, `eitherMatch` reduces to the right
branch applied to the carried value.  The left branch remains in the
statement because congruent reductions may still step under it before
the ι rule fires. -/
theorem RawTerm.eitherMatch_eitherInr_isStronglyNormalizing
    {scope : Nat}
    {valueTerm : RawTerm scope}
    (valueIsSN : RawTerm.isStronglyNormalizing valueTerm) :
    ∀ {leftBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing leftBranch →
    ∀ {rightBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing rightBranch →
      RawTerm.isStronglyNormalizing
        (RawTerm.app rightBranch valueTerm) →
      RawTerm.isStronglyNormalizing
        (RawTerm.eitherMatch
          (RawTerm.eitherInr valueTerm) leftBranch rightBranch) := by
  induction valueIsSN with
  | intro currentValue valueClosure valueIH =>
    intro leftBranch leftIsSN
    induction leftIsSN with
    | intro currentLeft leftClosure leftIH =>
      intro rightBranch rightIsSN rightAppIsSN
      induction rightIsSN with
      | intro currentRight rightClosure rightIH =>
        refine RawTerm.isStronglyNormalizing.intro
          (RawTerm.eitherMatch
            (RawTerm.eitherInr currentValue) currentLeft currentRight) ?_
        intro target progressStep
        rcases RawStep.par.eitherMatch_inv progressStep.1 with
          ⟨scrutineeTarget, leftTarget, rightTarget, targetEq,
            scrutineeStep, leftStep, rightStep⟩
          | ⟨valueTarget, leftTarget, targetEq, scrutineeStep, leftStep⟩
          | ⟨valueTarget, rightTarget, targetEq, scrutineeStep, rightStep⟩
        · obtain ⟨valueTarget, scrutineeTargetEq, valueStep⟩ :=
            RawStep.par.eitherInr_inv scrutineeStep
          subst scrutineeTargetEq
          subst targetEq
          by_cases valueEq : currentValue = valueTarget
          · subst valueEq
            by_cases leftEq : currentLeft = leftTarget
            · subst leftEq
              by_cases rightEq : currentRight = rightTarget
              · subst rightEq
                exact (progressStep.2 rfl).elim
              · have rightAppTargetIsSN :
                    RawTerm.isStronglyNormalizing
                      (RawTerm.app rightTarget currentValue) := by
                  by_cases appEq :
                      RawTerm.app currentRight currentValue =
                        RawTerm.app rightTarget currentValue
                  · rw [← appEq]
                    exact rightAppIsSN
                  · exact RawTerm.isStronglyNormalizing.step_preserves
                      rightAppIsSN
                      ⟨RawStep.par.app rightStep
                        (RawStep.par.refl currentValue), appEq⟩
                exact rightIH rightTarget ⟨rightStep, rightEq⟩
                  rightAppTargetIsSN
            · have rightTargetIsSN :
                  RawTerm.isStronglyNormalizing rightTarget := by
                by_cases rightEq : currentRight = rightTarget
                · subst rightEq
                  exact RawTerm.isStronglyNormalizing.intro
                    currentRight rightClosure
                · exact rightClosure rightTarget ⟨rightStep, rightEq⟩
              have rightAppTargetIsSN :
                  RawTerm.isStronglyNormalizing
                    (RawTerm.app rightTarget currentValue) := by
                by_cases appEq :
                    RawTerm.app currentRight currentValue =
                      RawTerm.app rightTarget currentValue
                · rw [← appEq]
                  exact rightAppIsSN
                · exact RawTerm.isStronglyNormalizing.step_preserves
                    rightAppIsSN
                    ⟨RawStep.par.app rightStep
                      (RawStep.par.refl currentValue), appEq⟩
              exact leftIH leftTarget ⟨leftStep, leftEq⟩
                rightTargetIsSN rightAppTargetIsSN
          · have leftTargetIsSN :
                RawTerm.isStronglyNormalizing leftTarget := by
              by_cases leftEq : currentLeft = leftTarget
              · subst leftEq
                exact RawTerm.isStronglyNormalizing.intro
                  currentLeft leftClosure
              · exact leftClosure leftTarget ⟨leftStep, leftEq⟩
            have rightTargetIsSN :
                RawTerm.isStronglyNormalizing rightTarget := by
              by_cases rightEq : currentRight = rightTarget
              · subst rightEq
                exact RawTerm.isStronglyNormalizing.intro
                  currentRight rightClosure
              · exact rightClosure rightTarget ⟨rightStep, rightEq⟩
            have rightAppTargetIsSN :
                RawTerm.isStronglyNormalizing
                  (RawTerm.app rightTarget valueTarget) := by
              by_cases appEq :
                  RawTerm.app currentRight currentValue =
                    RawTerm.app rightTarget valueTarget
              · rw [← appEq]
                exact rightAppIsSN
              · exact RawTerm.isStronglyNormalizing.step_preserves
                  rightAppIsSN
                  ⟨RawStep.par.app rightStep valueStep, appEq⟩
            exact valueIH valueTarget ⟨valueStep, valueEq⟩
              leftTargetIsSN rightTargetIsSN rightAppTargetIsSN
        · obtain ⟨valueTargetFromScrutinee, eitherInrEq, _valueStep⟩ :=
            RawStep.par.eitherInr_inv scrutineeStep
          nomatch eitherInrEq
        · obtain ⟨valueTargetFromScrutinee, eitherInrEq, valueStep⟩ :=
            RawStep.par.eitherInr_inv scrutineeStep
          injection eitherInrEq with _scopeEq valueTargetEq
          subst targetEq
          have valueStepToTarget :
              RawStep.par currentValue valueTarget := by
            rw [valueTargetEq]
            exact valueStep
          have rightAppTargetIsSN :
              RawTerm.isStronglyNormalizing
                (RawTerm.app rightTarget valueTarget) := by
            by_cases appEq :
                RawTerm.app currentRight currentValue =
                  RawTerm.app rightTarget valueTarget
            · rw [← appEq]
              exact rightAppIsSN
            · exact RawTerm.isStronglyNormalizing.step_preserves
                rightAppIsSN
                ⟨RawStep.par.app rightStep valueStepToTarget, appEq⟩
          exact rightAppTargetIsSN

/-- Typed either-right ι SN expansion for `Term.eitherMatch`. -/
theorem Term.eitherMatch_eitherInr_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftType rightType motiveType : Ty level scope}
    {valueRaw leftRaw rightRaw : RawTerm scope}
    {valueTerm : Term context rightType valueRaw}
    {leftBranch : Term context (Ty.arrow leftType motiveType) leftRaw}
    {rightBranch : Term context (Ty.arrow rightType motiveType) rightRaw}
    (valueIsSN : Term.isStronglyNormalizing valueTerm)
    (leftIsSN : Term.isStronglyNormalizing leftBranch)
    (rightIsSN : Term.isStronglyNormalizing rightBranch)
    (rightAppIsSN :
      Term.isStronglyNormalizing (Term.app rightBranch valueTerm)) :
    Term.isStronglyNormalizing
      (Term.eitherMatch
        (Term.eitherInr (leftType := leftType) valueTerm)
        leftBranch rightBranch) :=
  RawTerm.eitherMatch_eitherInr_isStronglyNormalizing
    valueIsSN leftIsSN rightIsSN rightAppIsSN

/-- **K12.20.X.2 eitherInr SN preservation**.  Mirror of
`eitherInl_isStronglyNormalizing` — same template, right injection. -/
theorem RawTerm.eitherInr_isStronglyNormalizing {scope : Nat}
    {valueTerm : RawTerm scope}
    (valueIsSN : RawTerm.isStronglyNormalizing valueTerm) :
    RawTerm.isStronglyNormalizing (RawTerm.eitherInr valueTerm) := by
  induction valueIsSN with
  | intro currentValue _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.eitherInr currentValue) ?_
    intro target progressStep
    obtain ⟨valueTarget, targetEq, valueStep⟩ :=
      RawStep.par.eitherInr_inv progressStep.1
    subst targetEq
    have valueDistinct :
        currentValue ≠ valueTarget := fun valueEq =>
      progressStep.2 (congrArg RawTerm.eitherInr valueEq)
    exact inductiveHypothesis valueTarget
      ⟨valueStep, valueDistinct⟩


end LeanFX2
