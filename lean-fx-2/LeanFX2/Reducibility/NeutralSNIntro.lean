import LeanFX2.Reducibility.NeutralSNHott

/-! # LeanFX2.Reducibility.NeutralSNIntro — K12.20.C ctor intros + type codes

Part 3 of K12.20.C.  Covers constructor-intro SN preservation
(`eitherInl`, `listCons`, `subsume`, `listNil`, container β
firings) plus the type-code SN cascade (`productCode`, `sumCode`,
`eitherCode`, `equivCode`, `listCode`, `optionCode`, `idCode`).

## What ships

* `RawTerm.eitherInl_isStronglyNormalizing` /
  `RawTerm.eitherInr_isStronglyNormalizing` — Either intros SN.
* `RawTerm.listCons_isStronglyNormalizing` /
  `RawTerm.listNil_isStronglyNormalizing` — List intros SN.
* `RawTerm.subsume_isStronglyNormalizing` — modal subsume wrapper
  SN.
* Container β-firing SN: `eitherMatch_eitherInl`,
  `eitherMatch_eitherInr`, `optionMatch_optionSome`,
  `listElim_listNil`, `listElim_listCons` — when the destructor
  fires on a canonical introducer, both branches' SN combine.
* `RawTerm.{product,sum,either,equiv,list,option,id}Code_isStronglyNormalizing`
  — value-shaped type-code Term ctors are SN by structural
  induction on their carrier sub-terms.

## Root status

Layer 3 metatheory leaf.  Continues the K12.20.C cascade.
Consumed by `NeutralSNClosure` (type-code-of summary lemma) and
downstream modules. -/

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

/-- **K12.20.Y modIntro SN preservation**.  Sister to the
optionSome / eitherInl / eitherInr helpers — unary cong-only ctor at
the modal-introduction ctor.  Powers future fundamental_modIntro at
parametric Ty.modal closures. -/
theorem RawTerm.modIntro_isStronglyNormalizing {scope : Nat}
    {innerTerm : RawTerm scope}
    (innerIsSN : RawTerm.isStronglyNormalizing innerTerm) :
    RawTerm.isStronglyNormalizing (RawTerm.modIntro innerTerm) := by
  induction innerIsSN with
  | intro currentInner _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.modIntro currentInner) ?_
    intro target progressStep
    obtain ⟨innerTarget, targetEq, innerStep⟩ :=
      RawStep.par.modIntro_inv progressStep.1
    subst targetEq
    have innerDistinct :
        currentInner ≠ innerTarget := fun innerEq =>
      progressStep.2 (congrArg RawTerm.modIntro innerEq)
    exact inductiveHypothesis innerTarget
      ⟨innerStep, innerDistinct⟩

/-- **K12.25 modal elimination SN preservation**.

`modElim` has a congruence arm plus the modal β arm
`modElim (modIntro payload) → payload`.  Congruent reducts recurse
through the inner SN witness.  β reducts first obtain SN of the
developed `modIntro payload`, then invert that constructor-shaped SN
back to SN of the payload. -/
theorem RawTerm.modElim_isStronglyNormalizing {scope : Nat}
    {innerTerm : RawTerm scope}
    (innerIsSN : RawTerm.isStronglyNormalizing innerTerm) :
    RawTerm.isStronglyNormalizing (RawTerm.modElim innerTerm) := by
  induction innerIsSN with
  | intro currentInner innerClosure innerIH =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.modElim currentInner) ?_
    intro target progressStep
    rcases RawStep.par.modElim_inv progressStep.1 with
      ⟨innerTarget, targetEq, innerStep⟩
      | ⟨payloadTarget, targetEq, innerStep⟩
    · subst targetEq
      by_cases innerEq : currentInner = innerTarget
      · subst innerEq
        exact (progressStep.2 rfl).elim
      · exact innerIH innerTarget ⟨innerStep, innerEq⟩
    · rw [targetEq]
      have introTargetIsSN :
          RawTerm.isStronglyNormalizing
            (RawTerm.modIntro payloadTarget) := by
        by_cases innerEq :
            currentInner = RawTerm.modIntro payloadTarget
        · rw [← innerEq]
          exact RawTerm.isStronglyNormalizing.intro
            currentInner innerClosure
        · exact innerClosure (RawTerm.modIntro payloadTarget)
            ⟨innerStep, innerEq⟩
      exact RawTerm.modIntro_inner_isStronglyNormalizing
        introTargetIsSN

/-- Typed wrapper for `RawTerm.modElim_isStronglyNormalizing`. -/
theorem Term.modElim_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    {innerTerm : Term context innerType innerRaw}
    (innerIsSN : Term.isStronglyNormalizing innerTerm) :
    Term.isStronglyNormalizing (Term.modElim innerTerm) :=
  RawTerm.modElim_isStronglyNormalizing innerIsSN

/-- **K12.20.Z pair SN preservation** — first binary cong-only SN
helper.  Pair has two parallel subterms; the SN proof needs nested
induction (outer on firstIsSN with `generalizing` to expose
second's SN as IH input, inner on secondIsSN) plus a per-side
disequality split.  When `pair currentFirst currentSecond` steps
to `pair firstTarget secondTarget` with the pair distinct, at
least one side must have advanced; case-split on which to discharge
via the outer or inner IH. -/
theorem RawTerm.pair_isStronglyNormalizing {scope : Nat}
    {firstValue : RawTerm scope}
    (firstIsSN : RawTerm.isStronglyNormalizing firstValue) :
    ∀ {secondValue : RawTerm scope},
      RawTerm.isStronglyNormalizing secondValue →
      RawTerm.isStronglyNormalizing
        (RawTerm.pair firstValue secondValue) := by
  induction firstIsSN with
  | intro currentFirst _ firstIH =>
    intro secondValue secondIsSN
    induction secondIsSN with
    | intro currentSecond secondClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.pair currentFirst currentSecond) ?_
      intro target progressStep
      obtain ⟨firstTarget, secondTarget, targetEq, firstStep, secondStep⟩ :=
        RawStep.par.pair_inv progressStep.1
      subst targetEq
      by_cases firstEq : currentFirst = firstTarget
      · subst firstEq
        have secondDistinct : currentSecond ≠ secondTarget := fun secondEq =>
          progressStep.2 (congrArg (RawTerm.pair currentFirst) secondEq)
        exact innerIH secondTarget ⟨secondStep, secondDistinct⟩
      · have firstProgress : RawStep.parProgress currentFirst firstTarget :=
          ⟨firstStep, firstEq⟩
        by_cases secondEq : currentSecond = secondTarget
        · subst secondEq
          exact firstIH firstTarget firstProgress
            (RawTerm.isStronglyNormalizing.intro currentSecond secondClosure)
        · exact firstIH firstTarget firstProgress
            (secondClosure secondTarget ⟨secondStep, secondEq⟩)

/-- Head-β SN expansion for first projection over a pair.

If both components are strongly normalizing, then `fst (pair first second)`
is strongly normalizing.  Congruence reducts recurse through the pair
components; β reducts land on a reduct of the first component. -/
theorem RawTerm.fst_pair_isStronglyNormalizing {scope : Nat}
    {firstValue : RawTerm scope}
    (firstIsSN : RawTerm.isStronglyNormalizing firstValue) :
    ∀ {secondValue : RawTerm scope},
      RawTerm.isStronglyNormalizing secondValue →
      RawTerm.isStronglyNormalizing
        (RawTerm.fst (RawTerm.pair firstValue secondValue)) := by
  induction firstIsSN with
  | intro currentFirst firstClosure firstIH =>
    intro secondValue secondIsSN
    induction secondIsSN with
    | intro currentSecond secondClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.fst (RawTerm.pair currentFirst currentSecond)) ?_
      intro target progressStep
      rcases RawStep.par.fst_inv progressStep.1 with
        ⟨pairTarget, targetEq, pairStep⟩
        | ⟨firstTarget, secondTarget, targetEq, pairStep⟩
      · obtain ⟨firstTarget, secondTarget, pairTargetEq,
            firstStep, secondStep⟩ :=
          RawStep.par.pair_inv pairStep
        subst pairTargetEq
        subst targetEq
        by_cases firstEq : currentFirst = firstTarget
        · subst firstEq
          by_cases secondEq : currentSecond = secondTarget
          · subst secondEq
            exact False.elim (progressStep.2 rfl)
          · exact innerIH secondTarget ⟨secondStep, secondEq⟩
        · have firstProgress :
              RawStep.parProgress currentFirst firstTarget :=
            ⟨firstStep, firstEq⟩
          by_cases secondEq : currentSecond = secondTarget
          · subst secondEq
            exact firstIH firstTarget firstProgress
              (RawTerm.isStronglyNormalizing.intro currentSecond secondClosure)
          · exact firstIH firstTarget firstProgress
              (secondClosure secondTarget ⟨secondStep, secondEq⟩)
      · obtain ⟨firstPairTarget, _secondPairTarget, pairTargetEq,
            firstStep, _secondStep⟩ :=
          RawStep.par.pair_inv pairStep
        injection pairTargetEq with _scopeEq firstTargetEq _secondTargetEq
        rw [targetEq]
        have firstStepToTarget : RawStep.par currentFirst firstTarget := by
          rw [firstTargetEq]
          exact firstStep
        by_cases firstEq : currentFirst = firstTarget
        · subst firstEq
          exact RawTerm.isStronglyNormalizing.intro
            currentFirst firstClosure
        · exact firstClosure firstTarget ⟨firstStepToTarget, firstEq⟩

/-- Head-β SN expansion for second projection over a pair.

If both components are strongly normalizing, then `snd (pair first second)`
is strongly normalizing.  Congruence reducts recurse through the pair
components; β reducts land on a reduct of the second component. -/
theorem RawTerm.snd_pair_isStronglyNormalizing {scope : Nat}
    {firstValue : RawTerm scope}
    (firstIsSN : RawTerm.isStronglyNormalizing firstValue) :
    ∀ {secondValue : RawTerm scope},
      RawTerm.isStronglyNormalizing secondValue →
      RawTerm.isStronglyNormalizing
        (RawTerm.snd (RawTerm.pair firstValue secondValue)) := by
  induction firstIsSN with
  | intro currentFirst firstClosure firstIH =>
    intro secondValue secondIsSN
    induction secondIsSN with
    | intro currentSecond secondClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.snd (RawTerm.pair currentFirst currentSecond)) ?_
      intro target progressStep
      rcases RawStep.par.snd_inv progressStep.1 with
        ⟨pairTarget, targetEq, pairStep⟩
        | ⟨firstTarget, secondTarget, targetEq, pairStep⟩
      · obtain ⟨firstTarget, secondTarget, pairTargetEq,
            firstStep, secondStep⟩ :=
          RawStep.par.pair_inv pairStep
        subst pairTargetEq
        subst targetEq
        by_cases firstEq : currentFirst = firstTarget
        · subst firstEq
          by_cases secondEq : currentSecond = secondTarget
          · subst secondEq
            exact False.elim (progressStep.2 rfl)
          · exact innerIH secondTarget ⟨secondStep, secondEq⟩
        · have firstProgress :
              RawStep.parProgress currentFirst firstTarget :=
            ⟨firstStep, firstEq⟩
          by_cases secondEq : currentSecond = secondTarget
          · subst secondEq
            exact firstIH firstTarget firstProgress
              (RawTerm.isStronglyNormalizing.intro currentSecond secondClosure)
          · exact firstIH firstTarget firstProgress
              (secondClosure secondTarget ⟨secondStep, secondEq⟩)
      · obtain ⟨_firstPairTarget, secondPairTarget, pairTargetEq,
            _firstStep, secondStep⟩ :=
          RawStep.par.pair_inv pairStep
        injection pairTargetEq with _scopeEq _firstTargetEq secondTargetEq
        rw [targetEq]
        have secondStepToTarget : RawStep.par currentSecond secondTarget := by
          rw [secondTargetEq]
          exact secondStep
        by_cases secondEq : currentSecond = secondTarget
        · subst secondEq
          exact RawTerm.isStronglyNormalizing.intro
            currentSecond secondClosure
        · exact secondClosure secondTarget ⟨secondStepToTarget, secondEq⟩

/-- Typed wrapper for pair SN expansion.

The raw proof is the computational content; this lemma exposes it at
the `Term` layer so future sigma-intro and head-expansion cases can
consume typed component SN witnesses directly. -/
theorem Term.pair_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {firstRaw secondRaw : RawTerm scope}
    {firstValue : Term context firstType firstRaw}
    {secondValue :
      Term context (secondType.subst0 firstType firstRaw) secondRaw}
    (firstIsSN : Term.isStronglyNormalizing firstValue)
    (secondIsSN : Term.isStronglyNormalizing secondValue) :
    Term.isStronglyNormalizing
      (Term.pair (secondType := secondType) firstValue secondValue) :=
  RawTerm.pair_isStronglyNormalizing firstIsSN secondIsSN

/-- Typed wrapper for `fst (pair first second)` SN expansion.

This is still an SN bridge, not the full sigma-intro reducibility
middle conjunct.  Full `Reducible firstType (fst (pair ...))`
requires typed backward closure at the result type. -/
theorem Term.fst_pair_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {firstRaw secondRaw : RawTerm scope}
    {firstValue : Term context firstType firstRaw}
    {secondValue :
      Term context (secondType.subst0 firstType firstRaw) secondRaw}
    (firstIsSN : Term.isStronglyNormalizing firstValue)
    (secondIsSN : Term.isStronglyNormalizing secondValue) :
    Term.isStronglyNormalizing
      (Term.fst
        (Term.pair (secondType := secondType) firstValue secondValue)) :=
  RawTerm.fst_pair_isStronglyNormalizing firstIsSN secondIsSN

/-- Typed wrapper for `snd (pair first second)` SN expansion. -/
theorem Term.snd_pair_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {firstRaw secondRaw : RawTerm scope}
    {firstValue : Term context firstType firstRaw}
    {secondValue :
      Term context (secondType.subst0 firstType firstRaw) secondRaw}
    (firstIsSN : Term.isStronglyNormalizing firstValue)
    (secondIsSN : Term.isStronglyNormalizing secondValue) :
    Term.isStronglyNormalizing
      (Term.snd
        (Term.pair (secondType := secondType) firstValue secondValue)) :=
  RawTerm.snd_pair_isStronglyNormalizing firstIsSN secondIsSN

/-- Generic first-projection SN preservation.

The congruence arm recurses through the projected pair.  The β arm can
only fire after the pair term develops to an explicit `pair`; component
SN then follows from the existing pair-component inversion lemma. -/
theorem RawTerm.fst_isStronglyNormalizing {scope : Nat}
    {pairRaw : RawTerm scope}
    (pairIsSN : RawTerm.isStronglyNormalizing pairRaw) :
    RawTerm.isStronglyNormalizing (RawTerm.fst pairRaw) := by
  induction pairIsSN with
  | intro currentPair pairClosure pairIH =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.fst currentPair) ?_
    intro target progressStep
    rcases RawStep.par.fst_inv progressStep.1 with
      ⟨pairTarget, targetEq, pairStep⟩
      | ⟨firstTarget, secondTarget, targetEq, pairStep⟩
    · subst targetEq
      by_cases pairEq : currentPair = pairTarget
      · subst pairEq
        exact (progressStep.2 rfl).elim
      · exact pairIH pairTarget ⟨pairStep, pairEq⟩
    · rw [targetEq]
      have developedPairIsSN :
          RawTerm.isStronglyNormalizing
            (RawTerm.pair firstTarget secondTarget) := by
        by_cases pairEq : currentPair =
            RawTerm.pair firstTarget secondTarget
        · rw [← pairEq]
          exact RawTerm.isStronglyNormalizing.intro
            currentPair pairClosure
        · exact pairClosure (RawTerm.pair firstTarget secondTarget)
            ⟨pairStep, pairEq⟩
      exact RawTerm.pair_first_isStronglyNormalizing developedPairIsSN

/-- Generic second-projection SN preservation.

This mirrors `RawTerm.fst_isStronglyNormalizing`; the β arm extracts
the second component from an SN developed pair. -/
theorem RawTerm.snd_isStronglyNormalizing {scope : Nat}
    {pairRaw : RawTerm scope}
    (pairIsSN : RawTerm.isStronglyNormalizing pairRaw) :
    RawTerm.isStronglyNormalizing (RawTerm.snd pairRaw) := by
  induction pairIsSN with
  | intro currentPair pairClosure pairIH =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.snd currentPair) ?_
    intro target progressStep
    rcases RawStep.par.snd_inv progressStep.1 with
      ⟨pairTarget, targetEq, pairStep⟩
      | ⟨firstTarget, secondTarget, targetEq, pairStep⟩
    · subst targetEq
      by_cases pairEq : currentPair = pairTarget
      · subst pairEq
        exact (progressStep.2 rfl).elim
      · exact pairIH pairTarget ⟨pairStep, pairEq⟩
    · rw [targetEq]
      have developedPairIsSN :
          RawTerm.isStronglyNormalizing
            (RawTerm.pair firstTarget secondTarget) := by
        by_cases pairEq : currentPair =
            RawTerm.pair firstTarget secondTarget
        · rw [← pairEq]
          exact RawTerm.isStronglyNormalizing.intro
            currentPair pairClosure
        · exact pairClosure (RawTerm.pair firstTarget secondTarget)
            ⟨pairStep, pairEq⟩
      exact RawTerm.pair_second_isStronglyNormalizing developedPairIsSN

/-- Direct M04 SN case for first projection from any SN pair term. -/
theorem Term.fst_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {pairRaw : RawTerm scope}
    {pairTerm : Term context (Ty.sigmaTy firstType secondType) pairRaw}
    (pairIsSN : Term.isStronglyNormalizing pairTerm) :
    Term.isStronglyNormalizing (Term.fst pairTerm) :=
  RawTerm.fst_isStronglyNormalizing pairIsSN

/-- Direct M04 SN case for second projection from any SN pair term. -/
theorem Term.snd_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {pairRaw : RawTerm scope}
    {pairTerm : Term context (Ty.sigmaTy firstType secondType) pairRaw}
    (pairIsSN : Term.isStronglyNormalizing pairTerm) :
    Term.isStronglyNormalizing (Term.snd pairTerm) :=
  RawTerm.snd_isStronglyNormalizing pairIsSN

/-- **K12.20.AA listCons SN preservation** — second binary SN
helper.  Same nested-induction + decidable-injectivity-split template
as `pair_isStronglyNormalizing`, applied to the cons-cell at the
head + tail positions of `Ty.listType`. -/
theorem RawTerm.listCons_isStronglyNormalizing {scope : Nat}
    {headTerm : RawTerm scope}
    (headIsSN : RawTerm.isStronglyNormalizing headTerm) :
    ∀ {tailTerm : RawTerm scope},
      RawTerm.isStronglyNormalizing tailTerm →
      RawTerm.isStronglyNormalizing
        (RawTerm.listCons headTerm tailTerm) := by
  induction headIsSN with
  | intro currentHead _ headIH =>
    intro tailTerm tailIsSN
    induction tailIsSN with
    | intro currentTail tailClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.listCons currentHead currentTail) ?_
      intro target progressStep
      obtain ⟨headTarget, tailTarget, targetEq, headStep, tailStep⟩ :=
        RawStep.par.listCons_inv progressStep.1
      subst targetEq
      by_cases headEq : currentHead = headTarget
      · subst headEq
        have tailDistinct : currentTail ≠ tailTarget := fun tailEq =>
          progressStep.2 (congrArg (RawTerm.listCons currentHead) tailEq)
        exact innerIH tailTarget ⟨tailStep, tailDistinct⟩
      · have headProgress : RawStep.parProgress currentHead headTarget :=
          ⟨headStep, headEq⟩
        by_cases tailEq : currentTail = tailTarget
        · subst tailEq
          exact headIH headTarget headProgress
            (RawTerm.isStronglyNormalizing.intro currentTail tailClosure)
        · exact headIH headTarget headProgress
            (tailClosure tailTarget ⟨tailStep, tailEq⟩)

/-- **K12.20.AB subsume SN preservation** — modal cumulativity cong.
Sister to `modIntro_isStronglyNormalizing` — unary cong-only ctor at
the modal-cumul-coercion position; no β rule at the raw level.
Powers future fundamental_subsume under the K12.16 Ty.cumulUp closure
chain. -/
theorem RawTerm.subsume_isStronglyNormalizing {scope : Nat}
    {innerTerm : RawTerm scope}
    (innerIsSN : RawTerm.isStronglyNormalizing innerTerm) :
    RawTerm.isStronglyNormalizing (RawTerm.subsume innerTerm) := by
  induction innerIsSN with
  | intro currentInner _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.subsume currentInner) ?_
    intro target progressStep
    obtain ⟨innerTarget, targetEq, innerStep⟩ :=
      RawStep.par.subsume_inv progressStep.1
    subst targetEq
    have innerDistinct :
        currentInner ≠ innerTarget := fun innerEq =>
      progressStep.2 (congrArg RawTerm.subsume innerEq)
    exact inductiveHypothesis innerTarget
      ⟨innerStep, innerDistinct⟩

/-- **K12.20.AC.1 listNil SN preservation** — nullary value at
parametric Ty.listType.  Sister to natZero / unit / boolTrue —
atomic ctor, only refl reduces, parProgress disequality contradicts
trivially. -/
theorem RawTerm.listNil_isStronglyNormalizing {scope : Nat} :
    RawTerm.isStronglyNormalizing (RawTerm.listNil : RawTerm scope) :=
  RawTerm.isStronglyNormalizing.intro
    (RawTerm.listNil : RawTerm scope)
    (fun _ progressStep =>
      (progressStep.2 (RawStep.par.listNil_inv progressStep.1).symm).elim)

/-- List-nil ι SN expansion for the eliminator.

For a canonical nil scrutinee, `listElim` reduces to the nil branch.
The cons branch stays explicit because congruent reductions may step
under it before the ι rule fires. -/
theorem RawTerm.listElim_listNil_isStronglyNormalizing
    {scope : Nat}
    {nilBranch : RawTerm scope}
    (nilIsSN : RawTerm.isStronglyNormalizing nilBranch) :
    ∀ {consBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing consBranch →
      RawTerm.isStronglyNormalizing
        (RawTerm.listElim RawTerm.listNil nilBranch consBranch) := by
  induction nilIsSN with
  | intro currentNil nilClosure nilIH =>
    intro consBranch consIsSN
    induction consIsSN with
    | intro currentCons consClosure consIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.listElim RawTerm.listNil currentNil currentCons) ?_
      intro target progressStep
      rcases RawStep.par.listElim_inv progressStep.1 with
        ⟨scrutineeTarget, nilTarget, consTarget, targetEq,
          scrutineeStep, nilStep, consStep⟩
        | ⟨nilTarget, targetEq, scrutineeStep, nilStep⟩
        | ⟨headTarget, tailTarget, consTarget, targetEq,
            scrutineeStep, consStep⟩
      · have scrutineeTargetEq :
            scrutineeTarget = (RawTerm.listNil : RawTerm scope) :=
          RawStep.par.listNil_inv scrutineeStep
        subst scrutineeTargetEq
        subst targetEq
        by_cases nilEq : currentNil = nilTarget
        · subst nilEq
          by_cases consEq : currentCons = consTarget
          · subst consEq
            exact (progressStep.2 rfl).elim
          · exact consIH consTarget ⟨consStep, consEq⟩
        · have consTargetIsSN :
              RawTerm.isStronglyNormalizing consTarget := by
            by_cases consEq : currentCons = consTarget
            · subst consEq
              exact RawTerm.isStronglyNormalizing.intro
                currentCons consClosure
            · exact consClosure consTarget ⟨consStep, consEq⟩
          exact nilIH nilTarget ⟨nilStep, nilEq⟩ consTargetIsSN
      · have nilTargetIsSN :
            RawTerm.isStronglyNormalizing nilTarget := by
          by_cases nilEq : currentNil = nilTarget
          · subst nilEq
            exact RawTerm.isStronglyNormalizing.intro
              currentNil nilClosure
          · exact nilClosure nilTarget ⟨nilStep, nilEq⟩
        rw [targetEq]
        exact nilTargetIsSN
      · have nilEq :
            RawTerm.listCons headTarget tailTarget =
              (RawTerm.listNil : RawTerm scope) :=
          RawStep.par.listNil_inv scrutineeStep
        nomatch nilEq

/-- Typed list-nil ι SN expansion for `Term.listElim`. -/
theorem Term.listElim_listNil_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {nilRaw consRaw : RawTerm scope}
    {nilBranch : Term context motiveType nilRaw}
    {consBranch : Term context (Ty.arrow elementType
                                  (Ty.arrow (Ty.listType elementType) motiveType)) consRaw}
    (nilIsSN : Term.isStronglyNormalizing nilBranch)
    (consIsSN : Term.isStronglyNormalizing consBranch) :
    Term.isStronglyNormalizing
      (Term.listElim
        (Term.listNil (elementType := elementType))
        nilBranch consBranch) :=
  RawTerm.listElim_listNil_isStronglyNormalizing
    nilIsSN consIsSN

/-- List-cons ι SN expansion for the eliminator.

For a canonical cons scrutinee, `listElim` reduces to
`consBranch head tail`.  The nil branch remains explicit because
congruent reductions may step under it before the ι rule fires. -/
theorem RawTerm.listElim_listCons_isStronglyNormalizing
    {scope : Nat}
    {headTerm : RawTerm scope}
    (headIsSN : RawTerm.isStronglyNormalizing headTerm) :
    ∀ {tailTerm : RawTerm scope},
      RawTerm.isStronglyNormalizing tailTerm →
    ∀ {nilBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing nilBranch →
    ∀ {consBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing consBranch →
      RawTerm.isStronglyNormalizing
        (RawTerm.app (RawTerm.app consBranch headTerm) tailTerm) →
      RawTerm.isStronglyNormalizing
        (RawTerm.listElim
          (RawTerm.listCons headTerm tailTerm) nilBranch consBranch) := by
  induction headIsSN with
  | intro currentHead headClosure headIH =>
    intro tailTerm tailIsSN
    induction tailIsSN with
    | intro currentTail tailClosure tailIH =>
      intro nilBranch nilIsSN
      induction nilIsSN with
      | intro currentNil nilClosure nilIH =>
        intro consBranch consIsSN consAppIsSN
        induction consIsSN with
        | intro currentCons consClosure consIH =>
          refine RawTerm.isStronglyNormalizing.intro
            (RawTerm.listElim
              (RawTerm.listCons currentHead currentTail)
              currentNil currentCons) ?_
          intro target progressStep
          rcases RawStep.par.listElim_inv progressStep.1 with
            ⟨scrutineeTarget, nilTarget, consTarget, targetEq,
              scrutineeStep, nilStep, consStep⟩
            | ⟨nilTarget, targetEq, scrutineeStep, nilStep⟩
            | ⟨headTarget, tailTarget, consTarget, targetEq,
                scrutineeStep, consStep⟩
          · obtain ⟨headTarget, tailTarget, scrutineeTargetEq,
                headStep, tailStep⟩ :=
              RawStep.par.listCons_inv scrutineeStep
            subst scrutineeTargetEq
            subst targetEq
            have headTargetIsSN :
                RawTerm.isStronglyNormalizing headTarget := by
              by_cases headEq : currentHead = headTarget
              · subst headEq
                exact RawTerm.isStronglyNormalizing.intro
                  currentHead headClosure
              · exact headClosure headTarget ⟨headStep, headEq⟩
            have tailTargetIsSN :
                RawTerm.isStronglyNormalizing tailTarget := by
              by_cases tailEq : currentTail = tailTarget
              · subst tailEq
                exact RawTerm.isStronglyNormalizing.intro
                  currentTail tailClosure
              · exact tailClosure tailTarget ⟨tailStep, tailEq⟩
            have nilTargetIsSN :
                RawTerm.isStronglyNormalizing nilTarget := by
              by_cases nilEq : currentNil = nilTarget
              · subst nilEq
                exact RawTerm.isStronglyNormalizing.intro
                  currentNil nilClosure
              · exact nilClosure nilTarget ⟨nilStep, nilEq⟩
            have consTargetIsSN :
                RawTerm.isStronglyNormalizing consTarget := by
              by_cases consEq : currentCons = consTarget
              · subst consEq
                exact RawTerm.isStronglyNormalizing.intro
                  currentCons consClosure
              · exact consClosure consTarget ⟨consStep, consEq⟩
            have consAppTargetIsSN :
                RawTerm.isStronglyNormalizing
                  (RawTerm.app
                    (RawTerm.app consTarget headTarget) tailTarget) := by
              by_cases appEq :
                  RawTerm.app (RawTerm.app currentCons currentHead) currentTail =
                    RawTerm.app (RawTerm.app consTarget headTarget) tailTarget
              · rw [← appEq]
                exact consAppIsSN
              · exact RawTerm.isStronglyNormalizing.step_preserves
                  consAppIsSN
                  ⟨RawStep.par.app
                    (RawStep.par.app consStep headStep) tailStep, appEq⟩
            by_cases headEq : currentHead = headTarget
            · subst headEq
              by_cases tailEq : currentTail = tailTarget
              · subst tailEq
                by_cases nilEq : currentNil = nilTarget
                · subst nilEq
                  by_cases consEq : currentCons = consTarget
                  · subst consEq
                    exact (progressStep.2 rfl).elim
                  · exact consIH consTarget ⟨consStep, consEq⟩
                      consAppTargetIsSN
                · exact nilIH nilTarget ⟨nilStep, nilEq⟩
                    consTargetIsSN consAppTargetIsSN
              · exact tailIH tailTarget ⟨tailStep, tailEq⟩
                  nilTargetIsSN consTargetIsSN consAppTargetIsSN
            · exact headIH headTarget ⟨headStep, headEq⟩
                tailTargetIsSN nilTargetIsSN consTargetIsSN
                consAppTargetIsSN
          · obtain ⟨headTarget, tailTarget, listNilEq,
                _headStep, _tailStep⟩ :=
              RawStep.par.listCons_inv scrutineeStep
            nomatch listNilEq
          · obtain ⟨headTargetFromScrutinee, tailTargetFromScrutinee,
                listConsEq, headStep, tailStep⟩ :=
              RawStep.par.listCons_inv scrutineeStep
            injection listConsEq with _scopeEq headTargetEq tailTargetEq
            subst targetEq
            have headStepToTarget :
                RawStep.par currentHead headTarget := by
              rw [headTargetEq]
              exact headStep
            have tailStepToTarget :
                RawStep.par currentTail tailTarget := by
              rw [tailTargetEq]
              exact tailStep
            have consAppTargetIsSN :
                RawTerm.isStronglyNormalizing
                  (RawTerm.app
                    (RawTerm.app consTarget headTarget) tailTarget) := by
              by_cases appEq :
                  RawTerm.app (RawTerm.app currentCons currentHead) currentTail =
                    RawTerm.app (RawTerm.app consTarget headTarget) tailTarget
              · rw [← appEq]
                exact consAppIsSN
              · exact RawTerm.isStronglyNormalizing.step_preserves
                  consAppIsSN
                  ⟨RawStep.par.app
                    (RawStep.par.app consStep headStepToTarget)
                    tailStepToTarget, appEq⟩
            exact consAppTargetIsSN

/-- Typed list-cons ι SN expansion for `Term.listElim`. -/
theorem Term.listElim_listCons_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {headRaw tailRaw nilRaw consRaw : RawTerm scope}
    {headTerm : Term context elementType headRaw}
    {tailTerm : Term context (Ty.listType elementType) tailRaw}
    {nilBranch : Term context motiveType nilRaw}
    {consBranch : Term context (Ty.arrow elementType
                                  (Ty.arrow (Ty.listType elementType) motiveType)) consRaw}
    (headIsSN : Term.isStronglyNormalizing headTerm)
    (tailIsSN : Term.isStronglyNormalizing tailTerm)
    (nilIsSN : Term.isStronglyNormalizing nilBranch)
    (consIsSN : Term.isStronglyNormalizing consBranch)
    (consAppIsSN :
      Term.isStronglyNormalizing
        (Term.app (Term.app consBranch headTerm) tailTerm)) :
    Term.isStronglyNormalizing
      (Term.listElim
        (Term.listCons headTerm tailTerm) nilBranch consBranch) :=
  RawTerm.listElim_listCons_isStronglyNormalizing
    headIsSN tailIsSN nilIsSN consIsSN consAppIsSN

/-- **K12.20.AC.2 optionNone SN preservation** — nullary value at
parametric Ty.optionType.  Same atomic shape as listNil. -/
theorem RawTerm.optionNone_isStronglyNormalizing {scope : Nat} :
    RawTerm.isStronglyNormalizing
      (RawTerm.optionNone : RawTerm scope) :=
  RawTerm.isStronglyNormalizing.intro
    (RawTerm.optionNone : RawTerm scope)
    (fun _ progressStep =>
      (progressStep.2 (RawStep.par.optionNone_inv progressStep.1).symm).elim)

/-- Option-none ι SN expansion for the eliminator.

For a canonical `none` scrutinee, `optionMatch` reduces to the none
branch.  The some branch remains in the statement because congruent
reductions may still step under it before the ι rule fires. -/
theorem RawTerm.optionMatch_optionNone_isStronglyNormalizing
    {scope : Nat}
    {noneBranch : RawTerm scope}
    (noneIsSN : RawTerm.isStronglyNormalizing noneBranch) :
    ∀ {someBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing someBranch →
      RawTerm.isStronglyNormalizing
        (RawTerm.optionMatch RawTerm.optionNone noneBranch someBranch) := by
  induction noneIsSN with
  | intro currentNone noneClosure noneIH =>
    intro someBranch someIsSN
    induction someIsSN with
    | intro currentSome someClosure someIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.optionMatch RawTerm.optionNone currentNone currentSome) ?_
      intro target progressStep
      rcases RawStep.par.optionMatch_inv progressStep.1 with
        ⟨scrutineeTarget, noneTarget, someTarget, targetEq,
          scrutineeStep, noneStep, someStep⟩
        | ⟨noneTarget, targetEq, scrutineeStep, noneStep⟩
        | ⟨valueTarget, someTarget, targetEq, scrutineeStep, someStep⟩
      · have scrutineeTargetEq :
            scrutineeTarget = (RawTerm.optionNone : RawTerm scope) :=
          RawStep.par.optionNone_inv scrutineeStep
        subst scrutineeTargetEq
        subst targetEq
        by_cases noneEq : currentNone = noneTarget
        · subst noneEq
          by_cases someEq : currentSome = someTarget
          · subst someEq
            exact (progressStep.2 rfl).elim
          · exact someIH someTarget ⟨someStep, someEq⟩
        · have someTargetIsSN :
              RawTerm.isStronglyNormalizing someTarget := by
            by_cases someEq : currentSome = someTarget
            · subst someEq
              exact RawTerm.isStronglyNormalizing.intro
                currentSome someClosure
            · exact someClosure someTarget ⟨someStep, someEq⟩
          exact noneIH noneTarget ⟨noneStep, noneEq⟩ someTargetIsSN
      · have noneTargetIsSN :
            RawTerm.isStronglyNormalizing noneTarget := by
          by_cases noneEq : currentNone = noneTarget
          · subst noneEq
            exact RawTerm.isStronglyNormalizing.intro
              currentNone noneClosure
          · exact noneClosure noneTarget ⟨noneStep, noneEq⟩
        rw [targetEq]
        exact noneTargetIsSN
      · have noneEq :
            RawTerm.optionSome valueTarget =
              (RawTerm.optionNone : RawTerm scope) :=
          RawStep.par.optionNone_inv scrutineeStep
        nomatch noneEq

/-- Typed option-none ι SN expansion for `Term.optionMatch`. -/
theorem Term.optionMatch_optionNone_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {noneRaw someRaw : RawTerm scope}
    {noneBranch : Term context motiveType noneRaw}
    {someBranch : Term context (Ty.arrow elementType motiveType) someRaw}
    (noneIsSN : Term.isStronglyNormalizing noneBranch)
    (someIsSN : Term.isStronglyNormalizing someBranch) :
    Term.isStronglyNormalizing
      (Term.optionMatch
        (Term.optionNone (elementType := elementType))
        noneBranch someBranch) :=
  RawTerm.optionMatch_optionNone_isStronglyNormalizing
    noneIsSN someIsSN

/-- **K12.20.AD.1 refl SN preservation** — HoTT identity-type
introduction.  Unary cong over the path witness; refl_inv discharges
each par step. -/
theorem RawTerm.refl_isStronglyNormalizing {scope : Nat}
    {rawWitness : RawTerm scope}
    (witnessIsSN : RawTerm.isStronglyNormalizing rawWitness) :
    RawTerm.isStronglyNormalizing (RawTerm.refl rawWitness) := by
  induction witnessIsSN with
  | intro currentWitness _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.refl currentWitness) ?_
    intro target progressStep
    obtain ⟨witnessTarget, targetEq, witnessStep⟩ :=
      RawStep.par.refl_inv progressStep.1
    subst targetEq
    have witnessDistinct :
        currentWitness ≠ witnessTarget := fun witnessEq =>
      progressStep.2 (congrArg RawTerm.refl witnessEq)
    exact inductiveHypothesis witnessTarget
      ⟨witnessStep, witnessDistinct⟩

/-- **K12.20.AD.2 oeqRefl SN preservation** — observational-equality
reflexivity intro.  Sister to refl helper; oeqRefl_inv discharges. -/
theorem RawTerm.oeqRefl_isStronglyNormalizing {scope : Nat}
    {witness : RawTerm scope}
    (witnessIsSN : RawTerm.isStronglyNormalizing witness) :
    RawTerm.isStronglyNormalizing (RawTerm.oeqRefl witness) := by
  induction witnessIsSN with
  | intro currentWitness _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.oeqRefl currentWitness) ?_
    intro target progressStep
    obtain ⟨witnessTarget, targetEq, witnessStep⟩ :=
      RawStep.par.oeqRefl_inv progressStep.1
    subst targetEq
    have witnessDistinct :
        currentWitness ≠ witnessTarget := fun witnessEq =>
      progressStep.2 (congrArg RawTerm.oeqRefl witnessEq)
    exact inductiveHypothesis witnessTarget
      ⟨witnessStep, witnessDistinct⟩

/-- **K12.20.AD.3 idStrictRefl SN preservation** — strict-id
reflexivity intro.  Same unary shape as refl / oeqRefl. -/
theorem RawTerm.idStrictRefl_isStronglyNormalizing {scope : Nat}
    {witness : RawTerm scope}
    (witnessIsSN : RawTerm.isStronglyNormalizing witness) :
    RawTerm.isStronglyNormalizing (RawTerm.idStrictRefl witness) := by
  induction witnessIsSN with
  | intro currentWitness _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.idStrictRefl currentWitness) ?_
    intro target progressStep
    obtain ⟨witnessTarget, targetEq, witnessStep⟩ :=
      RawStep.par.idStrictRefl_inv progressStep.1
    subst targetEq
    have witnessDistinct :
        currentWitness ≠ witnessTarget := fun witnessEq =>
      progressStep.2 (congrArg RawTerm.idStrictRefl witnessEq)
    exact inductiveHypothesis witnessTarget
      ⟨witnessStep, witnessDistinct⟩

/-- **K12.20.AE.1 interval0 SN preservation** — cubical interval
endpoint 0.  Atomic nullary, only-refl reduces, parProgress
disequality contradicts the .symm of interval0_inv. -/
theorem RawTerm.interval0_isStronglyNormalizing {scope : Nat} :
    RawTerm.isStronglyNormalizing (RawTerm.interval0 : RawTerm scope) :=
  RawTerm.isStronglyNormalizing.intro
    (RawTerm.interval0 : RawTerm scope)
    (fun _ progressStep =>
      (progressStep.2 (RawStep.par.interval0_inv progressStep.1).symm).elim)

/-- **K12.20.AE.2 interval1 SN preservation** — cubical interval
endpoint 1.  Sister to interval0; same atomic nullary shape. -/
theorem RawTerm.interval1_isStronglyNormalizing {scope : Nat} :
    RawTerm.isStronglyNormalizing (RawTerm.interval1 : RawTerm scope) :=
  RawTerm.isStronglyNormalizing.intro
    (RawTerm.interval1 : RawTerm scope)
    (fun _ progressStep =>
      (progressStep.2 (RawStep.par.interval1_inv progressStep.1).symm).elim)

/-- **K12.20.AR.2 universeCode SN preservation** — universe code
intro at outer level.  `RawTerm.universeCode innerLevel` has no
β/ι rules; only `RawStep.par.refl` applies (per
`RawStep.par.universeCode_inv` in
`Reduction/RawParInversion.lean`), so `parProgress`'s
source-≠-target requirement contradicts the inversion's
.symm. -/
theorem RawTerm.universeCode_isStronglyNormalizing {scope : Nat}
    (innerLevel : Nat) :
    RawTerm.isStronglyNormalizing
      (RawTerm.universeCode innerLevel : RawTerm scope) :=
  RawTerm.isStronglyNormalizing.intro
    (RawTerm.universeCode innerLevel : RawTerm scope)
    (fun _ progressStep =>
      (progressStep.2
        (RawStep.par.universeCode_inv progressStep.1).symm).elim)

/-- Type-code arrow constructor SN preservation.

Unlike `universeCode`, `arrowCode` carries schematic raw payloads and
`RawStep.par` reduces under both of them.  The SN premises are therefore
real obligations; M04 cannot treat schematic type-code payloads as
normalizing constants. -/
theorem RawTerm.arrowCode_isStronglyNormalizing {scope : Nat}
    {domainCode : RawTerm scope}
    (domainIsSN : RawTerm.isStronglyNormalizing domainCode) :
    ∀ {codomainCode : RawTerm scope},
    RawTerm.isStronglyNormalizing codomainCode →
    RawTerm.isStronglyNormalizing
      (RawTerm.arrowCode domainCode codomainCode) := by
  induction domainIsSN with
  | intro currentDomain _ domainIH =>
    intro codomainCode codomainIsSN
    induction codomainIsSN with
    | intro currentCodomain codomainClosure codomainIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.arrowCode currentDomain currentCodomain) ?_
      intro target progressStep
      obtain ⟨domainTarget, codomainTarget, targetEq,
              domainStep, codomainStep⟩ :=
        RawStep.par.arrowCode_inv progressStep.1
      subst targetEq
      by_cases domainEq : currentDomain = domainTarget
      · subst domainEq
        by_cases codomainEq : currentCodomain = codomainTarget
        · subst codomainEq
          exact False.elim (progressStep.2 rfl)
        · exact codomainIH codomainTarget ⟨codomainStep, codomainEq⟩
      · have domainProgress :
            RawStep.parProgress currentDomain domainTarget :=
          ⟨domainStep, domainEq⟩
        by_cases codomainEq : currentCodomain = codomainTarget
        · subst codomainEq
          exact domainIH domainTarget domainProgress
            (RawTerm.isStronglyNormalizing.intro
              currentCodomain codomainClosure)
        · exact domainIH domainTarget domainProgress
            (codomainClosure codomainTarget ⟨codomainStep, codomainEq⟩)

/-- Type-code dependent-Pi constructor SN preservation.

The codomain code lives under the Pi binder at `scope + 1`, so this is
not just a specialization of `arrowCode_isStronglyNormalizing`.  The
proof is the same two-payload congruence argument, with the second SN
witness indexed over the lifted scope. -/
theorem RawTerm.piTyCode_isStronglyNormalizing {scope : Nat}
    {domainCode : RawTerm scope}
    (domainIsSN : RawTerm.isStronglyNormalizing domainCode) :
    ∀ {codomainCode : RawTerm (scope + 1)},
    RawTerm.isStronglyNormalizing codomainCode →
    RawTerm.isStronglyNormalizing
      (RawTerm.piTyCode domainCode codomainCode) := by
  induction domainIsSN with
  | intro currentDomain _ domainIH =>
    intro codomainCode codomainIsSN
    induction codomainIsSN with
    | intro currentCodomain codomainClosure codomainIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.piTyCode currentDomain currentCodomain) ?_
      intro target progressStep
      obtain ⟨domainTarget, codomainTarget, targetEq,
              domainStep, codomainStep⟩ :=
        RawStep.par.piTyCode_inv progressStep.1
      subst targetEq
      by_cases domainEq : currentDomain = domainTarget
      · subst domainEq
        by_cases codomainEq : currentCodomain = codomainTarget
        · subst codomainEq
          exact False.elim (progressStep.2 rfl)
        · exact codomainIH codomainTarget ⟨codomainStep, codomainEq⟩
      · have domainProgress :
            RawStep.parProgress currentDomain domainTarget :=
          ⟨domainStep, domainEq⟩
        by_cases codomainEq : currentCodomain = codomainTarget
        · subst codomainEq
          exact domainIH domainTarget domainProgress
            (RawTerm.isStronglyNormalizing.intro
              currentCodomain codomainClosure)
        · exact domainIH domainTarget domainProgress
            (codomainClosure codomainTarget ⟨codomainStep, codomainEq⟩)

/-- Type-code dependent-Sigma constructor SN preservation.

Like `piTyCode_isStronglyNormalizing`, the second code payload is scoped
under the binder at `scope + 1`.  The proof isolates the two raw
congruence payloads and preserves SN by nested induction over them. -/
theorem RawTerm.sigmaTyCode_isStronglyNormalizing {scope : Nat}
    {firstCode : RawTerm scope}
    (firstIsSN : RawTerm.isStronglyNormalizing firstCode) :
    ∀ {secondCode : RawTerm (scope + 1)},
    RawTerm.isStronglyNormalizing secondCode →
    RawTerm.isStronglyNormalizing
      (RawTerm.sigmaTyCode firstCode secondCode) := by
  induction firstIsSN with
  | intro currentFirst _ firstIH =>
    intro secondCode secondIsSN
    induction secondIsSN with
    | intro currentSecond secondClosure secondIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.sigmaTyCode currentFirst currentSecond) ?_
      intro target progressStep
      obtain ⟨firstTarget, secondTarget, targetEq,
              firstStep, secondStep⟩ :=
        RawStep.par.sigmaTyCode_inv progressStep.1
      subst targetEq
      by_cases firstEq : currentFirst = firstTarget
      · subst firstEq
        by_cases secondEq : currentSecond = secondTarget
        · subst secondEq
          exact False.elim (progressStep.2 rfl)
        · exact secondIH secondTarget ⟨secondStep, secondEq⟩
      · have firstProgress :
            RawStep.parProgress currentFirst firstTarget :=
          ⟨firstStep, firstEq⟩
        by_cases secondEq : currentSecond = secondTarget
        · subst secondEq
          exact firstIH firstTarget firstProgress
            (RawTerm.isStronglyNormalizing.intro
              currentSecond secondClosure)
        · exact firstIH firstTarget firstProgress
            (secondClosure secondTarget ⟨secondStep, secondEq⟩)

/-- Type-code product constructor SN preservation.

`productCode` carries two same-scope schematic raw payloads.  Raw
parallel reduction reduces under both payloads, so SN of the product
code follows by nested induction over the two payload SN witnesses. -/
theorem RawTerm.productCode_isStronglyNormalizing {scope : Nat}
    {firstCode : RawTerm scope}
    (firstIsSN : RawTerm.isStronglyNormalizing firstCode) :
    ∀ {secondCode : RawTerm scope},
    RawTerm.isStronglyNormalizing secondCode →
    RawTerm.isStronglyNormalizing
      (RawTerm.productCode firstCode secondCode) := by
  induction firstIsSN with
  | intro currentFirst _ firstIH =>
    intro secondCode secondIsSN
    induction secondIsSN with
    | intro currentSecond secondClosure secondIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.productCode currentFirst currentSecond) ?_
      intro target progressStep
      obtain ⟨firstTarget, secondTarget, targetEq,
              firstStep, secondStep⟩ :=
        RawStep.par.productCode_inv progressStep.1
      subst targetEq
      by_cases firstEq : currentFirst = firstTarget
      · subst firstEq
        by_cases secondEq : currentSecond = secondTarget
        · subst secondEq
          exact False.elim (progressStep.2 rfl)
        · exact secondIH secondTarget ⟨secondStep, secondEq⟩
      · have firstProgress :
            RawStep.parProgress currentFirst firstTarget :=
          ⟨firstStep, firstEq⟩
        by_cases secondEq : currentSecond = secondTarget
        · subst secondEq
          exact firstIH firstTarget firstProgress
            (RawTerm.isStronglyNormalizing.intro
              currentSecond secondClosure)
        · exact firstIH firstTarget firstProgress
            (secondClosure secondTarget ⟨secondStep, secondEq⟩)

/-- Type-code sum constructor SN preservation.

`sumCode` mirrors `productCode`: both schematic raw payloads are in
the same scope, and raw parallel reduction only proceeds by congruence
under those payloads. -/
theorem RawTerm.sumCode_isStronglyNormalizing {scope : Nat}
    {leftCode : RawTerm scope}
    (leftIsSN : RawTerm.isStronglyNormalizing leftCode) :
    ∀ {rightCode : RawTerm scope},
    RawTerm.isStronglyNormalizing rightCode →
    RawTerm.isStronglyNormalizing
      (RawTerm.sumCode leftCode rightCode) := by
  induction leftIsSN with
  | intro currentLeft _ leftIH =>
    intro rightCode rightIsSN
    induction rightIsSN with
    | intro currentRight rightClosure rightIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.sumCode currentLeft currentRight) ?_
      intro target progressStep
      obtain ⟨leftTarget, rightTarget, targetEq,
              leftStep, rightStep⟩ :=
        RawStep.par.sumCode_inv progressStep.1
      subst targetEq
      by_cases leftEq : currentLeft = leftTarget
      · subst leftEq
        by_cases rightEq : currentRight = rightTarget
        · subst rightEq
          exact False.elim (progressStep.2 rfl)
        · exact rightIH rightTarget ⟨rightStep, rightEq⟩
      · have leftProgress :
            RawStep.parProgress currentLeft leftTarget :=
          ⟨leftStep, leftEq⟩
        by_cases rightEq : currentRight = rightTarget
        · subst rightEq
          exact leftIH leftTarget leftProgress
            (RawTerm.isStronglyNormalizing.intro
              currentRight rightClosure)
        · exact leftIH leftTarget leftProgress
            (rightClosure rightTarget ⟨rightStep, rightEq⟩)

/-- Type-code either constructor SN preservation.

`eitherCode` is the same same-scope binary type-code shape as
`sumCode`: raw parallel reduction only reduces congruently under the
left and right schematic payloads. -/
theorem RawTerm.eitherCode_isStronglyNormalizing {scope : Nat}
    {leftCode : RawTerm scope}
    (leftIsSN : RawTerm.isStronglyNormalizing leftCode) :
    ∀ {rightCode : RawTerm scope},
    RawTerm.isStronglyNormalizing rightCode →
    RawTerm.isStronglyNormalizing
      (RawTerm.eitherCode leftCode rightCode) := by
  induction leftIsSN with
  | intro currentLeft _ leftIH =>
    intro rightCode rightIsSN
    induction rightIsSN with
    | intro currentRight rightClosure rightIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.eitherCode currentLeft currentRight) ?_
      intro target progressStep
      obtain ⟨leftTarget, rightTarget, targetEq,
              leftStep, rightStep⟩ :=
        RawStep.par.eitherCode_inv progressStep.1
      subst targetEq
      by_cases leftEq : currentLeft = leftTarget
      · subst leftEq
        by_cases rightEq : currentRight = rightTarget
        · subst rightEq
          exact False.elim (progressStep.2 rfl)
        · exact rightIH rightTarget ⟨rightStep, rightEq⟩
      · have leftProgress :
            RawStep.parProgress currentLeft leftTarget :=
          ⟨leftStep, leftEq⟩
        by_cases rightEq : currentRight = rightTarget
        · subst rightEq
          exact leftIH leftTarget leftProgress
            (RawTerm.isStronglyNormalizing.intro
              currentRight rightClosure)
        · exact leftIH leftTarget leftProgress
            (rightClosure rightTarget ⟨rightStep, rightEq⟩)

/-- Type-code equivalence constructor SN preservation.

`equivCode` is congruence-only over two same-scope schematic type-code
payloads, so it follows the binary payload SN argument used by
`sumCode` and `eitherCode`. -/
theorem RawTerm.equivCode_isStronglyNormalizing {scope : Nat}
    {leftCode : RawTerm scope}
    (leftIsSN : RawTerm.isStronglyNormalizing leftCode) :
    ∀ {rightCode : RawTerm scope},
    RawTerm.isStronglyNormalizing rightCode →
    RawTerm.isStronglyNormalizing
      (RawTerm.equivCode leftCode rightCode) := by
  induction leftIsSN with
  | intro currentLeft _ leftIH =>
    intro rightCode rightIsSN
    induction rightIsSN with
    | intro currentRight rightClosure rightIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.equivCode currentLeft currentRight) ?_
      intro target progressStep
      obtain ⟨leftTarget, rightTarget, targetEq,
              leftStep, rightStep⟩ :=
        RawStep.par.equivCode_inv progressStep.1
      subst targetEq
      by_cases leftEq : currentLeft = leftTarget
      · subst leftEq
        by_cases rightEq : currentRight = rightTarget
        · subst rightEq
          exact False.elim (progressStep.2 rfl)
        · exact rightIH rightTarget ⟨rightStep, rightEq⟩
      · have leftProgress :
            RawStep.parProgress currentLeft leftTarget :=
          ⟨leftStep, leftEq⟩
        by_cases rightEq : currentRight = rightTarget
        · subst rightEq
          exact leftIH leftTarget leftProgress
            (RawTerm.isStronglyNormalizing.intro
              currentRight rightClosure)
        · exact leftIH leftTarget leftProgress
            (rightClosure rightTarget ⟨rightStep, rightEq⟩)

/-- Type-code list constructor SN preservation.

`listCode` is congruence-only over its schematic element-code
payload, so SN follows by one induction over that payload. -/
theorem RawTerm.listCode_isStronglyNormalizing {scope : Nat}
    {elementCode : RawTerm scope}
    (elementIsSN : RawTerm.isStronglyNormalizing elementCode) :
    RawTerm.isStronglyNormalizing
      (RawTerm.listCode elementCode) := by
  induction elementIsSN with
  | intro currentElement _ elementIH =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.listCode currentElement) ?_
    intro target progressStep
    obtain ⟨elementTarget, targetEq, elementStep⟩ :=
      RawStep.par.listCode_inv progressStep.1
    subst targetEq
    have elementDistinct :
        currentElement ≠ elementTarget := fun elementEq =>
      progressStep.2 (congrArg RawTerm.listCode elementEq)
    exact elementIH elementTarget
      ⟨elementStep, elementDistinct⟩

/-- Type-code option constructor SN preservation.

`optionCode` is congruence-only over its schematic element-code
payload, matching `listCode` at the raw layer. -/
theorem RawTerm.optionCode_isStronglyNormalizing {scope : Nat}
    {elementCode : RawTerm scope}
    (elementIsSN : RawTerm.isStronglyNormalizing elementCode) :
    RawTerm.isStronglyNormalizing
      (RawTerm.optionCode elementCode) := by
  induction elementIsSN with
  | intro currentElement _ elementIH =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.optionCode currentElement) ?_
    intro target progressStep
    obtain ⟨elementTarget, targetEq, elementStep⟩ :=
      RawStep.par.optionCode_inv progressStep.1
    subst targetEq
    have elementDistinct :
        currentElement ≠ elementTarget := fun elementEq =>
      progressStep.2 (congrArg RawTerm.optionCode elementEq)
    exact elementIH elementTarget
      ⟨elementStep, elementDistinct⟩

/-- Type-code identity constructor SN preservation.

`idCode` is congruence-only over its schematic carrier and endpoint
codes.  SN follows by the same payload-product induction as the
binary type-code constructors, extended to the ternary payload. -/
theorem RawTerm.idCode_isStronglyNormalizing {scope : Nat}
    {typeCode : RawTerm scope}
    (typeCodeIsSN : RawTerm.isStronglyNormalizing typeCode) :
    ∀ {leftCode : RawTerm scope},
    RawTerm.isStronglyNormalizing leftCode →
    ∀ {rightCode : RawTerm scope},
    RawTerm.isStronglyNormalizing rightCode →
  RawTerm.isStronglyNormalizing
      (RawTerm.idCode typeCode leftCode rightCode) := by
  induction typeCodeIsSN with
  | intro currentType _ typeIH =>
    intro leftCode leftCodeIsSN
    induction leftCodeIsSN with
    | intro currentLeft leftClosure leftIH =>
      intro rightCode rightCodeIsSN
      induction rightCodeIsSN with
      | intro currentRight rightClosure rightIH =>
        refine RawTerm.isStronglyNormalizing.intro
          (RawTerm.idCode currentType currentLeft currentRight) ?_
        intro target progressStep
        obtain ⟨typeTarget, leftTarget, rightTarget, targetEq,
                typeStep, leftStep, rightStep⟩ :=
          RawStep.par.idCode_inv progressStep.1
        subst targetEq
        by_cases typeEq : currentType = typeTarget
        · subst typeEq
          by_cases leftEq : currentLeft = leftTarget
          · subst leftEq
            by_cases rightEq : currentRight = rightTarget
            · subst rightEq
              exact False.elim (progressStep.2 rfl)
            · exact rightIH rightTarget ⟨rightStep, rightEq⟩
          · have leftProgress :
                RawStep.parProgress currentLeft leftTarget :=
              ⟨leftStep, leftEq⟩
            by_cases rightEq : currentRight = rightTarget
            · subst rightEq
              exact leftIH leftTarget leftProgress
                (RawTerm.isStronglyNormalizing.intro
                  currentRight rightClosure)
            · exact leftIH leftTarget leftProgress
                (rightClosure rightTarget ⟨rightStep, rightEq⟩)
        · have typeProgress :
              RawStep.parProgress currentType typeTarget :=
            ⟨typeStep, typeEq⟩
          by_cases leftEq : currentLeft = leftTarget
          · subst leftEq
            by_cases rightEq : currentRight = rightTarget
            · subst rightEq
              exact typeIH typeTarget typeProgress
                (RawTerm.isStronglyNormalizing.intro
                  currentLeft leftClosure)
                (RawTerm.isStronglyNormalizing.intro
                  currentRight rightClosure)
            · exact typeIH typeTarget typeProgress
                (RawTerm.isStronglyNormalizing.intro
                  currentLeft leftClosure)
                (rightClosure rightTarget ⟨rightStep, rightEq⟩)
          · have leftTargetIsSN :
                RawTerm.isStronglyNormalizing leftTarget :=
              leftClosure leftTarget ⟨leftStep, leftEq⟩
            by_cases rightEq : currentRight = rightTarget
            · subst rightEq
              exact typeIH typeTarget typeProgress
                leftTargetIsSN
                (RawTerm.isStronglyNormalizing.intro
                  currentRight rightClosure)
            · exact typeIH typeTarget typeProgress
                leftTargetIsSN
                (rightClosure rightTarget ⟨rightStep, rightEq⟩)

/-- **K12.27 type-code payload SN frontier**.

`Term.*Code` constructors currently store schematic `RawTerm` payloads
rather than recursive typed children.  Since raw parallel reduction
reduces under those payloads, M04 cannot discharge their constructor
cases from the `Term` induction alone.  This predicate names exactly
the residual evidence a schematic type-code tree must carry for the
raw SN endpoint.

For `idCode`, the carrier must itself be a normalizing type code, while
the endpoints only need raw SN: they are term codes at the carrier, not
type codes. -/
inductive RawTerm.IsStronglyNormalizingTypeCode :
    ∀ {scope : Nat}, RawTerm scope → Prop
  | universeCode {scope : Nat} (innerLevel : Nat) :
      RawTerm.IsStronglyNormalizingTypeCode
        (RawTerm.universeCode innerLevel : RawTerm scope)
  | arrowCode {scope : Nat} {domainCode codomainCode : RawTerm scope} :
      RawTerm.IsStronglyNormalizingTypeCode domainCode →
      RawTerm.IsStronglyNormalizingTypeCode codomainCode →
      RawTerm.IsStronglyNormalizingTypeCode
        (RawTerm.arrowCode domainCode codomainCode)
  | piTyCode {scope : Nat}
      {domainCode : RawTerm scope}
      {codomainCode : RawTerm (scope + 1)} :
      RawTerm.IsStronglyNormalizingTypeCode domainCode →
      RawTerm.IsStronglyNormalizingTypeCode codomainCode →
      RawTerm.IsStronglyNormalizingTypeCode
        (RawTerm.piTyCode domainCode codomainCode)
  | sigmaTyCode {scope : Nat}
      {domainCode : RawTerm scope}
      {codomainCode : RawTerm (scope + 1)} :
      RawTerm.IsStronglyNormalizingTypeCode domainCode →
      RawTerm.IsStronglyNormalizingTypeCode codomainCode →
      RawTerm.IsStronglyNormalizingTypeCode
        (RawTerm.sigmaTyCode domainCode codomainCode)
  | productCode {scope : Nat} {firstCode secondCode : RawTerm scope} :
      RawTerm.IsStronglyNormalizingTypeCode firstCode →
      RawTerm.IsStronglyNormalizingTypeCode secondCode →
      RawTerm.IsStronglyNormalizingTypeCode
        (RawTerm.productCode firstCode secondCode)
  | sumCode {scope : Nat} {leftCode rightCode : RawTerm scope} :
      RawTerm.IsStronglyNormalizingTypeCode leftCode →
      RawTerm.IsStronglyNormalizingTypeCode rightCode →
      RawTerm.IsStronglyNormalizingTypeCode
        (RawTerm.sumCode leftCode rightCode)
  | listCode {scope : Nat} {elementCode : RawTerm scope} :
      RawTerm.IsStronglyNormalizingTypeCode elementCode →
      RawTerm.IsStronglyNormalizingTypeCode
        (RawTerm.listCode elementCode)
  | optionCode {scope : Nat} {elementCode : RawTerm scope} :
      RawTerm.IsStronglyNormalizingTypeCode elementCode →
      RawTerm.IsStronglyNormalizingTypeCode
        (RawTerm.optionCode elementCode)
  | eitherCode {scope : Nat} {leftCode rightCode : RawTerm scope} :
      RawTerm.IsStronglyNormalizingTypeCode leftCode →
      RawTerm.IsStronglyNormalizingTypeCode rightCode →
      RawTerm.IsStronglyNormalizingTypeCode
        (RawTerm.eitherCode leftCode rightCode)
  | idCode {scope : Nat}
      {typeCode leftEndpoint rightEndpoint : RawTerm scope} :
      RawTerm.IsStronglyNormalizingTypeCode typeCode →
      RawTerm.isStronglyNormalizing leftEndpoint →
      RawTerm.isStronglyNormalizing rightEndpoint →
      RawTerm.IsStronglyNormalizingTypeCode
        (RawTerm.idCode typeCode leftEndpoint rightEndpoint)
  | equivCode {scope : Nat} {leftTypeCode rightTypeCode : RawTerm scope} :
      RawTerm.IsStronglyNormalizingTypeCode leftTypeCode →
      RawTerm.IsStronglyNormalizingTypeCode rightTypeCode →
      RawTerm.IsStronglyNormalizingTypeCode
        (RawTerm.equivCode leftTypeCode rightTypeCode)


end LeanFX2
