import LeanFX2.Reducibility.SNHelpers
import LeanFX2.Reducibility.Neutral.ModalAdvancedPreservation

/-! # LeanFX2.Reducibility.NeutralSNFoundation.ListOptionEither

Parametric inductive recursor SN preservation.  Covers `listElim`,
`optionMatch`, and `eitherMatch` in their `_var` and `_neutral`
variants.

## Root status

Layer 3 metatheory leaf.  Third slice of NeutralSNFoundation. -/

namespace LeanFX2

/-- **K12.20.AW.1 neutral listElim SN preservation**.  Sister to
the K12.20.AU/AV eliminator family; parametric-list recursor.

Variable scrutinee blocks both ι rules — `iotaListElimNil` needs
`var → listNil`, `iotaListElimCons` needs `var → listCons _ _` —
discharged via `var_inv` on each ι arm. -/
theorem RawTerm.listElim_var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope)
    {nilBranch : RawTerm scope}
    (nilIsSN : RawTerm.isStronglyNormalizing nilBranch) :
    ∀ {consBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing consBranch →
      RawTerm.isStronglyNormalizing
        (RawTerm.listElim (RawTerm.var position) nilBranch consBranch) := by
  induction nilIsSN with
  | intro currentNil _ nilIH =>
    intro consBranch consIsSN
    induction consIsSN with
    | intro currentCons consClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.listElim (RawTerm.var position) currentNil currentCons) ?_
      intro target progressStep
      rcases RawStep.par.listElim_inv progressStep.1 with
        ⟨scrutineeTarget, nilTarget, consTarget, targetEq,
          scrutineeStep, nilStep, consStep⟩
        | (⟨nilTarget, _targetEq, scrutineeStep, _nilStep⟩
          | ⟨headRaw, tailRaw, consTarget,
              _targetEq, scrutineeStep, _consStep⟩)
      · have scrutineeEq :
            scrutineeTarget = RawTerm.var position :=
          (RawStep.par.var_inv scrutineeStep)
        subst scrutineeEq
        subst targetEq
        by_cases nilEq : currentNil = nilTarget
        · subst nilEq
          have consDistinct :
              currentCons ≠ consTarget := fun consEq =>
            progressStep.2 (congrArg
              (RawTerm.listElim (RawTerm.var position) currentNil) consEq)
          exact innerIH consTarget ⟨consStep, consDistinct⟩
        · have nilProgress :
              RawStep.parProgress currentNil nilTarget :=
            ⟨nilStep, nilEq⟩
          by_cases consEq : currentCons = consTarget
          · subst consEq
            exact nilIH nilTarget nilProgress
              (RawTerm.isStronglyNormalizing.intro currentCons consClosure)
          · exact nilIH nilTarget nilProgress
              (consClosure consTarget ⟨consStep, consEq⟩)
      · exact (by
          have varEqNil :
              RawTerm.var position = RawTerm.listNil :=
            (RawStep.par.var_inv scrutineeStep).symm
          nomatch varEqNil)
      · exact (by
          have varEqCons :
              RawTerm.var position = RawTerm.listCons headRaw tailRaw :=
            (RawStep.par.var_inv scrutineeStep).symm
          nomatch varEqCons)

/-- List elimination with a neutral scrutinee is strongly normalizing
when the scrutinee and both branches are strongly normalizing.

The list ι arms are impossible because every parallel reduct of the
neutral scrutinee stays neutral, and neutral terms are never `listNil`
or `listCons` shaped.  The congruence arm recurses lexicographically on
scrutinee, nil-branch, and cons-branch progress. -/
theorem RawTerm.listElim_neutral_isStronglyNormalizing {scope : Nat}
    {scrutineeRaw nilBranch consBranch : RawTerm scope}
    (scrutineeIsNeutral : RawTerm.IsNeutral scrutineeRaw)
    (scrutineeIsSN : RawTerm.isStronglyNormalizing scrutineeRaw)
    (nilIsSN : RawTerm.isStronglyNormalizing nilBranch)
    (consIsSN : RawTerm.isStronglyNormalizing consBranch) :
    RawTerm.isStronglyNormalizing
      (RawTerm.listElim scrutineeRaw nilBranch consBranch) := by
  induction scrutineeIsSN generalizing nilBranch consBranch with
  | intro currentScrutinee _ scrutineeInduction =>
    induction nilIsSN generalizing consBranch with
    | intro currentNil nilClosure nilInduction =>
      induction consIsSN with
      | intro currentCons consClosure consInduction =>
        refine RawTerm.isStronglyNormalizing.intro
          (RawTerm.listElim currentScrutinee currentNil currentCons) ?_
        intro target progressStep
        rcases RawStep.par.listElim_inv progressStep.1 with
          ⟨scrutineeTarget, nilTarget, consTarget, targetEq,
            scrutineeStep, nilStep, consStep⟩
          | (⟨_nilTarget, _targetEq, scrutineeStep, _nilStep⟩
            | ⟨headRaw, tailRaw, _consTarget, _targetEq,
                scrutineeStep, _consStep⟩)
        · subst targetEq
          have scrutineeTargetIsNeutral :
              RawTerm.IsNeutral scrutineeTarget :=
            RawTerm.IsNeutral.par_preserves scrutineeIsNeutral
              scrutineeStep
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
          by_cases scrutineeEq : currentScrutinee = scrutineeTarget
          · subst scrutineeEq
            by_cases nilEq : currentNil = nilTarget
            · subst nilEq
              by_cases consEq : currentCons = consTarget
              · subst consEq
                exact (progressStep.2 rfl).elim
              · exact consInduction consTarget ⟨consStep, consEq⟩
            · exact nilInduction nilTarget ⟨nilStep, nilEq⟩
                consTargetIsSN
          · exact scrutineeInduction scrutineeTarget
              ⟨scrutineeStep, scrutineeEq⟩
              scrutineeTargetIsNeutral nilTargetIsSN consTargetIsSN
        · exact (RawTerm.IsNeutral.not_listNil
            (RawTerm.IsNeutral.par_preserves scrutineeIsNeutral
              scrutineeStep) rfl).elim
        · exact (RawTerm.IsNeutral.not_listCons
            (RawTerm.IsNeutral.par_preserves scrutineeIsNeutral
              scrutineeStep)
            (headRaw := headRaw) (tailRaw := tailRaw) rfl).elim

/-- **K12.20.AW.2 neutral optionMatch SN preservation**.  Sister
to `listElim_var`; option-eliminator with variable scrutinee.
Same proof shape; ι rules need `var → optionNone` and
`var → optionSome _`. -/
theorem RawTerm.optionMatch_var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope)
    {noneBranch : RawTerm scope}
    (noneIsSN : RawTerm.isStronglyNormalizing noneBranch) :
    ∀ {someBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing someBranch →
      RawTerm.isStronglyNormalizing
        (RawTerm.optionMatch (RawTerm.var position) noneBranch someBranch) := by
  induction noneIsSN with
  | intro currentNone _ noneIH =>
    intro someBranch someIsSN
    induction someIsSN with
    | intro currentSome someClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.optionMatch (RawTerm.var position) currentNone currentSome) ?_
      intro target progressStep
      rcases RawStep.par.optionMatch_inv progressStep.1 with
        ⟨scrutineeTarget, noneTarget, someTarget, targetEq,
          scrutineeStep, noneStep, someStep⟩
        | (⟨noneTarget, _targetEq, scrutineeStep, _noneStep⟩
          | ⟨valueRaw, someTarget, _targetEq, scrutineeStep, _someStep⟩)
      · have scrutineeEq :
            scrutineeTarget = RawTerm.var position :=
          (RawStep.par.var_inv scrutineeStep)
        subst scrutineeEq
        subst targetEq
        by_cases noneEq : currentNone = noneTarget
        · subst noneEq
          have someDistinct :
              currentSome ≠ someTarget := fun someEq =>
            progressStep.2 (congrArg
              (RawTerm.optionMatch (RawTerm.var position) currentNone) someEq)
          exact innerIH someTarget ⟨someStep, someDistinct⟩
        · have noneProgress :
              RawStep.parProgress currentNone noneTarget :=
            ⟨noneStep, noneEq⟩
          by_cases someEq : currentSome = someTarget
          · subst someEq
            exact noneIH noneTarget noneProgress
              (RawTerm.isStronglyNormalizing.intro currentSome someClosure)
          · exact noneIH noneTarget noneProgress
              (someClosure someTarget ⟨someStep, someEq⟩)
      · exact (by
          have varEqNone :
              RawTerm.var position = RawTerm.optionNone :=
            (RawStep.par.var_inv scrutineeStep).symm
          nomatch varEqNone)
      · exact (by
          have varEqSome :
              RawTerm.var position = RawTerm.optionSome valueRaw :=
            (RawStep.par.var_inv scrutineeStep).symm
          nomatch varEqSome)

/-- Option matching with a neutral scrutinee is strongly normalizing
when the scrutinee and both branches are strongly normalizing.

The option ι arms are impossible because every parallel reduct of the
neutral scrutinee stays neutral, and neutral terms are never
`optionNone` or `optionSome` shaped.  The congruence arm recurses across
scrutinee, none-branch, and some-branch progress. -/
theorem RawTerm.optionMatch_neutral_isStronglyNormalizing {scope : Nat}
    {scrutineeRaw noneBranch someBranch : RawTerm scope}
    (scrutineeIsNeutral : RawTerm.IsNeutral scrutineeRaw)
    (scrutineeIsSN : RawTerm.isStronglyNormalizing scrutineeRaw)
    (noneIsSN : RawTerm.isStronglyNormalizing noneBranch)
    (someIsSN : RawTerm.isStronglyNormalizing someBranch) :
    RawTerm.isStronglyNormalizing
      (RawTerm.optionMatch scrutineeRaw noneBranch someBranch) := by
  induction scrutineeIsSN generalizing noneBranch someBranch with
  | intro currentScrutinee _ scrutineeInduction =>
    induction noneIsSN generalizing someBranch with
    | intro currentNone noneClosure noneInduction =>
      induction someIsSN with
      | intro currentSome someClosure someInduction =>
        refine RawTerm.isStronglyNormalizing.intro
          (RawTerm.optionMatch currentScrutinee currentNone currentSome) ?_
        intro target progressStep
        rcases RawStep.par.optionMatch_inv progressStep.1 with
          ⟨scrutineeTarget, noneTarget, someTarget, targetEq,
            scrutineeStep, noneStep, someStep⟩
          | (⟨_noneTarget, _targetEq, scrutineeStep, _noneStep⟩
            | ⟨valueRaw, _someTarget, _targetEq,
                scrutineeStep, _someStep⟩)
        · subst targetEq
          have scrutineeTargetIsNeutral :
              RawTerm.IsNeutral scrutineeTarget :=
            RawTerm.IsNeutral.par_preserves scrutineeIsNeutral
              scrutineeStep
          have noneTargetIsSN :
              RawTerm.isStronglyNormalizing noneTarget := by
            by_cases noneEq : currentNone = noneTarget
            · subst noneEq
              exact RawTerm.isStronglyNormalizing.intro
                currentNone noneClosure
            · exact noneClosure noneTarget ⟨noneStep, noneEq⟩
          have someTargetIsSN :
              RawTerm.isStronglyNormalizing someTarget := by
            by_cases someEq : currentSome = someTarget
            · subst someEq
              exact RawTerm.isStronglyNormalizing.intro
                currentSome someClosure
            · exact someClosure someTarget ⟨someStep, someEq⟩
          by_cases scrutineeEq : currentScrutinee = scrutineeTarget
          · subst scrutineeEq
            by_cases noneEq : currentNone = noneTarget
            · subst noneEq
              by_cases someEq : currentSome = someTarget
              · subst someEq
                exact (progressStep.2 rfl).elim
              · exact someInduction someTarget ⟨someStep, someEq⟩
            · exact noneInduction noneTarget ⟨noneStep, noneEq⟩
                someTargetIsSN
          · exact scrutineeInduction scrutineeTarget
              ⟨scrutineeStep, scrutineeEq⟩
              scrutineeTargetIsNeutral noneTargetIsSN someTargetIsSN
        · exact (RawTerm.IsNeutral.not_optionNone
            (RawTerm.IsNeutral.par_preserves scrutineeIsNeutral
              scrutineeStep) rfl).elim
        · exact (RawTerm.IsNeutral.not_optionSome
            (RawTerm.IsNeutral.par_preserves scrutineeIsNeutral
              scrutineeStep)
            (valueRaw := valueRaw) rfl).elim

/-- **K12.20.AW.3 neutral eitherMatch SN preservation**.  Sister
to `listElim_var` / `optionMatch_var`; either-eliminator with
variable scrutinee.  Both ι rules carry a payload value (no
nullary constructor on either side), so both demand
`var → eitherInl _` / `var → eitherInr _` — both blocked by
`var_inv`. -/
theorem RawTerm.eitherMatch_var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope)
    {leftBranch : RawTerm scope}
    (leftIsSN : RawTerm.isStronglyNormalizing leftBranch) :
    ∀ {rightBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing rightBranch →
      RawTerm.isStronglyNormalizing
        (RawTerm.eitherMatch (RawTerm.var position) leftBranch rightBranch) := by
  induction leftIsSN with
  | intro currentLeft _ leftIH =>
    intro rightBranch rightIsSN
    induction rightIsSN with
    | intro currentRight rightClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.eitherMatch (RawTerm.var position)
          currentLeft currentRight) ?_
      intro target progressStep
      rcases RawStep.par.eitherMatch_inv progressStep.1 with
        ⟨scrutineeTarget, leftTarget, rightTarget, targetEq,
          scrutineeStep, leftStep, rightStep⟩
        | (⟨valueRaw, leftTarget, _targetEq, scrutineeStep, _leftStep⟩
          | ⟨valueRaw, rightTarget, _targetEq, scrutineeStep, _rightStep⟩)
      · have scrutineeEq :
            scrutineeTarget = RawTerm.var position :=
          (RawStep.par.var_inv scrutineeStep)
        subst scrutineeEq
        subst targetEq
        by_cases leftEq : currentLeft = leftTarget
        · subst leftEq
          have rightDistinct :
              currentRight ≠ rightTarget := fun rightEq =>
            progressStep.2 (congrArg
              (RawTerm.eitherMatch (RawTerm.var position) currentLeft) rightEq)
          exact innerIH rightTarget ⟨rightStep, rightDistinct⟩
        · have leftProgress :
              RawStep.parProgress currentLeft leftTarget :=
            ⟨leftStep, leftEq⟩
          by_cases rightEq : currentRight = rightTarget
          · subst rightEq
            exact leftIH leftTarget leftProgress
              (RawTerm.isStronglyNormalizing.intro currentRight rightClosure)
          · exact leftIH leftTarget leftProgress
              (rightClosure rightTarget ⟨rightStep, rightEq⟩)
      · exact (by
          have varEqInl :
              RawTerm.var position = RawTerm.eitherInl valueRaw :=
            (RawStep.par.var_inv scrutineeStep).symm
          nomatch varEqInl)
      · exact (by
          have varEqInr :
              RawTerm.var position = RawTerm.eitherInr valueRaw :=
            (RawStep.par.var_inv scrutineeStep).symm
          nomatch varEqInr)

/-- Either matching with a neutral scrutinee is strongly normalizing
when the scrutinee and both branches are strongly normalizing.

The either ι arms are impossible because every parallel reduct of the
neutral scrutinee stays neutral, and neutral terms are never
`eitherInl` or `eitherInr` shaped.  The congruence arm recurses across
scrutinee, left branch, and right branch progress. -/
theorem RawTerm.eitherMatch_neutral_isStronglyNormalizing {scope : Nat}
    {scrutineeRaw leftBranch rightBranch : RawTerm scope}
    (scrutineeIsNeutral : RawTerm.IsNeutral scrutineeRaw)
    (scrutineeIsSN : RawTerm.isStronglyNormalizing scrutineeRaw)
    (leftIsSN : RawTerm.isStronglyNormalizing leftBranch)
    (rightIsSN : RawTerm.isStronglyNormalizing rightBranch) :
    RawTerm.isStronglyNormalizing
      (RawTerm.eitherMatch scrutineeRaw leftBranch rightBranch) := by
  induction scrutineeIsSN generalizing leftBranch rightBranch with
  | intro currentScrutinee _ scrutineeInduction =>
    induction leftIsSN generalizing rightBranch with
    | intro currentLeft leftClosure leftInduction =>
      induction rightIsSN with
      | intro currentRight rightClosure rightInduction =>
        refine RawTerm.isStronglyNormalizing.intro
          (RawTerm.eitherMatch currentScrutinee currentLeft currentRight) ?_
        intro target progressStep
        rcases RawStep.par.eitherMatch_inv progressStep.1 with
          ⟨scrutineeTarget, leftTarget, rightTarget, targetEq,
            scrutineeStep, leftStep, rightStep⟩
          | (⟨valueRaw, _leftTarget, _targetEq,
                scrutineeStep, _leftStep⟩
            | ⟨valueRaw, _rightTarget, _targetEq,
                scrutineeStep, _rightStep⟩)
        · subst targetEq
          have scrutineeTargetIsNeutral :
              RawTerm.IsNeutral scrutineeTarget :=
            RawTerm.IsNeutral.par_preserves scrutineeIsNeutral
              scrutineeStep
          have leftTargetIsSN :
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
          by_cases scrutineeEq : currentScrutinee = scrutineeTarget
          · subst scrutineeEq
            by_cases leftEq : currentLeft = leftTarget
            · subst leftEq
              by_cases rightEq : currentRight = rightTarget
              · subst rightEq
                exact (progressStep.2 rfl).elim
              · exact rightInduction rightTarget ⟨rightStep, rightEq⟩
            · exact leftInduction leftTarget ⟨leftStep, leftEq⟩
                rightTargetIsSN
          · exact scrutineeInduction scrutineeTarget
              ⟨scrutineeStep, scrutineeEq⟩
              scrutineeTargetIsNeutral leftTargetIsSN rightTargetIsSN
        · exact (RawTerm.IsNeutral.not_eitherInl
            (RawTerm.IsNeutral.par_preserves scrutineeIsNeutral
              scrutineeStep)
            (valueRaw := valueRaw) rfl).elim
        · exact (RawTerm.IsNeutral.not_eitherInr
            (RawTerm.IsNeutral.par_preserves scrutineeIsNeutral
              scrutineeStep)
            (valueRaw := valueRaw) rfl).elim


end LeanFX2
