import LeanFX2.Reducibility.NeutralSNIntro.Modal

/-! # LeanFX2.Reducibility.NeutralSNIntro.Lists

`listCons` / `listNil` SN preservation + the binary
`listElim_listNil` / `listElim_listCons` ι-witnesses, plus
`optionNone` / `subsume` + `optionMatch_optionNone` ι-witness
(raw + typed).

## Root status

Layer 3 metatheory leaf.  K12.20.C ctor introduction SN preservation
for the list / option families. -/

namespace LeanFX2


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


end LeanFX2
