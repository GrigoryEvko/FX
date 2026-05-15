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

/-- **K12.20.AC.2 optionNone SN preservation** — nullary value at
parametric Ty.optionType.  Same atomic shape as listNil. -/
theorem RawTerm.optionNone_isStronglyNormalizing {scope : Nat} :
    RawTerm.isStronglyNormalizing
      (RawTerm.optionNone : RawTerm scope) :=
  RawTerm.isStronglyNormalizing.intro
    (RawTerm.optionNone : RawTerm scope)
    (fun _ progressStep =>
      (progressStep.2 (RawStep.par.optionNone_inv progressStep.1).symm).elim)


end LeanFX2
