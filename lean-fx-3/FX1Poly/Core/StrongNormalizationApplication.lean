import FX1Poly.Core.StrongNormalizationConstructors

/-! # Foundation/PolyCell/Core/StrongNormalizationApplication
    — strong normalization of an application descends to its function position

The reducibility-candidate CR1 for the (Kripke) ARROW needs the structural fact that a strongly
normalizing application `app f a` has a strongly normalizing function `f`: the standard Tait argument
proves a function in the arrow candidate is SN by applying it to a fresh variable (a neutral in the
domain) and reading SN back off the resulting application via THIS lemma.  It is also general-purpose SN
infrastructure (the converse direction of the shipped `isStronglyNormalizing_of_twoChildCong`, which lifts
children-SN to parent-SN; here we descend parent-SN to a child).

The proof is an accessibility pullback along the application's function congruence: a `Step f f'` lifts to
`Step (app f a) (app f' a)` (`appFunctionCongStep`, the generic `cong` + `StepChildren.here`), so the map
`f ↦ app f a` is a reduction simulation and `Acc` transfers backward (generalizing the application image so
the `Acc` recursor's induction hypothesis applies at each function reduct).

## Zero-axiom verification

`Acc.rec` induction + a structural `Eq` generalization (`Eq.rec`, not `propext`) + the `cong` /
`StepChildren.here` congruence.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega` (verified by `#print axioms` in scratch before landing).  Gated per declaration in
`FX1PolyAudit/AuditCoreSubstrate.lean`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
open StepStar

/-- The application cell `app functionTerm argument`. -/
abbrev applicationCell {scope : Nat} (functionTerm argument : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_app () (.childCons functionTerm (.childCons argument .childNil))

/-- **Stepping the function steps the application.**  The generic congruence `Step.cong` on the `gen_app`
generator, reducing the head child via `StepChildren.here`. -/
theorem appFunctionCongStep {scope : Nat} {functionTerm functionTerm' argument : RawTerm scope}
    (functionStep : Step functionTerm functionTerm') :
    Step (applicationCell functionTerm argument) (applicationCell functionTerm' argument) :=
  Step.cong .gen_app ()
    (StepChildren.here (.childCons argument .childNil : RawTermChildren [0] scope) functionStep)

/-- **Accessibility pullback (generalized over the application image).**  If `app functionTerm argument` is
accessible for the step-successor relation, so is `functionTerm` — each function reduct `functionTerm'`
maps to a reduct `app functionTerm' argument` accessible below the image, and the induction hypothesis
descends. -/
theorem isStronglyNormalizing_of_appFunction_aux {scope : Nat} (argument : RawTerm scope) :
    ∀ {appImage : RawTerm scope}, Acc StepSuccessor appImage →
      ∀ {functionTerm : RawTerm scope}, appImage = applicationCell functionTerm argument →
        Acc StepSuccessor functionTerm := by
  intro appImage accImage
  induction accImage with
  | intro _current _accPred ih =>
    intro functionTerm imageEq
    subst imageEq
    refine Acc.intro functionTerm (fun functionTerm' functionStep => ?_)
    exact ih (applicationCell functionTerm' argument) (appFunctionCongStep functionStep) rfl

/-- **An application's strong normalization descends to its function (CR1 ingredient).** -/
theorem isStronglyNormalizing_of_appFunction {scope : Nat} {functionTerm argument : RawTerm scope}
    (appTerminates : IsStronglyNormalizing (applicationCell functionTerm argument)) :
    IsStronglyNormalizing functionTerm :=
  isStronglyNormalizing_of_appFunction_aux argument appTerminates rfl

end FX1Poly.Core
