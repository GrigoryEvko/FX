import FX1Poly.Typed.HasTypeDescPiCongruence
import FX1Poly.Typed.HasTypeDescPiBetaSR
import FX1Poly.Typed.WfContextDescPi
import FX1Poly.Core.StepInversion

/-! # FX1Poly/Typed/HasTypeDescPiSubjectReductionArms
    — the per-shape ROUTING arms of the grown-engine subject-reduction dispatcher (SN-055)

The SR dispatcher `HasTypeDescPi Γ s S → Step s s' → HasTypeDescPi Γ s' S` cases on the subject's head and the
firing `Step`, routing to the right SR congruence / β arm.  This file ships the two NON-former routing arms — λ
(introduction) and application (elimination) — each turning a `Step` AT that head into the SR conclusion, given
the children's SR threaded as recursive hypotheses.  They are the arms the eventual dispatcher's `piIntro` and
`piElim` typing cases invoke (the children's SR is supplied by the structural recursion on the typing
derivation).

  * **λ (`subjectReductionAtLam`)**: a λ has NO root redex — `Step.from_lam` shows the only `Step` is body
    congruence.  Route to `congLamBody` with the body's SR.
  * **application (`subjectReductionAtApp`)**: `Step.from_app`'s 3-way disjunction — β (→ `betaSubjectReduction`),
    function congruence (→ `congFunction` with the function's SR), or argument congruence (→ `congArgument` with
    the argument's SR + the one-step `Conv` the argument-output adjustment needs).

These arms are UNCONDITIONAL (no grown context-conversion bundle): only the genFormationPi former-DOMAIN arm
with a GROWN codomain needs that; the formation-codomain former case is already discharged
(`HasTypeDescPiFormerStepDomainFormationCodomain`).

## Zero-axiom verification

`Step.from_lam` / `Step.from_app` (the per-cell Step inversions) + the shipped cong arms + `betaSubjectReduction`
+ a one-step `Conv` (`StepStar.single` + `StepStar.refl`).  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **SR routing arm at a λ.**  A `Step (lamCell body) reduct` is necessarily body congruence (a λ heads no
redex), so — given the body's SR (`bodyPreserves`) — `reduct` is typed at the same classifier through
`congLamBody`.  The dispatcher's `piIntro` case. -/
theorem HasTypeDescPi.subjectReductionAtLam {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainAnn : RawTerm scope} {body : RawTerm (scope + 1)}
    {reduct : RawTerm scope} {classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context (lamCell domainAnn body) classifier)
    (step : Step (lamCell domainAnn body) reduct)
    (bodyPreserves : ∀ {bindingType : RawTerm scope} {bodyReduct bodyClassifier : RawTerm (scope + 1)},
      Step body bodyReduct →
        HasTypeDescPi profile (context.cons bindingType) body bodyClassifier →
          HasTypeDescPi profile (context.cons bindingType) bodyReduct bodyClassifier)
    (domainPreserves : ∀ {domainReduct : RawTerm scope},
      Step domainAnn domainReduct →
        HasTypeDescPi profile context (lamCell domainReduct body) classifier)
    (wellFormed : WfContextDescPi context) :
    HasTypeDescPi profile context reduct classifier := by
  rcases Step.from_lam step with
    ⟨domainAfter, reductEq, domainStep⟩ | ⟨bodyAfter, reductEq, bodyStep⟩
  · subst reductEq
    exact domainPreserves domainStep
  · subst reductEq
    exact HasTypeDescPi.congLamBody typed (fun bodyTyped => bodyPreserves bodyStep bodyTyped)
      wellFormed

/-- **SR routing arm at an application.**  `Step (appCell functionTerm argument) reduct` is one of: β-contraction
(→ `betaSubjectReduction`), function congruence (→ `congFunction` with the function's SR), or argument congruence
(→ `congArgument` with the argument's SR and the one-step `Conv argument argumentAfter`).  The dispatcher's
`piElim` case. -/
theorem HasTypeDescPi.subjectReductionAtApp {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {functionTerm argument reduct classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context (appCell functionTerm argument) classifier)
    (step : Step (appCell functionTerm argument) reduct)
    (functionPreserves : ∀ {functionReduct functionClassifier : RawTerm scope},
      Step functionTerm functionReduct →
        HasTypeDescPi profile context functionTerm functionClassifier →
          HasTypeDescPi profile context functionReduct functionClassifier)
    (argumentPreserves : ∀ {argumentReduct argumentClassifier : RawTerm scope},
      Step argument argumentReduct →
        HasTypeDescPi profile context argument argumentClassifier →
          HasTypeDescPi profile context argumentReduct argumentClassifier)
    (wellFormed : WfContextDescPi context) :
    HasTypeDescPi profile context reduct classifier := by
  rcases Step.from_app step with ⟨domainAnn, body, functionEq, reductEq⟩ |
      ⟨functionAfter, reductEq, functionStep⟩ | ⟨argumentAfter, reductEq, argumentStep⟩
  · subst functionEq
    subst reductEq
    exact HasTypeDescPi.betaSubjectReduction typed wellFormed
  · subst reductEq
    exact HasTypeDescPi.congFunction typed
      (fun functionTyped => functionPreserves functionStep functionTyped) wellFormed
  · subst reductEq
    exact HasTypeDescPi.congArgument typed
      (fun argumentTyped => argumentPreserves argumentStep argumentTyped)
      ⟨_, StepStar.single argumentStep, StepStar.refl _⟩ wellFormed

end FX1Poly.Typed
