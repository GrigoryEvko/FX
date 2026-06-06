import FX1Poly.Typed.HasTypeDescPiBetaSR
import FX1Poly.Typed.HasTypeDescPiAppInversion
import FX1Poly.Typed.HasTypeDescPiFormerCongruence
import FX1Poly.Typed.HasTypeDescPiClassifierValidity
import FX1Poly.Core.StepInversion
import FX1Poly.Core.ConvSubstRename

/-! # FX1Poly/Typed/HasTypeDescPiSubjectReductionInlineArms
    — the ASSEMBLY-USABLE (specific-IH) λ / application SR arms of the dispatcher (SN-055)

The dispatcher proves SR by induction on the TYPING with the step-quantified motive
`∀ s', Step s s' → HasTypeDescPi Γ s' S`; the inductive hypothesis for each child is its SR AT THE CHILD'S
SPECIFIC CLASSIFIER (the one in the derivation).  This is a SUBTLER interface than the congruence arms
(`congLamBody`/`congFunction`/…), whose `childPreserves` is GENERAL over the classifier (`∀ classifier, …`) —
required because they recover the components by INVERSION (the classifier is existential), but NOT providable
from the specific IH.  So the dispatcher must reconstruct each arm DIRECTLY from the typing components plus the
specific child SR, not through the general-childPreserves congruence arms.

This file ships those direct reconstructions for the two function-space arms (`piIntro`/`piElim`), so the
dispatcher's induction calls them with the IHs verbatim:

  * **`subjectReductionPiIntroArm`** — `Step.from_lam` exposes the body step; rebuild via `piIntro` with the
    body's IH.  No classifier adjustment (the λ's type is fixed by its components).
  * **`subjectReductionPiElimArm`** — `Step.from_app`'s 3-way: β (→ `betaSubjectReduction`), function step
    (→ `piElim` with the function's IH), or argument step (→ `piElim` with the argument's IH, then the
    dependent output `subst0 codomainCode argument` is moved by `Conv.subst0` + the grown `conv`, since the
    argument changed).

## Zero-axiom verification

`Step.from_lam` / `Step.from_app` + `piIntro` / `piElim` / `betaSubjectReduction` + `Conv.subst0` + a one-step
`Conv` + `classifierIsTypeDescPi`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **Dispatcher λ arm (specific-IH).**  Given the λ's domain/codomain universe-typings and the body's SR at
its specific classifier, a `Step (lamCell body) reduct` rebuilds `reduct` at the λ's Π type via `piIntro`. -/
theorem HasTypeDescPi.subjectReductionPiIntroArm {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode body : RawTerm (scope + 1)}
    {domainLevel codomainLevel : LevelExpr} {flag : UniverseFlag} {reduct : RawTerm scope}
    (domainTyped : HasTypeDescPi profile context domainCode (universeCodeCell domainLevel flag))
    (codomainTyped : HasTypeDescPi profile (context.cons domainCode) codomainCode
      (universeCodeCell codomainLevel flag))
    (step : Step (lamCell body) reduct)
    (bodySR : ∀ {bodyReduct : RawTerm (scope + 1)},
      Step body bodyReduct →
        HasTypeDescPi profile (context.cons domainCode) bodyReduct codomainCode) :
    HasTypeDescPi profile context reduct (piTyCodeCell domainCode codomainCode) := by
  obtain ⟨bodyAfter, reductEq, bodyStep⟩ := Step.from_lam step
  subst reductEq
  exact HasTypeDescPi.piIntro domainLevel codomainLevel flag domainTyped codomainTyped (bodySR bodyStep)

/-- **Dispatcher application arm (specific-IH).**  Given the function's Π-typing, the argument's typing, and
each child's SR at its specific classifier, a `Step (appCell functionTerm argument) reduct` rebuilds `reduct`
at `subst0 codomainCode argument`: β via `betaSubjectReduction`, function congruence via `piElim`, argument
congruence via `piElim` + the `Conv.subst0` output-move + the grown `conv`. -/
theorem HasTypeDescPi.subjectReductionPiElimArm {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {functionTerm argument : RawTerm scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {reduct : RawTerm scope}
    (functionTyped : HasTypeDescPi profile context functionTerm (piTyCodeCell domainCode codomainCode))
    (argumentTyped : HasTypeDescPi profile context argument domainCode)
    (step : Step (appCell functionTerm argument) reduct)
    (functionSR : ∀ {functionReduct : RawTerm scope},
      Step functionTerm functionReduct →
        HasTypeDescPi profile context functionReduct (piTyCodeCell domainCode codomainCode))
    (argumentSR : ∀ {argumentReduct : RawTerm scope},
      Step argument argumentReduct → HasTypeDescPi profile context argumentReduct domainCode)
    (wellFormed : WfContextDescPi context) :
    HasTypeDescPi profile context reduct (RawTerm.subst0 codomainCode argument) := by
  rcases Step.from_app step with ⟨body, functionEq, reductEq⟩ |
      ⟨functionAfter, reductEq, functionStep⟩ | ⟨argumentAfter, reductEq, argumentStep⟩
  · subst functionEq
    subst reductEq
    exact HasTypeDescPi.betaSubjectReduction
      (HasTypeDescPi.piElim functionTyped argumentTyped) wellFormed
  · subst reductEq
    exact HasTypeDescPi.piElim (functionSR functionStep) argumentTyped
  · subst reductEq
    have rebuilt :
        HasTypeDescPi profile context (appCell functionTerm argumentAfter)
          (RawTerm.subst0 codomainCode argumentAfter) :=
      HasTypeDescPi.piElim functionTyped (argumentSR argumentStep)
    have convMovedOutput :
        Conv (RawTerm.subst0 codomainCode argumentAfter) (RawTerm.subst0 codomainCode argument) :=
      Conv.subst0 (Conv.refl codomainCode)
        ⟨argumentAfter, StepStar.refl _, StepStar.single argumentStep⟩
    obtain ⟨classifierLevel, classifierFlag, classifierTyped⟩ :=
      (HasTypeDescPi.piElim functionTyped argumentTyped).classifierIsTypeDescPi wellFormed
    exact HasTypeDescPi.conv classifierLevel classifierFlag rebuilt convMovedOutput classifierTyped

/-- **Dispatcher Π-former arm (specific-IH).**  Given the components' universe-typings, each child's SR at its
specific universe, and the codomain re-typing under a stepped domain, a `Step (piTyCodeCell domainCode
codomainCode) reduct` rebuilds `reduct` at the canonical `Type@(lmax domainLevel codomainLevel)` via
`piFormationViaGenArm` — domain step uses `domainSR` + `codomainReTyping`; codomain step uses `codomainSR`. -/
theorem HasTypeDescPi.subjectReductionPiFormerArm {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel codomainLevel : LevelExpr} {flag : UniverseFlag} {reduct : RawTerm scope}
    (domainTyped : HasTypeDescPi profile context domainCode (universeCodeCell domainLevel flag))
    (codomainTyped : HasTypeDescPi profile (context.cons domainCode) codomainCode
      (universeCodeCell codomainLevel flag))
    (step : Step (piTyCodeCell domainCode codomainCode) reduct)
    (domainSR : ∀ {domainReduct : RawTerm scope},
      Step domainCode domainReduct →
        HasTypeDescPi profile context domainReduct (universeCodeCell domainLevel flag))
    (codomainSR : ∀ {codomainReduct : RawTerm (scope + 1)},
      Step codomainCode codomainReduct →
        HasTypeDescPi profile (context.cons domainCode) codomainReduct
          (universeCodeCell codomainLevel flag))
    (codomainReTyping : ∀ {domainReduct : RawTerm scope},
      Step domainCode domainReduct →
        HasTypeDescPi profile (context.cons domainCode) codomainCode
            (universeCodeCell codomainLevel flag) →
          HasTypeDescPi profile (context.cons domainReduct) codomainCode
            (universeCodeCell codomainLevel flag)) :
    HasTypeDescPi profile context reduct
      (universeCodeCell (LevelExpr.lmax domainLevel codomainLevel) flag) := by
  rcases Step.from_piTyCode step with ⟨domainAfter, reductEq, domainStep⟩ |
      ⟨codomainAfter, reductEq, codomainStep⟩
  · subst reductEq
    exact HasTypeDescPi.piFormationViaGenArm context domainAfter codomainCode domainLevel
      codomainLevel flag (domainSR domainStep) (codomainReTyping domainStep codomainTyped)
  · subst reductEq
    exact HasTypeDescPi.piFormationViaGenArm context domainCode codomainAfter domainLevel
      codomainLevel flag domainTyped (codomainSR codomainStep)

/-- **Dispatcher Σ-former arm (specific-IH)** — the Σ dual of `subjectReductionPiFormerArm`, via
`Step.from_sigmaTyCode` + `sigmaFormationViaGenArm`. -/
theorem HasTypeDescPi.subjectReductionSigmaFormerArm {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel codomainLevel : LevelExpr} {flag : UniverseFlag} {reduct : RawTerm scope}
    (domainTyped : HasTypeDescPi profile context domainCode (universeCodeCell domainLevel flag))
    (codomainTyped : HasTypeDescPi profile (context.cons domainCode) codomainCode
      (universeCodeCell codomainLevel flag))
    (step : Step (sigmaTyCodeCell domainCode codomainCode) reduct)
    (domainSR : ∀ {domainReduct : RawTerm scope},
      Step domainCode domainReduct →
        HasTypeDescPi profile context domainReduct (universeCodeCell domainLevel flag))
    (codomainSR : ∀ {codomainReduct : RawTerm (scope + 1)},
      Step codomainCode codomainReduct →
        HasTypeDescPi profile (context.cons domainCode) codomainReduct
          (universeCodeCell codomainLevel flag))
    (codomainReTyping : ∀ {domainReduct : RawTerm scope},
      Step domainCode domainReduct →
        HasTypeDescPi profile (context.cons domainCode) codomainCode
            (universeCodeCell codomainLevel flag) →
          HasTypeDescPi profile (context.cons domainReduct) codomainCode
            (universeCodeCell codomainLevel flag)) :
    HasTypeDescPi profile context reduct
      (universeCodeCell (LevelExpr.lmax domainLevel codomainLevel) flag) := by
  rcases Step.from_sigmaTyCode step with ⟨domainAfter, reductEq, domainStep⟩ |
      ⟨codomainAfter, reductEq, codomainStep⟩
  · subst reductEq
    exact HasTypeDescPi.sigmaFormationViaGenArm context domainAfter codomainCode domainLevel
      codomainLevel flag (domainSR domainStep) (codomainReTyping domainStep codomainTyped)
  · subst reductEq
    exact HasTypeDescPi.sigmaFormationViaGenArm context domainCode codomainAfter domainLevel
      codomainLevel flag domainTyped (codomainSR codomainStep)

end FX1Poly.Typed
