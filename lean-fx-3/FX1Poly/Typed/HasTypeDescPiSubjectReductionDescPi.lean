import FX1Poly.Typed.HasTypeDescPiBetaSR
import FX1Poly.Typed.HasTypeDescPiClassifierValidity
import FX1Poly.Typed.HasTypeDescPiSubjectReductionInlineArms

/-! # FX1Poly/Typed/HasTypeDescPiSubjectReductionDescPi
    — the function-space SR arms re-threaded over the GROWN well-formedness `WfContextDescPi`

The master subject-reduction dispatcher inducts on a grown derivation and must EXTEND well-formedness at each
grown `piIntro` binder.  It threads the grown `WfContextDescPi`, which extends at a grown binder
(`WfContextDescPi.cons` + the binder's domain typing IS its `IsTypeDescPi`).  This file ships the two
function-space SR arms over `WfContextDescPi`, using grown classifier-validity
`HasTypeDescPi.classifierIsTypeDescPi`.

In each arm the lone `WfContextDescPi` use is the classifier-validity call (for the final `conv`'s universe
witness); every other step (inversion, `Conv.piTyCode_inj`, `substituteUnderBinding`, `Conv.subst0`) is
well-formedness-free.

  * `HasTypeDescPi.betaSubjectReductionDescPi` — β-redex SR under `WfContextDescPi`: a `(λ.body) arg` typed at
    `classifier` reduces to `body[arg]` still typed at `classifier`.
  * `HasTypeDescPi.subjectReductionPiElimArmDescPi` — the dispatcher's application arm under `WfContextDescPi`:
    `Step.from_app`'s 3-way (β → `betaSubjectReductionDescPi`; function step → `piElim` + the function IH;
    argument step → `piElim` + the argument IH + the `Conv.subst0` output-move re-typed via
    `classifierIsTypeDescPi`).

With these + the well-formedness-free `subjectReductionPiIntroArm`, the dispatcher's function-space arms all
thread `WfContextDescPi`.  The remaining dispatcher residual is the former arms' `codomainReTyping` (the grown
context-conversion bundle) — a SEPARATE leg.

## Zero-axiom verification

`invertApp` / `invertLam` / `Conv.piTyCode_inj` / `substituteUnderBinding` / `Conv.trans` / `Conv.subst0` /
`Step.from_app` / `piElim` + the grown `classifierIsTypeDescPi`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **β-redex subject reduction under the grown well-formedness `WfContextDescPi`.**  A `(λ.body) arg` typed at
`classifier` reduces to `body[arg]`, still typed at `classifier`.  The `WfContextDescPi` variant of
`HasTypeDescPi.betaSubjectReduction`: every step is well-formedness-free except the final classifier
universe witness, which comes from the grown `classifierIsTypeDescPi`. -/
theorem HasTypeDescPi.betaSubjectReductionDescPi {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {body : RawTerm (scope + 1)} {argument classifier : RawTerm scope}
    (redexTyped : HasTypeDescPi profile context (appCell (lamCell body) argument) classifier)
    (wellFormed : WfContextDescPi context) :
    HasTypeDescPi profile context (RawTerm.subst0 body argument) classifier := by
  obtain ⟨domainCode, codomainCode, functionTyped, argumentTyped, convClassifierToOutput⟩ :=
    redexTyped.invertApp
  obtain ⟨lamDomainCode, lamCodomainCode, lamDomainLevel, lamCodomainLevel, lamFlag,
      convPiToPi, lamDomainTyped, _lamCodomainTyped, bodyTyped⟩ :=
    functionTyped.invertLam
  obtain ⟨convDomain, convCodomain⟩ := Conv.piTyCode_inj convPiToPi
  have argumentTypedAtLamDomain :
      HasTypeDescPi profile context argument lamDomainCode :=
    HasTypeDescPi.conv lamDomainLevel lamFlag argumentTyped convDomain lamDomainTyped
  have reductTyped :
      HasTypeDescPi profile context (RawTerm.subst0 body argument)
        (RawTerm.subst0 lamCodomainCode argument) :=
    HasTypeDescPi.substituteUnderBinding argument bodyTyped argumentTypedAtLamDomain
  have convReductOutputToClassifier :
      Conv (RawTerm.subst0 lamCodomainCode argument) classifier :=
    Conv.trans (Conv.subst0 convCodomain.sym (Conv.refl argument)) convClassifierToOutput.sym
  obtain ⟨classifierLevel, classifierFlag, classifierTyped⟩ :=
    redexTyped.classifierIsTypeDescPi wellFormed
  exact HasTypeDescPi.conv classifierLevel classifierFlag reductTyped
    convReductOutputToClassifier classifierTyped

/-- **The dispatcher's application SR arm under the grown well-formedness `WfContextDescPi`.**  `Step.from_app`'s
three cases on `Step (appCell functionTerm argument) reduct`: β (→ `betaSubjectReductionDescPi`), function
congruence (→ `piElim` with the function IH), argument congruence (→ `piElim` with the argument IH, then the
dependent output `subst0 codomainCode argument` moved by `Conv.subst0` + `conv`, re-typed via the grown
`classifierIsTypeDescPi`).  The `WfContextDescPi` variant of `HasTypeDescPi.subjectReductionPiElimArm`. -/
theorem HasTypeDescPi.subjectReductionPiElimArmDescPi {profile : PolyProfile} {scope : Nat}
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
    exact HasTypeDescPi.betaSubjectReductionDescPi
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

end FX1Poly.Typed
