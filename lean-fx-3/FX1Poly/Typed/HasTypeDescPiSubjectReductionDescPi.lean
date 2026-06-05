import FX1Poly.Typed.HasTypeDescPiBetaSR
import FX1Poly.Typed.HasTypeDescPiClassifierValidity
import FX1Poly.Typed.HasTypeDescPiSubjectReductionInlineArms

/-! # FX1Poly/Typed/HasTypeDescPiSubjectReductionDescPi
    — the function-space SR arms re-threaded over the GROWN well-formedness `WfContextDescPi`

The master subject-reduction dispatcher (SN-055 / SRD-1 / TG-3) inducts on a grown derivation and must EXTEND
well-formedness at each grown `piIntro` binder.  The `HasType`-based `WfContext` cannot reach there (no
`HasTypeDescPi → IsType` bridge), so the dispatcher must thread the grown `WfContextDescPi` (WFG-1), which DOES
extend at a grown binder (`WfContextDescPi.cons` + the binder's domain typing IS its `IsTypeDescPi`).  The two
function-space SR arms previously consumed `WfContext`; this file ships their `WfContextDescPi` twins, now that
grown classifier-validity `HasTypeDescPi.classifierIsTypeDescPi` (WFG-3) is available.

Each twin is a one-site swap — the lone `WfContext` use in both is the classifier-validity call (for the final
`conv`'s universe witness), every other step (inversion, `Conv.piTyCode_inj`, `substituteUnderBinding`,
`Conv.subst0`) is already well-formedness-free.  Since `WfContext → WfContextDescPi` (`ofWfContext`), these
twins SUBSUME the existing `WfContext` versions.

  * `HasTypeDescPi.betaSubjectReductionDescPi` — β-redex SR under `WfContextDescPi`: a `(λ.body) arg` typed at
    `classifier` reduces to `body[arg]` still typed at `classifier`.  Identical to `betaSubjectReduction` with
    `classifierIsTypeDesc` → `classifierIsTypeDescPi`.
  * `HasTypeDescPi.subjectReductionPiElimArmDescPi` — the dispatcher's application arm under `WfContextDescPi`:
    `Step.from_app`'s 3-way (β → `betaSubjectReductionDescPi`; function step → `piElim` + the function IH;
    argument step → `piElim` + the argument IH + the `Conv.subst0` output-move re-typed via
    `classifierIsTypeDescPi`).  Identical to `subjectReductionPiElimArm` with both `WfContext` calls swapped.

With these + the already-`WfContext`-free `subjectReductionPiIntroArm`, the dispatcher's function-space arms all
thread `WfContextDescPi`.  The remaining dispatcher residual is the former arms' `codomainReTyping` (the grown
context-conversion / GCC bundle, `#838`-`#843`) — a SEPARATE leg, not a well-formedness swap.

## Zero-axiom verification

`invertApp` / `invertLam` / `Conv.piTyCode_inj` / `substituteUnderBinding` / `Conv.trans` / `Conv.subst0` /
`Step.from_app` / `piElim` + the grown `classifierIsTypeDescPi`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **β-redex subject reduction under the grown well-formedness `WfContextDescPi`.**  A `(λ.body) arg` typed at
`classifier` reduces to `body[arg]`, still typed at `classifier`.  The `WfContextDescPi` twin of
`HasTypeDescPi.betaSubjectReduction`: every step is already well-formedness-free except the final classifier
universe witness, which now comes from the grown `classifierIsTypeDescPi`. -/
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
`classifierIsTypeDescPi`).  The `WfContextDescPi` twin of `HasTypeDescPi.subjectReductionPiElimArm`. -/
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
