import FX1Poly.Typed.HasTypeDescPiAppInversion
import FX1Poly.Typed.HasTypeDescPiLamInversion
import FX1Poly.Typed.HasTypeDescPiSubstitution
import FX1Poly.Typed.HasTypeDescPiClassifierValidity
import FX1Poly.Typed.ConvCodeInjectivity
import FX1Poly.Core.ConvSubstRename

/-! # FX1Poly/Typed/HasTypeDescPiBetaSR — fully-general β subject reduction (TY-SR-β, #474)

The INVERTED β subject reduction for the grown engine: for ANY grown derivation of a β-redex
`appCell (lamCell body) argument` at `classifier` (and a well-formed context), the β-reduct
`RawTerm.subst0 body argument` is typed at the SAME `classifier`.  This is the preservation half of
subject reduction for the `Step.beta` rule, in the form the SR master dispatcher (#458) consumes
(`HasTypeDescPi Γ t T → Step t t' → HasTypeDescPi Γ t' T`, same `T`).

## Why this is the inverted form (vs the shipped `betaCoherence`)

`HasTypeDescPi.betaCoherence` already gives β preservation for a redex assembled FROM COMPONENTS
(`body`/`argument`/`domain`/`codomain` typings handed in) — both the redex and its reduct land at
`subst0 codomainCode argument`.  Its docstring flags the remaining gap: "the fully-general inverted SR
over an arbitrary `HasTypeDescPi` derivation modulo `conv` additionally needs Π-arm inversion".  That
Π-arm inversion is now shipped (`invertApp` + `invertLam`), so this file closes the gap: it INVERTS an
arbitrary redex derivation to recover the components, then retypes the reduct and converts it back to
the original `classifier`.

## The assembly (every ingredient shipped)

  1. `invertApp` the redex ⟹ `lamCell body : piTyCodeCell dom cod`, `argument : dom`,
     `Conv classifier (subst0 cod argument)`.
  2. `invertLam` the function ⟹ `body : cod'` under `cons dom'`, `dom' : Type@domLvl flag`,
     `Conv (piTyCodeCell dom cod) (piTyCodeCell dom' cod')`.
  3. `Conv.piTyCode_inj` ⟹ `Conv dom dom'` ∧ `Conv cod cod'`.
  4. `conv` `argument : dom` along `Conv dom dom'` (using `dom' : Type`) ⟹ `argument : dom'`.
  5. `substituteUnderBinding` (the grown β-engine) on `body : cod'` (under `dom'`) and `argument : dom'`
     ⟹ `subst0 body argument : subst0 cod' argument`.
  6. `Conv.subst0 (Conv cod' cod) (refl argument)` then `Conv.trans` with `(Conv classifier (subst0 cod
     argument)).sym` ⟹ `Conv (subst0 cod' argument) classifier`.
  7. validity (`classifierIsTypeDescPi`, the `WfContextDescPi` consumer) ⟹ `classifier : Type`, so the
     final `conv` retypes `subst0 body argument` at `classifier`.

## Zero-axiom verification

A composition of shipped zero-axiom results (`invertApp`, `invertLam`, `Conv.piTyCode_inj`,
`HasTypeDescPi.substituteUnderBinding`, `Conv.subst0`, `Conv.trans`/`Conv.sym`,
`HasTypeDescPi.classifierIsTypeDescPi`) + the grown `conv` rule.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Fully-general β subject reduction (TY-SR-β, #474).**  Any grown derivation of a β-redex
`appCell (lamCell body) argument` at `classifier`, over a well-formed context, has its β-reduct
`RawTerm.subst0 body argument` typed at the SAME `classifier`.  Inverts the redex (`invertApp` +
`invertLam`), reconciles the application's and the λ's domain/codomain by Π-`Conv`-injectivity,
retypes the reduct by the grown substitution engine, and converts back to `classifier` via validity.
The `Step.beta` case of the SR master dispatcher (#458). -/
theorem HasTypeDescPi.betaSubjectReduction {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainAnn : RawTerm scope} {body : RawTerm (scope + 1)} {argument classifier : RawTerm scope}
    (redexTyped :
      HasTypeDescPi profile context (appCell (lamCell domainAnn body) argument) classifier)
    (wellFormed : WfContextDescPi context) :
    HasTypeDescPi profile context (RawTerm.subst0 body argument) classifier := by
  obtain ⟨domainCode, codomainCode, functionTyped, argumentTyped, convClassifierToOutput⟩ :=
    redexTyped.invertApp
  obtain ⟨lamCodomainCode, lamDomainLevel, lamCodomainLevel, lamFlag,
      convPiToPi, lamDomainTyped, _lamCodomainTyped, bodyTyped⟩ :=
    functionTyped.invertLam
  obtain ⟨convDomain, convCodomain⟩ := Conv.piTyCode_inj convPiToPi
  have argumentTypedAtLamDomain :
      HasTypeDescPi profile context argument domainAnn :=
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

end FX1Poly.Typed
