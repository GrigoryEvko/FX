import FX1Poly.Typed.HasTypeDescPiInversion
import FX1Poly.Typed.HasTypeDescPiSubstitution
import FX1Poly.Typed.WfContextDescPi

/-! # FX1Poly/Typed/HasTypeDescPiApplication — the dependent-eliminator OUTPUT is a grown type
    (the validity heart of Π-elimination / Σ-projection, for the GROWN engine).

The grown analogue of `HasTypeDescApplication`: a dependent eliminator's output type is the
codomain/motive instantiated at the eliminated value (`subst0 codomainCode argument`), and this file
proves that output is itself a well-formed grown type.  It composes the grown Π/Σ-code inversion
(`inversionPiCodeComponents` — its codomain is a grown type under the domain binder) with the grown
β-engine (`substituteUnderBinding` — instantiate that codomain at the argument); the resulting
universe classifier `subst0 (universeCodeCell ..) argument` IS the universe code by the
`subst0`/`subst_universeCodeCell` defeq, closing the `IsTypeDescPi` existential.

## Why the type-former well-formedness is a HYPOTHESIS, not derived

The FORMATION `piApplicationOutputIsType` derives "the Π-code is a type" from the function term's
typing via validity (the grown `classifierIsTypeDescPi`).  Here the type-former's well-formedness
(`IsTypeDescPi (piTyCodeCell ..)`) is taken as a HYPOTHESIS instead, for LAYERING: this file is
UPSTREAM of grown validity (`HasTypeDescPiClassifierValidity.classifierIsTypeDescPi` consumes
`piCodeInstantiationIsType`'s twin in its `piElim` arm), so it cannot call validity without an import
cycle.
The hypothesis IS the genuine output-validity obligation, and it is exactly the witness validity /
subject-reduction / canonicity carry in hand (they hold the eliminated value's type, hence its
well-formedness), so the decoupling costs nothing.

## Zero-axiom

Composition of `inversionPiCodeComponents` (zero-axiom) + `substituteUnderBinding` (zero-axiom) + the
`subst0`/`subst_universeCodeCell` defeq.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Audit-gated.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- The output type of grown Π-ELIMINATION is a well-formed grown type: if `Π domainCode. codomainCode`
is a grown type and `argument : domainCode`, then `codomainCode[argument]` (the application's result
type, `subst0 codomainCode argument`) is a grown type.  The validity obligation of the grown `app`
rule — grown Π inversion (the codomain is a type under the domain binder) fed into the grown β-engine
substitution, the universe classifier landing by the `subst0`/`subst_universeCodeCell` defeq. -/
theorem HasTypeDescPi.piCodeInstantiationIsType {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {argument : RawTerm scope}
    (piIsType : IsTypeDescPi profile context (piTyCodeCell domainCode codomainCode))
    (argumentTyped : HasTypeDescPi profile context argument domainCode)
    (_wellFormed : WfContextDescPi context) :
    IsTypeDescPi profile context (RawTerm.subst0 codomainCode argument) := by
  obtain ⟨_piLevel, _piFlag, piTyped⟩ := piIsType
  obtain ⟨_domainLevel, codomainLevel, flag, _domainTyped, codomainTyped⟩ :=
    HasTypeDescPi.inversionPiCodeComponents piTyped
  have substituted :=
    HasTypeDescPi.substituteUnderBinding argument codomainTyped argumentTyped
  exact ⟨codomainLevel, flag, substituted⟩

/-- The output type of grown Σ-PROJECTION (the second projection) is a well-formed grown type — the
Σ mirror of `piCodeInstantiationIsType`, via `inversionSigmaCodeComponents`.  If `Σ domainCode.
codomainCode` is a grown type and `firstProjection : domainCode`, then `codomainCode[firstProjection]`
(`subst0 codomainCode firstProjection`) is a grown type. -/
theorem HasTypeDescPi.sigmaCodeInstantiationIsType {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {firstProjection : RawTerm scope}
    (sigmaIsType : IsTypeDescPi profile context (sigmaTyCodeCell domainCode codomainCode))
    (firstProjectionTyped : HasTypeDescPi profile context firstProjection domainCode)
    (_wellFormed : WfContextDescPi context) :
    IsTypeDescPi profile context (RawTerm.subst0 codomainCode firstProjection) := by
  obtain ⟨_sigmaLevel, _sigmaFlag, sigmaTyped⟩ := sigmaIsType
  obtain ⟨_domainLevel, codomainLevel, flag, _domainTyped, codomainTyped⟩ :=
    HasTypeDescPi.inversionSigmaCodeComponents sigmaTyped
  have substituted :=
    HasTypeDescPi.substituteUnderBinding firstProjection codomainTyped firstProjectionTyped
  exact ⟨codomainLevel, flag, substituted⟩

end FX1Poly.Typed
