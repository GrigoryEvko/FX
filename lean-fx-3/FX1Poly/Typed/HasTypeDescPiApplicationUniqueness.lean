import FX1Poly.Typed.HasTypeDescPiAppInversion
import FX1Poly.Typed.ConvCodeInjectivity
import FX1Poly.Core.ConvSubstRename

/-! # FX1Poly/Typed/HasTypeDescPiApplicationUniqueness
    — per-subject type uniqueness at an APPLICATION position (the SN-052 COMPARE-step ingredient for app)

The bidirectional grown-engine checker (SN-052) checks an infer-mode subject by synthesizing its type and
comparing to the target via the SN-051 typed-`Conv` decider — the COMPARE step
(`HasTypeDescPi.decidableCheckOfInferredUniqueAtType`) whose completeness (`isFalse`) ingredient is
`uniqueAtSubject`: every type the subject can receive is `Conv` to the synthesized one.  The two leaf positions
(variable, universe-code) supply it via unconditional inversions (`HasTypeDescPiVariableInversion`,
`HasTypeDescPiUniverseCodeInversion`).  The APPLICATION position is different: an application's type is NOT
unconditionally unique — `appCell functionTerm argument` inherits the function's type non-uniqueness (a bare λ
in function position has many Π types, §`HasTypeDescPiTypingNonUnique`).

This file supplies the application's `uniqueAtSubject` PARAMETERIZED over the function's type uniqueness — the
honest factoring: application-of-λ is non-unique only BECAUSE the λ is, and GIVEN the function's type is unique
up to `Conv`, the application's dependent output `subst0 codomainCode argument` is too.  When the application
checker lands (gated on SR to expose the function's Π-head), the recursive function-inference supplies the
`functionUnique` premise and this lemma discharges `uniqueAtSubject` directly.

## Recipe (SR-free, pure inversion + Π-injectivity + subst0-congruence)

Invert the foreign application derivation (`invertApp`, #769) to recover its function-typing at
`piTyCodeCell otherDomain otherCodomain`, the argument-typing, and `Conv otherType (subst0 otherCodomain
argument)`.  `functionUnique` forces `Conv (piTyCodeCell domainCode codomainCode) (piTyCodeCell otherDomain
otherCodomain)`; `Conv.piTyCode_inj` projects the codomain `Conv`; `Conv.subst0` pushes it through the SAME
argument to `Conv (subst0 codomainCode argument) (subst0 otherCodomain argument)`; `Conv.trans` with the
inverted classifier `Conv` (`.sym`) closes the goal.

## Zero-axiom verification

`invertApp` + `Conv.piTyCode_inj` + `Conv.subst0` + the unconditional raw `Conv.trans` / `Conv.sym` /
`Conv.refl` (#714).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **Application-type uniqueness given function-type uniqueness.**  If the function's type is unique up to
`Conv` (`functionUnique` — every type `functionTerm` receives is `Conv` to `piTyCodeCell domainCode
codomainCode`), then every type the application `appCell functionTerm argument` receives is `Conv` to the
dependent output `RawTerm.subst0 codomainCode argument`.  This is exactly the `uniqueAtSubject` shape the
SN-052 COMPARE step consumes at an application — the per-subject uniqueness that, unlike the variable and
universe-code leaves, is CONDITIONAL (an application inherits the function's type non-uniqueness; a bare λ in
function position has many Π types). -/
theorem HasTypeDescPi.applicationTypeUniqueGivenFunction {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {functionTerm argument : RawTerm scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (functionUnique :
      ∀ {otherFunctionType : RawTerm scope},
        HasTypeDescPi profile context functionTerm otherFunctionType →
          Conv (piTyCodeCell domainCode codomainCode) otherFunctionType) :
    ∀ {otherType : RawTerm scope},
      HasTypeDescPi profile context (appCell functionTerm argument) otherType →
        Conv (RawTerm.subst0 codomainCode argument) otherType :=
  fun {_otherType} otherDeriv => by
    obtain ⟨_otherDomain, otherCodomain, otherFunctionTyped, _otherArgTyped, otherConv⟩ :=
      HasTypeDescPi.invertApp otherDeriv
    have piConv :
        Conv (piTyCodeCell domainCode codomainCode) (piTyCodeCell _otherDomain otherCodomain) :=
      functionUnique otherFunctionTyped
    obtain ⟨_domainConv, codomainConv⟩ := Conv.piTyCode_inj piConv
    have outputConv :
        Conv (RawTerm.subst0 codomainCode argument) (RawTerm.subst0 otherCodomain argument) :=
      Conv.subst0 codomainConv (Conv.refl argument)
    exact Conv.trans outputConv otherConv.sym

end FX1Poly.Typed
