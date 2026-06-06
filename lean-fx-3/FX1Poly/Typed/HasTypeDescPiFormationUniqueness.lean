import FX1Poly.Typed.HasTypeDescPiFormerInversion
import FX1Poly.Typed.HasTypeDecidableConv
import FX1Poly.Core.RawConfluence

/-! # FX1Poly/Typed/HasTypeDescPiFormationUniqueness
    — per-subject type uniqueness at a Π/Σ-FORMATION position (the SN-052 COMPARE-step ingredient for formers)

The bidirectional grown-engine checker (SN-052) checks an infer-mode subject by synthesizing its type and
comparing to the target via the SN-051 typed-`Conv` decider; the COMPARE step
(`HasTypeDescPi.decidableCheckOfInferredUniqueAtType`) consumes a per-subject UNIQUENESS witness
(`uniqueAtSubject`).  The leaf positions (variable, universe-code) supply it unconditionally; the application
position supplies it CONDITIONALLY on the function's type-uniqueness (`HasTypeDescPiApplicationUniqueness`).

The Π/Σ-FORMATION positions (`piTyCodeCell` / `sigmaTyCodeCell`) are the same shape as the application: a
former's type is `universeCodeCell (lmaxAll [domainLevel, codomainLevel]) flag`, whose level/flag are pinned by
the COMPONENTS' types — so the former's type is unique up to `Conv` exactly when the components' types are.
This file supplies that uniqueness PARAMETERIZED over the domain's and codomain's type-uniqueness, the honest
factoring (a former's components are arbitrary grown types, themselves non-unique in general).  When the
formation checker lands, the recursive component-inference delivers the `domainUnique` / `codomainUnique`
premises and these lemmas discharge `uniqueAtSubject` directly.

## Recipe (SR-free, pure former-inversion + universe-code injectivity)

`invertPiTyCode` (resp. `invertSigmaTyCode`) inverts the foreign former derivation to recover the components'
universe-typings at `(otherDomainLevel, otherFlag)` / `(otherCodomainLevel, otherFlag)` (the former inversion
forces BOTH components at the SAME `flag`) and `Conv otherType (universeCodeCell (lmaxAll [otherDomainLevel,
otherCodomainLevel]) otherFlag)`.  `domainUnique` / `codomainUnique` force the components' levels/flags via
`levelFlag_eq_of_conv_universeCodeCell` (SYNTACTIC `LevelExpr`/`UniverseFlag` equality — universe codes are
normal, so `Conv` is structural); substituting aligns the two output universe codes, and the inverted
classifier `Conv` (`.sym`) closes the goal.

## Zero-axiom verification

`invertPiTyCode` / `invertSigmaTyCode` + `levelFlag_eq_of_conv_universeCodeCell` + `subst` + the unconditional
raw `Conv.sym` (#714).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **Π-formation type uniqueness given component type-uniqueness.**  If the domain's and codomain's types are
unique up to `Conv` (`domainUnique` / `codomainUnique`), then every type the Π-code `piTyCodeCell domainCode
codomainCode` receives is `Conv` to its formation output `universeCodeCell (lmaxAll [domainLevel,
codomainLevel]) flag` — the `uniqueAtSubject` shape the SN-052 COMPARE step consumes at a Π-formation
position. -/
theorem HasTypeDescPi.piFormationTypeUniqueGivenComponents {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel codomainLevel : LevelExpr} {flag : UniverseFlag}
    (_wellFormed : WfContext context)
    (domainUnique :
      ∀ {otherDomainType : RawTerm scope},
        HasTypeDescPi profile context domainCode otherDomainType →
          Conv (universeCodeCell domainLevel flag) otherDomainType)
    (codomainUnique :
      ∀ {otherCodomainType : RawTerm (scope + 1)},
        HasTypeDescPi profile (context.cons domainCode) codomainCode otherCodomainType →
          Conv (universeCodeCell codomainLevel flag) otherCodomainType) :
    ∀ {otherType : RawTerm scope},
      HasTypeDescPi profile context (piTyCodeCell domainCode codomainCode) otherType →
        Conv (universeCodeCell (lmaxAll [domainLevel, codomainLevel]) flag) otherType :=
  fun {_otherType} otherDeriv => by
    obtain ⟨_otherDomainLevel, _otherCodomainLevel, _otherFlag,
            otherDomainTyped, otherCodomainTyped, otherConv⟩ :=
      HasTypeDescPi.invertPiTyCode otherDeriv
    obtain ⟨domainLevelEq, domainFlagEq⟩ :=
      levelFlag_eq_of_conv_universeCodeCell (context := context) (domainUnique otherDomainTyped)
    obtain ⟨codomainLevelEq, _codomainFlagEq⟩ :=
      levelFlag_eq_of_conv_universeCodeCell (context := context.cons domainCode)
        (codomainUnique otherCodomainTyped)
    subst domainLevelEq
    subst codomainLevelEq
    subst domainFlagEq
    exact otherConv.sym

/-- **Σ-formation type uniqueness given component type-uniqueness** — the Σ dual of
`piFormationTypeUniqueGivenComponents`, identical recipe over `sigmaTyCodeCell` and `invertSigmaTyCode`. -/
theorem HasTypeDescPi.sigmaFormationTypeUniqueGivenComponents {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel codomainLevel : LevelExpr} {flag : UniverseFlag}
    (_wellFormed : WfContext context)
    (domainUnique :
      ∀ {otherDomainType : RawTerm scope},
        HasTypeDescPi profile context domainCode otherDomainType →
          Conv (universeCodeCell domainLevel flag) otherDomainType)
    (codomainUnique :
      ∀ {otherCodomainType : RawTerm (scope + 1)},
        HasTypeDescPi profile (context.cons domainCode) codomainCode otherCodomainType →
          Conv (universeCodeCell codomainLevel flag) otherCodomainType) :
    ∀ {otherType : RawTerm scope},
      HasTypeDescPi profile context (sigmaTyCodeCell domainCode codomainCode) otherType →
        Conv (universeCodeCell (lmaxAll [domainLevel, codomainLevel]) flag) otherType :=
  fun {_otherType} otherDeriv => by
    obtain ⟨_otherDomainLevel, _otherCodomainLevel, _otherFlag,
            otherDomainTyped, otherCodomainTyped, otherConv⟩ :=
      HasTypeDescPi.invertSigmaTyCode otherDeriv
    obtain ⟨domainLevelEq, domainFlagEq⟩ :=
      levelFlag_eq_of_conv_universeCodeCell (context := context) (domainUnique otherDomainTyped)
    obtain ⟨codomainLevelEq, _codomainFlagEq⟩ :=
      levelFlag_eq_of_conv_universeCodeCell (context := context.cons domainCode)
        (codomainUnique otherCodomainTyped)
    subst domainLevelEq
    subst codomainLevelEq
    subst domainFlagEq
    exact otherConv.sym

end FX1Poly.Typed
