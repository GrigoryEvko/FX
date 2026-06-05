import FX1Poly.Typed.HasTypeDescPiClassifierValidity

/-! # FX1Poly/Typed/HasTypeDescPiFunctionComponentValidity
    — the function-component validity presuppositions for the grown engine: a function's DOMAIN and CODOMAIN are
      types

A standard well-formedness presupposition of dependent type theory: if `function : Π(domain). codomain` is
grown-typed in a well-formed context, then the `domain` is a type and the `codomain` is a type under the domain
binder.  These are the "validity of the Π components extracted from a function" lemmas — distinct from the Π-CODE
inversions (`inversionPiCodeComponentsUnconditional`, which invert a `piTyCodeCell` SUBJECT): here the Π type is
the function's CLASSIFIER, reached through grown classifier-validity.

  * `HasTypeDescPi.functionDomainIsType` — a `function : Π(domain). codomain` has `domain : Type`.
  * `HasTypeDescPi.functionCodomainIsType` — and `codomain : Type` under `context.cons domain`.

Both compose two shipped pieces with no new induction: `HasTypeDescPi.classifierIsTypeDescPi` (WFG-3 — the
function's classifier `Π(domain). codomain` is a grown type) feeds its universe witness to
`HasTypeDescPi.inversionPiCodeComponentsUnconditional` (the well-formedness-free Π-code component inversion),
whose two conjuncts ARE the domain and codomain typings.  The `WfContextDescPi` premise is exactly the one
`classifierIsTypeDescPi` consumes; the inversion adds none.

These are the load-bearing presuppositions the subject-reduction congruence arms and the grown context-conversion
`piElim` arm (GCC-5, the SN-055 residual) need — to context-convert / re-type a function's domain and codomain,
one first needs them to BE types.  Named here so those developments cite a presupposition rather than re-derive
the `classifierIsTypeDescPi ∘ inversionPiCodeComponentsUnconditional` composite at each site.

## Zero-axiom verification

Two `obtain`-destructurings of the shipped `classifierIsTypeDescPi` and `inversionPiCodeComponentsUnconditional`,
re-bundled as `IsTypeDescPi` (`∃ level flag, … (universeCodeCell level flag)`).  No new recursion.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **A function's domain is a type.**  If `function : Π(domainCode). codomainCode` is grown-typed in a
well-formed context, then `domainCode` is a grown type.  Grown classifier-validity exposes the function's Π
classifier as a type (its universe witness); the well-formedness-free Π-code component inversion reads off the
domain's typing. -/
theorem HasTypeDescPi.functionDomainIsType {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {function : RawTerm scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (functionTyped : HasTypeDescPi profile context function (piTyCodeCell domainCode codomainCode))
    (wellFormed : WfContextDescPi context) :
    IsTypeDescPi profile context domainCode := by
  obtain ⟨_piLevel, _piFlag, piTyped⟩ := functionTyped.classifierIsTypeDescPi wellFormed
  obtain ⟨domainLevel, _codomainLevel, flag, domainTyped, _codomainTyped⟩ :=
    HasTypeDescPi.inversionPiCodeComponentsUnconditional piTyped
  exact ⟨domainLevel, flag, domainTyped⟩

/-- **A function's codomain is a type under the domain binder.**  If `function : Π(domainCode). codomainCode` is
grown-typed in a well-formed context, then `codomainCode` is a grown type under `context.cons domainCode`.  The
codomain twin of `functionDomainIsType`, reading off the second conjunct of the Π-code component inversion. -/
theorem HasTypeDescPi.functionCodomainIsType {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {function : RawTerm scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (functionTyped : HasTypeDescPi profile context function (piTyCodeCell domainCode codomainCode))
    (wellFormed : WfContextDescPi context) :
    IsTypeDescPi profile (context.cons domainCode) codomainCode := by
  obtain ⟨_piLevel, _piFlag, piTyped⟩ := functionTyped.classifierIsTypeDescPi wellFormed
  obtain ⟨_domainLevel, codomainLevel, flag, _domainTyped, codomainTyped⟩ :=
    HasTypeDescPi.inversionPiCodeComponentsUnconditional piTyped
  exact ⟨codomainLevel, flag, codomainTyped⟩

end FX1Poly.Typed
