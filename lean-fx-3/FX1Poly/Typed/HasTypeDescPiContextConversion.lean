import FX1Poly.Typed.HasTypeDescContextConversion
import FX1Poly.Typed.HasTypeDescPi

/-! # FX1Poly/Typed/HasTypeDescPiContextConversion — grown-engine context-conversion: the validity-free arms
    (#814 part 2a — the ofFormation bridge + the universe-code conv-back; the formation-codomain unblocker)

CONTEXT-CONVERSION for the GROWN engine `HasTypeDescPi` (typing stable under a pointwise-`Conv`-replaced
context) is the brick the former-DOMAIN SR congruence (#458/SN-055) needs.  Part 1
(`HasTypeDescContextConversion`) shipped it for the FORMATION engine `HasTypeDesc` (the wf-free leaf half).

## The validity-entanglement finding (why the grown core is deferred)

Of the grown engine's six arms, FIVE are validity-free:
  * `ofFormation` — delegate to part 1, re-embed (THIS FILE).
  * `var` — `var Γ' i` + `contextConv i`.
  * `conv` — recurse + compose conversions.
  * `piIntro` — domain/codomain conv-back to universe codes (`convBackToUniverseCode`, no `wf`); body
    conv-back via the recursively-obtained codomain typing (no `wf`).
  * `genFormationPi` — recurse the premise spine; heads conv-back via `convBackToUniverseCode`.

The LONE hard arm is `piElim`: to rebuild `appCell function argument`, the function (typed at `F' ≡ Π D C`
under `Γ'`) must be conv-backed to the EXACT syntactic `Π D C`, whose `conv`-rule reclassifier is "`Π D C`
typed under `Γ'`".  Obtaining that needs `classifierIsTypeDesc` on a derivation that is NOT a structural
sub-derivation (the Pi's validity), i.e. a "typing a `Conv`-equal type" step — which IS subject reduction.
There is no `type-Conv-closure` lemma (it would be circular with SR).  So the full grown context-conversion
is part of the mutual FUNDAMENTAL-METATHEORY bundle (type-correctness + context-conversion + Π-injectivity +
SR), a deliberate multi-fire development — NOT a clean single-fire brick.

## What this file ships (and what it already enables)

The two validity-free pieces:

  * `HasTypeDescPi.convBackToUniverseCode` — conv-back to a universe code in the grown engine (via
    `HasTypeDescPi.universeFormation`); the grown twin of the formation helper.
  * `HasTypeDescPi.convContextOfFormation` — the grown `ofFormation` arm: a FORMATION-typed grown subject
    context-converts by delegating to part 1 (`HasTypeDesc.convContext`) and re-embedding through
    `ofFormation`.

Together these already discharge former-DOMAIN congruence for the COMMON case — a former `Π domain
codomain` whose `codomain` is a FORMATION type (a variable, a universe code, or a nested former over
formation children): when `domain` steps, the codomain re-types under `cons domain'` through
`convContextOfFormation`.  Only the grown-codomain case (a type-level application / λ in the codomain)
awaits the mutual bundle.

## Zero-axiom verification

`convBackToUniverseCode` is a `conv` + `universeFormation`; `convContextOfFormation` is a `let`-destructure
of part 1 + `ofFormation`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration audit-gated.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Conv-back to a universe code (grown engine).**  A grown subject typed at any classifier `reachedCode`
convertible FROM the universe code `Type@(level, flag)` is typed at that universe code itself —
`ofFormation ∘ HasTypeDesc.universeFormation` supplies the reclassifier typing (there is no grown
`universeFormation` arm), so the `conv` rule closes it with no side conditions.  The grown twin of
`HasTypeDesc.convBackToUniverseCode`. -/
theorem HasTypeDescPi.convBackToUniverseCode {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject reachedCode : RawTerm scope}
    {level : LevelExpr} {flag : UniverseFlag}
    (typedAtReached : HasTypeDescPi profile context subject reachedCode)
    (universeConvToReached : Conv (universeCodeCell level flag) reachedCode) :
    HasTypeDescPi profile context subject (universeCodeCell level flag) :=
  HasTypeDescPi.conv level.lsucc flag typedAtReached universeConvToReached.sym
    (HasTypeDescPi.ofFormation (HasTypeDesc.universeFormation context level flag))

/-- **The grown `ofFormation` context-conversion arm.**  A FORMATION-typed grown subject survives replacing
the context by a pointwise-`Conv`-related one: context-convert the formation derivation through part 1
(`HasTypeDesc.convContext`), then re-embed the result via `HasTypeDescPi.ofFormation`.  This is the validity-
FREE arm of grown context-conversion, and it already discharges former-DOMAIN congruence whenever the
codomain is a FORMATION type (the common dependent-type case). -/
theorem HasTypeDescPi.convContextOfFormation {profile : PolyProfile} {scope : Nat}
    {sourceContext : TypingContext profile scope} {subject classifier : RawTerm scope}
    (formationTyped : HasTypeDesc profile sourceContext subject classifier)
    (targetContext : TypingContext profile scope)
    (contextConv : ∀ index : Fin scope,
      Conv (sourceContext.lookup index) (targetContext.lookup index)) :
    ∃ classifier', Conv classifier classifier' ∧
      HasTypeDescPi profile targetContext subject classifier' :=
  let ⟨convertedClassifier, classifierConverts, formationTypedUnderTarget⟩ :=
    formationTyped.convContext targetContext contextConv
  ⟨convertedClassifier, classifierConverts, HasTypeDescPi.ofFormation formationTypedUnderTarget⟩

end FX1Poly.Typed
