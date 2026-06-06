import FX1Poly.Typed.HasTypeDescPiVariableInversion
import FX1Poly.Typed.ConvCodeInjectivity
import FX1Poly.Typed.WfContextDescPi

/-! # FX1Poly/Typed/GrownVariableHonesty
    — 0-FP honesty for a VARIABLE subject in the grown engine `HasTypeDescPi`: a variable inhabits ONLY its
      declared type (up to `Conv`) (SN-140 L1, the variable leaf of the grown shape discipline)

`GrownEngineHonesty` pinned the λ / type-code leaves (a λ inhabits only a Π; a Π/Σ-type code only a universe) and
`GrownUniverseConsistency` the universe-code leaf (no Type:Type / inflation / deflation / flag drift).  This file
adds the remaining leaf — the VARIABLE — completing the grown engine's 0-FP shape discipline over every subject
shape the engine types (var / λ / type code / universe code; app's classifier is the substituted codomain, not a
fixed shape).

Unlike the λ leaf (whose classifier shape is determined by the λ ITSELF, so `lam_notTypedAtUniverseCode` is
UNCONDITIONAL), a variable's classifier shape is determined by its CONTEXT LOOKUP — so the variable honesty is
inherently relative to the lookup.  `HasTypeDescPi.inversionVariable` pins it: any classifier a variable receives
is `Conv` to `context.lookup index`.  The honest rejection is the contrapositive — a variable is NOT typed at any
classifier `Conv`-distinct from its lookup — and the concrete leaf rejections compose it with the conv-rigidity
family for a lookup of known shape.

  * `variable_notTypedAtNonConvLookup` — the GENERAL variable 0-FP: a variable inhabits ONLY classifiers `Conv`
    to its context lookup.  Every concrete rejection below is an instance.
  * `piTypedVariable_notTypedAtUniverseCode` — a variable whose lookup is a Π-type code is NOT typed at a
    universe code (it is a function-typed term, not a type): inversion `Conv`s the universe code to the Π-type
    lookup, refuted by `Conv.piTyCode_not_universeCode`.
  * `universeTypedVariable_notTypedAtPiTyCode` / `…AtSigmaTyCode` — a type variable (lookup a universe code) is
    NOT typed at a Π / Σ-type code (it is a type, not a function/pair type): inversion `Conv`s the Π/Σ code to
    the universe-code lookup, refuted by `Conv.piTyCode_not_universeCode` / `Conv.sigmaTyCode_not_universeCode`.

## Zero-axiom verification

Each rejection feeds `HasTypeDescPi.inversionVariable`'s `Conv` witness (rewritten by the lookup hypothesis) to
a conv-rigidity lemma, the general one directly to the non-`Conv` hypothesis.  Each probe carries the grown
well-formedness `WfContextDescPi` as a shape decoration (the honesty is over well-formed contexts); the empty
context (`WfContextDescPi.emptyIsWellFormed`) already instantiates it.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The general variable 0-FP: a variable inhabits ONLY classifiers `Conv` to its lookup.**  The contrapositive
of `HasTypeDescPi.inversionVariable`: if a classifier is NOT `Conv` to the variable's context lookup, the
variable is not typed at it.  Every concrete leaf rejection is an instance. -/
theorem variable_notTypedAtNonConvLookup {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} (_wellFormed : WfContextDescPi context)
    {index : Fin scope} {classifier : RawTerm scope}
    (classifierNotConvLookup : ¬ Conv classifier (context.lookup index)) :
    ¬ HasTypeDescPi profile context (variableCell index) classifier :=
  fun typed => classifierNotConvLookup (HasTypeDescPi.inversionVariable typed)

/-- **A Π-typed variable is never typed at a universe code.**  A variable whose context lookup is a Π-type code
`piTyCodeCell …` is a function-typed term, not a type: `inversionVariable` `Conv`s the universe code to the
Π-type lookup, refuted by `Conv.piTyCode_not_universeCode`. -/
theorem piTypedVariable_notTypedAtUniverseCode {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} (_wellFormed : WfContextDescPi context) {index : Fin scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (lookupIsPi : context.lookup index = piTyCodeCell domainCode codomainCode)
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    ¬ HasTypeDescPi profile context (variableCell index) (universeCodeCell levelExpr flag) := by
  intro typed
  have conv : Conv (universeCodeCell levelExpr flag : RawTerm scope) (context.lookup index) :=
    HasTypeDescPi.inversionVariable typed
  rw [lookupIsPi] at conv
  exact Conv.piTyCode_not_universeCode conv.sym

/-- **A type variable is never typed at a Π-type code.**  A variable whose context lookup is a universe code
`universeCodeCell …` (a TYPE variable — its values are types) is not classified by a Π type:
`inversionVariable` `Conv`s the Π-type code to the universe-code lookup, refuted by
`Conv.piTyCode_not_universeCode`. -/
theorem universeTypedVariable_notTypedAtPiTyCode {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} (_wellFormed : WfContextDescPi context) {index : Fin scope}
    {levelExpr : LevelExpr} {flag : UniverseFlag}
    (lookupIsUniverse : context.lookup index = universeCodeCell levelExpr flag)
    (domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1)) :
    ¬ HasTypeDescPi profile context (variableCell index) (piTyCodeCell domainCode codomainCode) := by
  intro typed
  have conv : Conv (piTyCodeCell domainCode codomainCode : RawTerm scope) (context.lookup index) :=
    HasTypeDescPi.inversionVariable typed
  rw [lookupIsUniverse] at conv
  exact Conv.piTyCode_not_universeCode conv

/-- **A type variable is never typed at a Σ-type code** (the Σ dual of `universeTypedVariable_notTypedAtPiTyCode`):
a universe-typed variable is not classified by a Σ type, refuted by `Conv.sigmaTyCode_not_universeCode`. -/
theorem universeTypedVariable_notTypedAtSigmaTyCode {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} (_wellFormed : WfContextDescPi context) {index : Fin scope}
    {levelExpr : LevelExpr} {flag : UniverseFlag}
    (lookupIsUniverse : context.lookup index = universeCodeCell levelExpr flag)
    (domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1)) :
    ¬ HasTypeDescPi profile context (variableCell index) (sigmaTyCodeCell domainCode codomainCode) := by
  intro typed
  have conv : Conv (sigmaTyCodeCell domainCode codomainCode : RawTerm scope) (context.lookup index) :=
    HasTypeDescPi.inversionVariable typed
  rw [lookupIsUniverse] at conv
  exact Conv.sigmaTyCode_not_universeCode conv

end FX1Poly.Typed
