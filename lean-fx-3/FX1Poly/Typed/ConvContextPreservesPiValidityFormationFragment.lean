import FX1Poly.Typed.HasTypeDescPiContextConversion
import FX1Poly.Typed.HasTypeDescPiContextConversionPiElimReduction
import FX1Poly.Typed.IsTypeDesc

/-! # FX1Poly/Typed/ConvContextPreservesPiValidityFormationFragment
    — the residual `ConvContextPreservesPiValidity` is UNCONDITIONALLY free for FORMATION-valid Π-codes

`ConvContextPreservesPiValidity` (`#1092`) is the single residual to which both open grown-metatheory
release blockers reduce (GCC-5 context-conversion `#842` AND SRD-2 master SR `#845`, unified in `#1098`):
a `Π`-type-code's GROWN validity is stable under context conversion.  The seven prior GCC-5 firings
established it is the genuine fixpoint of the mutual recursion (the function's `Π`-classifier validity is
NOT a structural premise of `piElim`, and `classifierIsTypeDescPi` can return an unbounded-height
derivation), so no well-founded measure breaks it; its honest discharge is the OPEN-context semantic
model (a Kripke / sconing logical relation — the bounded reducibility model is closed-substitution-based,
structurally unfit for the open residual, and reflection fails at the neutral base case).

This file pins the OTHER side of that boundary: the residual is UNCONDITIONALLY FREE for the FORMATION
fragment.  A `Π domain codomain` whose validity factors through `ofFormation` (i.e. is a FORMATION type:
the domain/codomain are variables, universe codes, or nested formers over formation children — the common
dependent-type case, no type-level computation) context-converts with NO semantic input, via the shipped
UNCONDITIONAL formation context-conversion `HasTypeDescPi.convContextOfFormation` (`HasTypeDesc.convContext`
re-embedded through `ofFormation`) plus `convBackToUniverseCode`.

Together with `#1095` (the validity-RESPECTS-REDUCTION twin of the residual is likewise free for the
formation fragment, via the unconditional formation subject reduction), this LOCALIZES the residual's
genuinely-open core precisely: it is exactly the GENUINELY-GROWN `Π`-codes — those whose domain or codomain
is an OPEN NEUTRAL type-level application (`(var f) (var a)` at a universe) or a type-level `λ`, typed via
`piElim` / `piIntro` at the type level, NOT via `ofFormation` / `genFormationPi`-from-formation.  And that
open-neutral case IS GCC-5 itself (context-converting a neutral type-level application is the piElim
context-conversion), so the residual's hard core is irreducibly the open semantic-model obligation — there
is no further syntactic fragment to peel off.

## Zero-axiom verification

`obtain` the formation universe witness, `HasTypeDescPi.convContextOfFormation` (the shipped unconditional
formation context-conversion arm) + `HasTypeDescPi.convBackToUniverseCode`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **The residual is unconditionally free for FORMATION-valid Π-codes.**  If `piTyCodeCell domainCode
codomainCode` is a FORMATION type under `sourceContext` (`IsTypeDesc`, i.e. typed at a universe by the
formation engine — no type-level computation), then it is a GROWN type (`IsTypeDescPi`) under any
pointwise-`Conv`-related `targetContext`.  The FORMATION half of `ConvContextPreservesPiValidity` (`#1092`),
discharged with NO semantic input: the shipped unconditional formation context-conversion
`HasTypeDescPi.convContextOfFormation` re-types the formation-valid code under the target at a `Conv`-equal
classifier, and `convBackToUniverseCode` collapses that back to the universe code.  This isolates the
residual's genuinely-open core to the GENUINELY-GROWN (non-`ofFormation`) `Π`-codes — the open-neutral
type-level applications that are GCC-5 itself. -/
theorem HasTypeDescPi.convContextPreservesPiValidityForFormationCode {profile : PolyProfile} {scope : Nat}
    {sourceContext : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (formationValid : IsTypeDesc profile sourceContext (piTyCodeCell domainCode codomainCode))
    (targetContext : TypingContext profile scope)
    (contextConv : ∀ index : Fin scope,
      Conv (sourceContext.lookup index) (targetContext.lookup index)) :
    IsTypeDescPi profile targetContext (piTyCodeCell domainCode codomainCode) := by
  obtain ⟨level, flag, formationTyped⟩ := formationValid
  obtain ⟨classifier', convToClassifier', typedUnderTarget⟩ :=
    HasTypeDescPi.convContextOfFormation formationTyped targetContext contextConv
  exact ⟨level, flag, typedUnderTarget.convBackToUniverseCode convToClassifier'⟩

end FX1Poly.Typed
