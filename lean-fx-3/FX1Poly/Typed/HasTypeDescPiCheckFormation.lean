import FX1Poly.Typed.HasTypeDescPiCheckOfInferred
import FX1Poly.Typed.HasTypeDescPiFormationUniqueness
import FX1Poly.Typed.HasTypeDescPiFormerCongruence
import FX1Poly.Typed.WfContextDescPiFromWfContextDesc

/-! # FX1Poly/Typed/HasTypeDescPiCheckFormation
    — the Π/Σ-FORMATION cases of the bidirectional grown-engine checker (SN-052)

The Π/Σ-formation positions (`piTyCodeCell` / `sigmaTyCodeCell`) are infer-mode positions whose inference is
SR-FREE: a former types unconditionally at `Type@(lmax domainLevel codomainLevel)` GIVEN its components'
universe-typings (`piFormationViaGenArm` / `sigmaFormationViaGenArm`, one generic `genFormationPi` row).  Unlike
the application position — which needs the function's `Π`-head EXPOSED (the SR-gated normalize-then-`conv`) —
the components of a former are ALREADY type codes typed at universes, so there is nothing to expose.  The only
input the checker cannot compute itself is the components' typing + uniqueness, which the recursive
component-inference delivers; here they are threaded as parameters (the same factoring as the application
checker, but with NO sub-decision branch — a former always types given its components, so the whole decision is
the COMPARE step's `Conv` comparison against the target).

The four ingredients per former:

  * INFERENCE: `{pi,sigma}FormationViaGenArm` builds `former : Type@(lmax domainLevel codomainLevel)`;
  * the inferred type's typing: that universe code is typed at the next universe by `universeFormation`;
  * UNIQUENESS: `{pi,sigma}FormationTypeUniqueGivenComponents` (the former's type is `Conv`-unique given the
    components' type-uniqueness — `lmaxAll [domainLevel, codomainLevel]` is `lmax domainLevel codomainLevel`
    definitionally, so the uniqueness and inference agree on the inferred type);
  * the COMPARE step `decidableCheckOfInferredUniqueAtType` decides against the target.

With the variable, universe-code, application, and now Π/Σ-formation positions covered, every infer-mode
checker position has its SR-free combinator; only the λ INTRODUCTION position (CHECK mode, gated on exposing
the target's `Π`-components and on context-conversion for completeness) and the recursive assembly remain.

## Zero-axiom verification

A direct application of the shipped COMPARE step to the shipped former inference + `universeFormation` +
former-uniqueness.  No `match`, no `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **Decidable checking of a Π-formation cell against a known-type target, given the components.**  Given the
domain's and codomain's universe-typings (`domainTyped` / `codomainTyped`) and their type-uniqueness
(`domainUnique` / `codomainUnique`), `piTyCodeCell domainCode codomainCode : targetType` is decided by the
COMPARE step against the former's inferred type `Type@(lmax domainLevel codomainLevel)` — SR-free, since a
former needs no exposure (its components are already type codes). -/
def HasTypeDescPi.decidableCheckPiFormationGivenComponents {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (wellFormed : WfContextDesc context)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel codomainLevel : LevelExpr} {flag : UniverseFlag}
    (domainTyped : HasTypeDescPi profile context domainCode (universeCodeCell domainLevel flag))
    (codomainTyped :
      HasTypeDescPi profile (context.cons domainCode) codomainCode
        (universeCodeCell codomainLevel flag))
    (domainUnique :
      ∀ {otherDomainType : RawTerm scope},
        HasTypeDescPi profile context domainCode otherDomainType →
          Conv (universeCodeCell domainLevel flag) otherDomainType)
    (codomainUnique :
      ∀ {otherCodomainType : RawTerm (scope + 1)},
        HasTypeDescPi profile (context.cons domainCode) codomainCode otherCodomainType →
          Conv (universeCodeCell codomainLevel flag) otherCodomainType)
    {targetType : RawTerm scope} {targetLevel : LevelExpr} {targetFlag : UniverseFlag}
    (targetTyped :
      HasTypeDescPi profile context targetType (universeCodeCell targetLevel targetFlag)) :
    Decidable (HasTypeDescPi profile context (piTyCodeCell domainCode codomainCode) targetType) :=
  HasTypeDescPi.decidableCheckOfInferredUniqueAtType wellFormed
    (inferred :=
      HasTypeDescPi.piFormationViaGenArm context domainCode codomainCode domainLevel codomainLevel
        flag domainTyped codomainTyped)
    (inferredTypeTyped :=
      .ofFormation (HasTypeDesc.universeFormation context
        (LevelExpr.lmax domainLevel codomainLevel) flag))
    (targetTyped := targetTyped)
    (uniqueAtSubject :=
      HasTypeDescPi.piFormationTypeUniqueGivenComponents
        (WfContextDescPi.ofWfContextDesc wellFormed) domainUnique codomainUnique)

/-- **Decidable checking of a Σ-formation cell against a known-type target, given the components** — the Σ dual
of `decidableCheckPiFormationGivenComponents`, identical recipe over `sigmaTyCodeCell`,
`sigmaFormationViaGenArm`, and `sigmaFormationTypeUniqueGivenComponents`. -/
def HasTypeDescPi.decidableCheckSigmaFormationGivenComponents {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (wellFormed : WfContextDesc context)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel codomainLevel : LevelExpr} {flag : UniverseFlag}
    (domainTyped : HasTypeDescPi profile context domainCode (universeCodeCell domainLevel flag))
    (codomainTyped :
      HasTypeDescPi profile (context.cons domainCode) codomainCode
        (universeCodeCell codomainLevel flag))
    (domainUnique :
      ∀ {otherDomainType : RawTerm scope},
        HasTypeDescPi profile context domainCode otherDomainType →
          Conv (universeCodeCell domainLevel flag) otherDomainType)
    (codomainUnique :
      ∀ {otherCodomainType : RawTerm (scope + 1)},
        HasTypeDescPi profile (context.cons domainCode) codomainCode otherCodomainType →
          Conv (universeCodeCell codomainLevel flag) otherCodomainType)
    {targetType : RawTerm scope} {targetLevel : LevelExpr} {targetFlag : UniverseFlag}
    (targetTyped :
      HasTypeDescPi profile context targetType (universeCodeCell targetLevel targetFlag)) :
    Decidable (HasTypeDescPi profile context (sigmaTyCodeCell domainCode codomainCode) targetType) :=
  HasTypeDescPi.decidableCheckOfInferredUniqueAtType wellFormed
    (inferred :=
      HasTypeDescPi.sigmaFormationViaGenArm context domainCode codomainCode domainLevel codomainLevel
        flag domainTyped codomainTyped)
    (inferredTypeTyped :=
      .ofFormation (HasTypeDesc.universeFormation context
        (LevelExpr.lmax domainLevel codomainLevel) flag))
    (targetTyped := targetTyped)
    (uniqueAtSubject :=
      HasTypeDescPi.sigmaFormationTypeUniqueGivenComponents
        (WfContextDescPi.ofWfContextDesc wellFormed) domainUnique codomainUnique)

end FX1Poly.Typed
