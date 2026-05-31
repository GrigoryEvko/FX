import FX1Poly.Typed.HasTypeDescValidity
import FX1Poly.Typed.HasTypeDescInversion
import FX1Poly.Typed.HasTypeDescSubstitution

/-! # FX1Poly/Typed/HasTypeDescApplication — the DEPENDENT-ELIMINATOR OUTPUT is a well-formed
    type (the validity obligation of Π-elimination and Σ-projection), INTRINSIC.

polycell.md §11.8.5 (the non-uniform seam PAST formation): an eliminator's output type is
MOTIVE-DEPENDENT — it instantiates a codomain/motive at the eliminated value.  For
Π-elimination `app : (f : Π A. B) → (a : A) → B[a]` the output is `B[a] = subst0 B a`; for
Σ-projection `snd : (p : Σ A. B) → B[fst p]` it is `B` at the first projection.  This file
proves the SOUNDNESS HEART of those rules — that the instantiated codomain is itself a
well-formed type (`IsTypeDesc`).

## The construction (standalone, non-degenerate)

The eliminator output-VALIDITY obligation is a POSITIVE construction, the hard semantic
content of dependent elimination: it composes three intrinsic bricks — validity
(`classifierIsTypeDesc`), Π/Σ inversion-components (`inversion{Pi,Sigma}CodeComponents`),
and the β-engine substitution (`substituteUnderBinding`) — feeding the intrinsic
substitution into a dependent-elimination soundness fact.  Non-vacuous: a variable of
Π-type (resp. Σ-type) and a variable of the domain type inhabit the hypotheses.  Standalone
lemmas: touch neither `HasTypeDesc`'s constructors nor the `toHasType` ⟺ map.

## The defeq that closes it

`RawTerm.subst0 (universeCodeCell L flag) argument` is DEFINITIONALLY `universeCodeCell L flag`
— `subst0` is `@[reducible]` (`= subst (singleton argument) _`) and `subst_universeCodeCell`
is `rfl` (universe codes carry their level/flag as PAYLOAD, with an empty child spine, so
substitution leaves them fixed).  So `substituteUnderBinding`'s output classifier
`subst0 (universeCodeCell codomainLevel flag) argument` IS `universeCodeCell codomainLevel
flag`, and the `IsTypeDesc` existential witness closes by defeq.

## Zero-axiom

Composition of `classifierIsTypeDesc` + `inversion{Pi,Sigma}CodeComponents` +
`substituteUnderBinding`, plus the `subst0`/`subst_universeCodeCell` defeq.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Audit-gated.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- The output type of Π-ELIMINATION is well-formed: if `functionTerm : Π domainCode.
codomainCode` and `argument : domainCode`, then `codomainCode[argument]` (the application's
result type, `subst0 codomainCode argument`) is a description-engine type.  The validity
obligation of the `app` rule, proved by composing intrinsic validity (the Π-type is a
type), Π inversion-components (its codomain is a type under the domain binder), and the
intrinsic substitution β-engine (instantiate the codomain at the argument); the resulting
universe classifier `subst0 (universeCodeCell ..) argument` is the universe code by defeq. -/
theorem HasTypeDesc.piApplicationOutputIsType {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {functionTerm domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {argument : RawTerm scope}
    (functionTyped :
      HasTypeDesc profile context functionTerm (piTyCodeCell domainCode codomainCode))
    (argumentTyped : HasTypeDesc profile context argument domainCode)
    (wellFormed : WfContext context) :
    IsTypeDesc profile context (RawTerm.subst0 codomainCode argument) := by
  obtain ⟨_piLevel, _piFlag, piTyped⟩ := functionTyped.classifierIsTypeDesc wellFormed
  obtain ⟨_domainLevel, codomainLevel, flag, _domainTyped, codomainTyped, _convToPiCode⟩ :=
    HasTypeDesc.inversionPiCodeComponents piTyped wellFormed
  have substituted :=
    HasTypeDesc.substituteUnderBinding argument codomainTyped argumentTyped
  exact ⟨codomainLevel, flag, substituted⟩

/-- The output type of Σ-PROJECTION (the second projection) is well-formed: if
`pairTerm : Σ domainCode. codomainCode` and `firstProjection : domainCode` (the value the
codomain is instantiated at — `fst pairTerm` in the `snd` rule), then
`codomainCode[firstProjection]` (`subst0 codomainCode firstProjection`) is a description-engine
type.  The Σ mirror of `piApplicationOutputIsType`, via `inversionSigmaCodeComponents`. -/
theorem HasTypeDesc.sigmaProjectionOutputIsType {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {pairTerm domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {firstProjection : RawTerm scope}
    (pairTyped :
      HasTypeDesc profile context pairTerm (sigmaTyCodeCell domainCode codomainCode))
    (firstProjectionTyped : HasTypeDesc profile context firstProjection domainCode)
    (wellFormed : WfContext context) :
    IsTypeDesc profile context (RawTerm.subst0 codomainCode firstProjection) := by
  obtain ⟨_sigmaLevel, _sigmaFlag, sigmaTyped⟩ := pairTyped.classifierIsTypeDesc wellFormed
  obtain ⟨_domainLevel, codomainLevel, flag, _domainTyped, codomainTyped, _convToSigmaCode⟩ :=
    HasTypeDesc.inversionSigmaCodeComponents sigmaTyped wellFormed
  have substituted :=
    HasTypeDesc.substituteUnderBinding firstProjection codomainTyped firstProjectionTyped
  exact ⟨codomainLevel, flag, substituted⟩

end FX1Poly.Typed
