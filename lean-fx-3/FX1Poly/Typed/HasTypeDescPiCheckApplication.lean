import FX1Poly.Typed.HasTypeDescPiCheckOfInferred
import FX1Poly.Typed.HasTypeDescPiApplicationUniqueness
import FX1Poly.Typed.HasTypeDescPiSubstitution
import FX1Poly.Typed.HasTypeDescPiAppInversion
import FX1Poly.Typed.ConvCodeInjectivity

/-! # FX1Poly/Typed/HasTypeDescPiCheckApplication
    — the APPLICATION case of the bidirectional grown-engine checker (SN-052), factored over the SR-gated
      function exposure

The application position `appCell functionTerm argument` is an INFER-mode position, but inferring its type
requires the function's type as a `Π`-head (`piTyCodeCell domainCode codomainCode`) — and exposing a grown
function's type as a syntactic `Π` is the SR-gated step (normalize via OB-5 SN, re-type through `conv`, the
target's `Π`-components recovered by injectivity).  This file ships the SR-FREE remainder: GIVEN the function's
`Π`-typing + its type-uniqueness + the `Π`-components' universe-typings (all delivered by the eventual
recursive inference once the exposure lands), the application check against a known-type target is decidable.

The two halves of the decision:

  * the ARGUMENT must check against the function's domain — that recursive sub-decision is threaded as
    `argumentChecks` (the application is well-typed only when the argument is);
  * once the argument checks (`a : domainCode`), the application's inferred type is the dependent output
    `subst0 codomainCode argument` (`piElim`), its universe-typing is the substitution lemma applied to the
    codomain's, and its per-subject uniqueness is `applicationTypeUniqueGivenFunction` — the shipped COMPARE
    step `decidableCheckOfInferredUniqueAtType` then decides against the target.

The `isFalse` branch (argument does NOT check against the domain) closes by `invertApp`: any typing of the
application forces the argument at SOME domain `Conv`-equal to `domainCode` (`functionUnique` + Π-injectivity),
which `conv` re-types to `domainCode` — contradicting `argNotTyped`.  So the application's well-typedness is
EXACTLY the argument's, given the function exposure.

This is the application analogue of `HasTypeDescPiCheckVariable` / `HasTypeDescPiCheckUniverseCode`; the
difference is that the application's "inference" is conditional on an SR-gated exposure, so that exposure is an
input rather than computed here.

## Zero-axiom verification

A `match` on the threaded `argumentChecks` feeding (isTrue) the shipped COMPARE step + `piElim` +
`substituteUnderBinding` + `applicationTypeUniqueGivenFunction`, or (isFalse) `invertApp` +
`Conv.piTyCode_inj` + the grown `conv` rule.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **Decidable checking of an application against a known-type target, given the function exposure.**
`appCell functionTerm argument : targetType` is decidable once the function's `Π`-typing (`functionTyped`), its
type-uniqueness (`functionUnique`), and the `Π`-components' universe-typings (`domainTyped` / `codomainTyped`)
are supplied — the SR-gated function exposure threaded as input.  The decision reduces to the argument's check
against the domain (`argumentChecks`): if the argument checks, `piElim` synthesizes the dependent output
`subst0 codomainCode argument`, `substituteUnderBinding` types it at a universe, and the COMPARE step compares
to the target; if the argument does not check, `invertApp` + Π-injectivity + `conv` show the application cannot
be typed at all. -/
def HasTypeDescPi.decidableCheckApplicationGivenFunction {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (wellFormed : WfContext context)
    {functionTerm argument : RawTerm scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel codomainLevel : LevelExpr} {domainFlag codomainFlag : UniverseFlag}
    (functionTyped :
      HasTypeDescPi profile context functionTerm (piTyCodeCell domainCode codomainCode))
    (functionUnique :
      ∀ {otherFunctionType : RawTerm scope},
        HasTypeDescPi profile context functionTerm otherFunctionType →
          Conv (piTyCodeCell domainCode codomainCode) otherFunctionType)
    (domainTyped : HasTypeDescPi profile context domainCode (universeCodeCell domainLevel domainFlag))
    (codomainTyped :
      HasTypeDescPi profile (context.cons domainCode) codomainCode
        (universeCodeCell codomainLevel codomainFlag))
    (argumentChecks : Decidable (HasTypeDescPi profile context argument domainCode))
    {targetType : RawTerm scope} {targetLevel : LevelExpr} {targetFlag : UniverseFlag}
    (targetTyped :
      HasTypeDescPi profile context targetType (universeCodeCell targetLevel targetFlag)) :
    Decidable (HasTypeDescPi profile context (appCell functionTerm argument) targetType) :=
  match argumentChecks with
  | isTrue argTyped =>
      HasTypeDescPi.decidableCheckOfInferredUniqueAtType wellFormed
        (inferred := HasTypeDescPi.piElim functionTyped argTyped)
        (inferredTypeTyped := HasTypeDescPi.substituteUnderBinding argument codomainTyped argTyped)
        (targetTyped := targetTyped)
        (uniqueAtSubject := HasTypeDescPi.applicationTypeUniqueGivenFunction functionUnique)
  | isFalse argNotTyped =>
      isFalse fun derivation => by
        obtain ⟨_otherDomain, _otherCodomain, otherFunctionTyped, otherArgTyped, _otherConv⟩ :=
          HasTypeDescPi.invertApp derivation
        obtain ⟨domainConv, _codomainConv⟩ :=
          Conv.piTyCode_inj (functionUnique otherFunctionTyped)
        exact argNotTyped
          (HasTypeDescPi.conv domainLevel domainFlag otherArgTyped domainConv.sym domainTyped)

end FX1Poly.Typed
