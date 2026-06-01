import FX1Poly.Typed.HasTypeHonesty
import FX1Poly.Typed.HasTypeSubjectReduction
import FX1Poly.Core.ConvNormalForm
import FX1Poly.Core.StrongNormalizationLeaves
import FX1Poly.Core.RawTermDecEq

/-! # FX1Poly/Typed/HasTypeDecidableConv
    — decidable type conversion for the native pi/sigma-formation HasType core

In the native pi/sigma-formation `HasType` core every *type* (every `IsType` classifier) is
NORMAL: it has no outgoing `Step`.  The type formers (`piTyCodeCell`,
`sigmaTyCodeCell`) are non-stepping because their typed children are normal, and
the leaves (`variableCell`, `universeCodeCell`) trivially so
(`HasType.subjectHasNoStep`).

Feeding that into the normal-form rigidity seed (`Conv.iff_eq_of_noStep`) gives
this fragment's P11 line: **type conversion is decidable** — two well-formed
types are convertible iff equal, decided by the propext-free `DecidableEq
(RawTerm scope)` with no normalizer.  Scope: the general decider needs the NbE
normalizer for non-normal inputs; the typed classifiers of *this* fragment are
already normal, so the special case suffices and is exact (0 false negatives
here).

## Zero-axiom verification

`IsType.hasNoStep` delegates to `HasType.subjectHasNoStep` (the propext-free
induction-on-derivation invariant) on the type's own typing witness.  The
decidable instance is a two-arm `match` on `DecidableEq (RawTerm)` with a
constant motive (propext-clean).  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- Every type in the native pi/sigma-formation HasType core is a non-stepping normal form.  An
`IsType` witness exposes a typing derivation whose *subject* is the type itself
(`typed : HasType … classifier (univ …)`), so type normality is exactly the
subject-side `HasType.subjectHasNoStep` specialised to that derivation —
`IsType.hasNoStep` is the classifier-side face of the one structural invariant.

Delegating (rather than re-running the classification split) keeps both faces on
the single induction-on-derivation proof: `subjectHasNoStep` absorbs the nesting
formers via their children IHs and this corollary follows directly. -/
theorem IsType.hasNoStep {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    (isType : IsType profile context classifier) :
    ∀ reduct : RawTerm scope, Step classifier reduct → False := by
  obtain ⟨levelExpr, flag, typed⟩ := isType
  exact typed.subjectHasNoStep

/-- **Convertible well-formed types are equal** (native pi/sigma-formation HasType core): both types
are normal, so `Conv` collapses to `Eq` by rigidity. -/
theorem Conv.eq_of_isType {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {firstType secondType : RawTerm scope}
    (firstIsType : IsType profile context firstType)
    (secondIsType : IsType profile context secondType)
    (convertibility : Conv firstType secondType) :
    firstType = secondType :=
  Conv.eq_of_noStep firstIsType.hasNoStep secondIsType.hasNoStep convertibility

/-- **Universe-code rigidity ⟹ level/flag equality.**  Two convertible
universe-code cells carry equal levels and equal flags.  Universe codes are
non-stepping normal forms (`IsType.hasNoStep`), so `Conv.eq_of_isType` collapses
the `Conv` to a literal cell equality, and `injection` (the same propext-free
destructuring `inversionUniverseCode` uses) extracts the `LevelExpr × UniverseFlag`
payload — then splits the `Prod`.

A Π type's principal classifier is `universeCodeCell (lmax l1 l2) f` where the
`(l1, f)`, `(l2, f)` come from the *derivation's* premises, so matching two Π
derivations (recursive `uniqueness`) and refuting a flag-mismatch
(`Decidable IsType`'s Π `isFalse` branch) both need to turn a `Conv` between the
children's universe-code classifiers into syntactic level/flag equality.
Universe codes never nest, so they remain normal leaves. -/
theorem levelFlag_eq_of_conv_universeCodeCell {profile : PolyProfile}
    {scope : Nat} {context : TypingContext profile scope}
    {firstLevel secondLevel : LevelExpr} {firstFlag secondFlag : UniverseFlag}
    (convertibility :
      Conv (universeCodeCell firstLevel firstFlag : RawTerm scope)
        (universeCodeCell secondLevel secondFlag)) :
    firstLevel = secondLevel ∧ firstFlag = secondFlag := by
  have cellsEqual :
      (universeCodeCell firstLevel firstFlag : RawTerm scope)
        = universeCodeCell secondLevel secondFlag :=
    Conv.eq_of_isType
      ⟨firstLevel.lsucc, firstFlag,
        HasType.universeFormation context firstLevel firstFlag⟩
      ⟨secondLevel.lsucc, secondFlag,
        HasType.universeFormation context secondLevel secondFlag⟩
      convertibility
  have payloadEqual :
      (firstLevel, firstFlag) = (secondLevel, secondFlag) := by
    injection cellsEqual
  injection payloadEqual with levelAgree flagAgree
  exact ⟨levelAgree, flagAgree⟩

/-- For the native pi/sigma-formation HasType core, type conversion is exactly equality of types. -/
theorem Conv.iff_eq_of_isType {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {firstType secondType : RawTerm scope}
    (firstIsType : IsType profile context firstType)
    (secondIsType : IsType profile context secondType) :
    Conv firstType secondType ↔ firstType = secondType :=
  Conv.iff_eq_of_noStep firstIsType.hasNoStep secondIsType.hasNoStep

/-- **Type conversion is decidable for the native pi/sigma-formation HasType core** (the P11 /
★ MILESTONE-A seed): decide `firstType = secondType` with the propext-free
`DecidableEq (RawTerm scope)` and transport across `Conv.iff_eq_of_isType`.  No
normalizer is consulted — the typed classifiers here are already normal. -/
def Conv.decidableOfIsType {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {firstType secondType : RawTerm scope}
    (firstIsType : IsType profile context firstType)
    (secondIsType : IsType profile context secondType) :
    Decidable (Conv firstType secondType) :=
  match instDecidableEqRawTerm firstType secondType with
  | isTrue typesEqual =>
      isTrue ((Conv.iff_eq_of_isType firstIsType secondIsType).mpr typesEqual)
  | isFalse typesDistinct =>
      isFalse fun convertibility =>
        typesDistinct
          ((Conv.iff_eq_of_isType firstIsType secondIsType).mp convertibility)

end FX1Poly.Typed
