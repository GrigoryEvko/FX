import FX1Poly.Typed.HasTypeHonesty
import FX1Poly.Core.ConvNormalForm
import FX1Poly.Core.StrongNormalizationLeaves
import FX1Poly.Core.RawTermDecEq

/-! # FX1Poly/Typed/HasTypeDecidableConv
    — decidable type conversion for the current typing fragment

In the current `HasType` fragment (`var` / `conv` / `universeFormation`) every
well-typed subject is a non-stepping leaf — a `variableCell` or a
`universeCodeCell` (`typedSubjectIsVariableOrUniverseCode`).  In particular
every *type* (every `IsType` classifier) is normal: it has no outgoing `Step`.

Feeding that into the normal-form rigidity seed (`Conv.iff_eq_of_noStep`) gives
the headline of this fragment's P11 line: **type conversion is decidable** —
two well-formed types are convertible iff equal, decided by the propext-free
`DecidableEq (RawTerm scope)` with no normalizer.  This is honestly scoped: the
general decider still needs the NbE normalizer (M12) for non-normal inputs; the
typed classifiers of *this* fragment are already normal, so the special case
suffices and is exact (0 false negatives here).

## Zero-axiom verification

`IsType.hasNoStep` case-splits the validity witness via
`typedSubjectIsVariableOrUniverseCode` and applies the leaf no-step lemmas
(`noStep_var` / `noStep_universeCode`).  The decidable instance is a two-arm
`match` on `DecidableEq (RawTerm)` with a constant motive (propext-clean).
Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- Every type in the current fragment is a non-stepping leaf.  An `IsType`
witness exposes a typing derivation whose subject is the type itself; that
subject is a variable cell or a universe-code cell, and both are normal leaves
(`noStep_var` / `noStep_universeCode`). -/
theorem IsType.hasNoStep {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    (isType : IsType profile context classifier) :
    ∀ reduct : RawTerm scope, Step classifier reduct → False := by
  obtain ⟨levelExpr, flag, typed⟩ := isType
  rcases typed.typedSubjectIsVariableOrUniverseCode with
    ⟨index, classifierIsVariable⟩ | ⟨codeLevel, codeFlag, classifierIsUniverse⟩
  · subst classifierIsVariable
    exact fun _reduct step => StepStar.noStep_var index step
  · subst classifierIsUniverse
    exact fun _reduct step =>
      StepStar.noStep_universeCode (codeLevel, codeFlag) step

/-- **Convertible well-formed types are equal** (current fragment): both types
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

Staged for #443: a Π type's principal classifier is `universeCodeCell (lmax l1
l2) f` where the `(l1, f)`, `(l2, f)` come from the *derivation's* premises, so
matching two Π derivations (recursive `uniqueness`) and refuting a flag-mismatch
(`Decidable IsType`'s Π `isFalse` branch) both need to turn a `Conv` between the
children's universe-code classifiers into syntactic level/flag equality.  Holds
on the current fragment and stays valid after Π lands (universe codes never nest,
so they remain normal leaves). -/
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

/-- For the current fragment, type conversion is exactly equality of types. -/
theorem Conv.iff_eq_of_isType {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {firstType secondType : RawTerm scope}
    (firstIsType : IsType profile context firstType)
    (secondIsType : IsType profile context secondType) :
    Conv firstType secondType ↔ firstType = secondType :=
  Conv.iff_eq_of_noStep firstIsType.hasNoStep secondIsType.hasNoStep

/-- **Type conversion is decidable for the current fragment** (the P11 /
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
