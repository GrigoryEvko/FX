import FX1Poly.Typed.Engine.Union.HasTypeUnionGenericVariableInversion
import FX1Poly.Typed.Metatheory.Universe.UniverseClassificationUnique
import FX1Poly.Typed.Metatheory.Universe.UniverseCodeConversion

/-! # FX1Poly/Typed/Metatheory/Universe/NativeUniverseClassificationUnique
    — native universe-flag-uniqueness, the variable leaf (consistency-leg keystone #1697/#1740)

The native `HasTypeUnion` port of `HasTypeDescPi.variableUniverseClassificationUnique`: two universe-code
classifiers of ONE variable agree on BOTH level and flag.  Built directly on the variable-head inversion
(`invertAtVarHeadGeneric`): each universe-code typing of `variableCell index` makes the context lookup
`context.lookup index` convert to that universe code, so the two universe codes are mutually `Conv` (through the
shared lookup), and `Conv.universeCode_injective` reads off the level/flag agreement.

This is the first of the structural leaves of native universe-flag-uniqueness for type-subjects — the keystone
the option/either/nat/list/idJ motive-step congruence subject-reduction arms (gate-2 residual of the consistency
leg) reduce to via drifted-branch-type reformedness at a common flag.  The neutral (application-spine) leaf and
the structural assembly follow, mirroring `neutralUniverseClassificationUnique` /
`normalUniverseClassificationUniqueAtBudget`.

## Zero-axiom verification

`invertAtVarHeadGeneric`, `variableCell_inj_of_conv`, `Conv.universeCode_injective`, `Conv.refl` / `Conv.sym` /
`Conv.trans`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration audit-gated. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **★ Native variable universe-classification uniqueness.**  A variable typed at two universe codes agrees on
level and flag — the native variable leaf of universe-flag-uniqueness.  Both inversions route the lookup through
`Conv` to the respective universe code; the codes are then mutually convertible and `universeCode_injective`
closes it. -/
theorem HasTypeUnion.variableUniverseClassificationUnique {profile : PolyProfile}
    {scope : Nat} {context : TypingContext profile scope} {index : Fin scope}
    {firstLevel secondLevel : LevelExpr} {firstFlag secondFlag : UniverseFlag}
    (firstClassified : HasTypeUnion profile context (variableCell index)
      (universeCodeCell firstLevel firstFlag))
    (secondClassified : HasTypeUnion profile context (variableCell index)
      (universeCodeCell secondLevel secondFlag)) :
    firstLevel = secondLevel ∧ firstFlag = secondFlag := by
  obtain ⟨firstIndex, firstShape, firstLookupConv⟩ :=
    HasTypeUnion.invertAtVarHeadGeneric firstClassified rfl
  obtain ⟨secondIndex, secondShape, secondLookupConv⟩ :=
    HasTypeUnion.invertAtVarHeadGeneric secondClassified rfl
  have firstConvVar : Conv (variableCell index : RawTerm scope) (variableCell firstIndex) :=
    firstShape ▸ Conv.refl (variableCell index)
  have secondConvVar : Conv (variableCell index : RawTerm scope) (variableCell secondIndex) :=
    secondShape ▸ Conv.refl (variableCell index)
  have firstEq : index = firstIndex := variableCell_inj_of_conv firstConvVar
  have secondEq : index = secondIndex := variableCell_inj_of_conv secondConvVar
  rw [← firstEq] at firstLookupConv
  rw [← secondEq] at secondLookupConv
  exact Conv.universeCode_injective (firstLookupConv.sym.trans secondLookupConv)

end FX1Poly.Typed
