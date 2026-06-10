import FX1Poly.Typed.RenameAlongFlagCoherent
import FX1Poly.Typed.ConvUniverseClassificationUnique

/-! # The caller-selected-pair negotiation (E3 capstone)

THE flag wall, closed: a pinned base's universe pair is FORCED to the caller's — rename the base
validity forward into the target context (`renameAlongFlagCoherent`), then negotiate at the
pin's Conv with the Conv-lifted uniqueness (`convUniverseClassificationUnique`).  The corollary
`pinBaseValidAtCallerPair` upgrades any ∃-flag `IsTypeDescPi` pin base (the shipped plateau
extraction's conclusion shape) to validity at the caller's EXACT (level, flag) — so the
λ-reduct assembly's Π-components inherit `invertLam`'s shared flag, and `piIntro` reassembles.

Consumers: the E4 λ-reduct discharge (domain/codomain pins at the inversion's flag) and the E2
re-thread of the pinned-reflection master arms over the flag-coherent condition. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **The pin selects the caller's pair**: a classifier pinned to a renamed base, with the base
valid at some source pair and the classifier valid at the caller's target pair, forces the two
pairs EQUAL — forward renaming + the Conv-lifted uniqueness. -/
theorem HasTypeDescPi.pinSelectsCallerPair {profile : PolyProfile}
    {sourceScope targetScope : Nat} {rho : RawRenaming sourceScope targetScope}
    {sourceContext : TypingContext profile sourceScope}
    {targetContext : TypingContext profile targetScope}
    {classifier : RawTerm targetScope} {base : RawTerm sourceScope}
    {callerLevel baseLevel : LevelExpr} {callerFlag baseFlag : UniverseFlag}
    (targetWellFormed : WfContextDescPi targetContext)
    (condition : ContextReflectsRenameFlagCoherent profile rho sourceContext targetContext)
    (pinned : Conv classifier (RawTerm.rename rho base))
    (callerValid : HasTypeDescPi profile targetContext classifier
      (universeCodeCell callerLevel callerFlag))
    (baseValid : HasTypeDescPi profile sourceContext base
      (universeCodeCell baseLevel baseFlag)) :
    callerLevel = baseLevel ∧ callerFlag = baseFlag := by
  have renamedBaseValid := HasTypeDescPi.renameAlongFlagCoherent baseValid
    targetContext rho condition
  rw [rename_universeCodeCell] at renamedBaseValid
  exact HasTypeDescPi.convUniverseClassificationUnique targetWellFormed pinned
    callerValid renamedBaseValid

/-- **The pinned base re-types at the caller's pair** — the consumable form: any ∃-flag pin base
validity upgrades to validity at the caller's EXACT (level, flag), closing the flag wall for
that pin. -/
theorem HasTypeDescPi.pinBaseValidAtCallerPair {profile : PolyProfile}
    {sourceScope targetScope : Nat} {rho : RawRenaming sourceScope targetScope}
    {sourceContext : TypingContext profile sourceScope}
    {targetContext : TypingContext profile targetScope}
    {classifier : RawTerm targetScope} {base : RawTerm sourceScope}
    {callerLevel : LevelExpr} {callerFlag : UniverseFlag}
    (targetWellFormed : WfContextDescPi targetContext)
    (condition : ContextReflectsRenameFlagCoherent profile rho sourceContext targetContext)
    (pinned : Conv classifier (RawTerm.rename rho base))
    (callerValid : HasTypeDescPi profile targetContext classifier
      (universeCodeCell callerLevel callerFlag))
    (baseIsType : IsTypeDescPi profile sourceContext base) :
    HasTypeDescPi profile sourceContext base (universeCodeCell callerLevel callerFlag) := by
  obtain ⟨baseLevel, baseFlag, baseValid⟩ := baseIsType
  obtain ⟨levelEq, flagEq⟩ := HasTypeDescPi.pinSelectsCallerPair targetWellFormed condition
    pinned callerValid baseValid
  rw [levelEq, flagEq]
  exact baseValid

end FX1Poly.Typed

