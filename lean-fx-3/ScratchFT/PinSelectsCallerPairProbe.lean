import FX1Poly.Typed.RenameAlongFlagCoherent
import FX1Poly.Typed.ConvUniverseClassificationUnique

/-! Probe: E3 capstone — the caller-selected-pair negotiation.  A pinned base's universe pair is
FORCED to the caller's: rename the base validity forward into the target context (the new
fibration leg), then negotiate at the pin's Conv with the E2.8 lift.  The corollary re-types the
base at the caller's exact (level, flag) — the flag-coherent pin the Π-reassembly consumes. -/

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

#print axioms FX1Poly.Typed.HasTypeDescPi.pinSelectsCallerPair
#print axioms FX1Poly.Typed.HasTypeDescPi.pinBaseValidAtCallerPair
