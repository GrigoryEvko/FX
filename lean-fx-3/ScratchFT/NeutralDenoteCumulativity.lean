import FX1Poly.Typed.DenoteKeyedReducibility

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

/-- A weak-head-normal, non-Π, non-universe type code is reducible-as-type (with the level-independent
SN candidate) at EVERY denote level: the neutral arm's premises don't mention the level, so the witness
is uniform. The positive complement to gapUniverseDomainPiVacuouslyReducibleAtLowLevel. -/
theorem neutralTypeReducibleAtEveryDenoteLevel {scope : Nat} (env : Nat → Nat)
    {typeCode : RawTerm scope}
    (noWeakHeadStep : ∀ reduct : RawTerm scope, ¬ WeakHeadStep typeCode reduct)
    (notPiCode : typeCode.rootGenerator ≠ Generator.gen_piTyCode)
    (notUniverseCode : typeCode.rootGenerator ≠ Generator.gen_universeCode)
    (level : Nat) :
    ReducibleTypeAtDenote env level typeCode IsStronglyNormalizing :=
  ReducibleTypeStepDenote.neutral noWeakHeadStep notPiCode notUniverseCode

/-- Same-candidate cumulativity for the neutral fragment: a neutral type reducible at any level is
reducible at any other level (the SN candidate is level-stable). The obstruction is the universe/gap
case ALONE; the neutral fragment lifts both ways, freely. -/
theorem neutralReducibleCumulativeAtDenote {scope : Nat} (env : Nat → Nat)
    {typeCode : RawTerm scope}
    (noWeakHeadStep : ∀ reduct : RawTerm scope, ¬ WeakHeadStep typeCode reduct)
    (notPiCode : typeCode.rootGenerator ≠ Generator.gen_piTyCode)
    (notUniverseCode : typeCode.rootGenerator ≠ Generator.gen_universeCode)
    (lowerLevel higherLevel : Nat) :
    ReducibleTypeAtDenote env lowerLevel typeCode IsStronglyNormalizing →
    ReducibleTypeAtDenote env higherLevel typeCode IsStronglyNormalizing :=
  fun _ => neutralTypeReducibleAtEveryDenoteLevel env noWeakHeadStep notPiCode notUniverseCode higherLevel

#print axioms FX1Poly.Typed.neutralTypeReducibleAtEveryDenoteLevel
#print axioms FX1Poly.Typed.neutralReducibleCumulativeAtDenote
