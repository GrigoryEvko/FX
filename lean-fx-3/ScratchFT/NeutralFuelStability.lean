import FX1Poly.Typed.FundamentalAtAllPositiveArguments

namespace FX1Poly.Typed

open FX1Poly.Core
open FX1Poly.Foundation
open StepStar

-- Neutral-fragment fuel stability: the genuinely-tractable arm of #672.
-- A weak-head-normal non-Pi non-universe type's candidate is SN at every level (candidateIffStronglyNormalizing),
-- so membership at one positive fuel implies SN, implies membership at all positive fuels.
theorem neutralFuelStability_probe {scope : Nat} {typeCode term : RawTerm scope}
    (noWeakHeadStep : ∀ reduct : RawTerm scope, ¬ WeakHeadStep typeCode reduct)
    (notPiType : typeCode.rootGenerator ≠ Generator.gen_piTyCode)
    (notUniverse : typeCode.rootGenerator ≠ Generator.gen_universeCode)
    (typeAllLevels : IsReducibleTypeAtAllLevels typeCode)
    {predLevel : Nat}
    (member : IsReducibleMemberAt (predLevel + 1) typeCode term) :
    IsReducibleMemberAtAllPositiveLevels typeCode term := by
  obtain ⟨candAtK, reducibleAtK, termInCandAtK⟩ := member
  have termSN : IsStronglyNormalizing term :=
    (ReducibleTypeStep.candidateIffStronglyNormalizing reducibleAtK
      noWeakHeadStep notPiType notUniverse term).mp termInCandAtK
  intro level
  obtain ⟨candAtJ, reducibleAtJ⟩ := typeAllLevels (level + 1)
  exact ⟨candAtJ, reducibleAtJ,
    (ReducibleTypeStep.candidateIffStronglyNormalizing reducibleAtJ
      noWeakHeadStep notPiType notUniverse term).mpr termSN⟩

end FX1Poly.Typed
