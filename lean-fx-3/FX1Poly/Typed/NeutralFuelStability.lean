import FX1Poly.Typed.FundamentalAtAllPositiveArguments

/-! # FX1Poly/Typed/NeutralFuelStability
    — the neutral arm of the fuel-stability gate (toward #672 / SN-043)

`HasPositiveMemberExtensionForStronglyNormalizingAllLevelTypes` (the SN-043 gate, `FundamentalWith
TypeValueCandidates.lean`) asks: for a strongly-normalizing type code reducible at EVERY fuel level, a
member at ONE positive fuel is a member at ALL positive fuels.  The difficulty is genuinely the universe
and Π arms, where the stratified candidate `ReducibleTypeAt level` is level-DEPENDENT (the universe arm's
candidate strictly grows with fuel: `universeReducibilityPredicate (ReducibleTypeAt n)` references the
relation one level down).  This file discharges the arm where it is NOT level-dependent.

**The neutral arm.**  When `typeCode` is weak-head-normal, non-Π-rooted, and non-universe-rooted, its
candidate at every level is exactly `IsStronglyNormalizing` (`ReducibleTypeStep.candidateIffStronglyNormal
izing`, level-agnostic — it holds over any lower relation).  So membership at any positive fuel is just
"the term is SN", which is fuel-independent: a member at one positive fuel is SN, hence a member at every
positive fuel.  No saturation argument is needed — the neutral candidate simply does not move with the
fuel.

This is a genuine sub-case of the gate (a real instance: e.g. a variable-headed neutral type whose members
are the SN terms), not the full gate — the universe / Π arms remain the open crux (#672).

## Zero-axiom verification

`candidateIffStronglyNormalizing` (shipped, `StratifiedReducibleType.lean`) applied at the member's level
and at each target positive level, plus the existential repackaging of `IsReducibleMemberAt` /
`IsReducibleTypeAtAllLevels` / `IsReducibleMemberAtAllPositiveLevels`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core
open FX1Poly.Foundation
open StepStar

/-- **Fuel stability for neutral types** (the neutral arm of the #672 gate).  A weak-head-normal,
non-Π-rooted, non-universe-rooted type code reducible at every fuel level has a level-independent candidate
(`IsStronglyNormalizing`), so a member at one positive fuel is a member at every positive fuel.  The member
is strongly normalizing (read off the neutral candidate at its level), and SN feeds the neutral candidate
back at every other positive level.  Honest scope: this is NOT the full gate — the universe / Π arms, where
the candidate genuinely moves with the fuel, remain the open crux. -/
theorem IsReducibleMemberAtAllPositiveLevels.ofNeutralTypeMember {scope : Nat}
    {typeCode term : RawTerm scope}
    (noWeakHeadStep : ∀ reduct : RawTerm scope, ¬ WeakHeadStep typeCode reduct)
    (notPiType : typeCode.rootGenerator ≠ Generator.gen_piTyCode)
    (notUniverse : typeCode.rootGenerator ≠ Generator.gen_universeCode)
    (typeReducibleAtAllLevels : IsReducibleTypeAtAllLevels typeCode)
    {predLevel : Nat}
    (member : IsReducibleMemberAt (predLevel + 1) typeCode term) :
    IsReducibleMemberAtAllPositiveLevels typeCode term := by
  obtain ⟨candidateAtMemberLevel, reducibleAtMemberLevel, termInCandidate⟩ := member
  have termStronglyNormalizing : IsStronglyNormalizing term :=
    (ReducibleTypeStep.candidateIffStronglyNormalizing reducibleAtMemberLevel
      noWeakHeadStep notPiType notUniverse term).mp termInCandidate
  intro level
  obtain ⟨candidateAtLevel, reducibleAtLevel⟩ := typeReducibleAtAllLevels (level + 1)
  exact ⟨candidateAtLevel, reducibleAtLevel,
    (ReducibleTypeStep.candidateIffStronglyNormalizing reducibleAtLevel
      noWeakHeadStep notPiType notUniverse term).mpr termStronglyNormalizing⟩

end FX1Poly.Typed
