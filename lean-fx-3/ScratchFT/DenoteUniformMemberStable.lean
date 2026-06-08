import FX1Poly.Typed.DenoteKeyedLevelIrrelevance

/-! Scratch B (member-level complement of A2): general member-stability for any type reducible with a SINGLE
candidate uniform across ALL denote levels. The universe-domain member-stability
(`universeDomainPi_memberStableAcrossDenoteLevels`) is uniform only ABOVE `denote e env`; for uniform-candidate
types (neutral, data, uniform-candidate Π) the candidate is uniform at EVERY level, so member-stability holds
unconditionally via determinism. The member-level analogue of `uniformDomainPi_reducibleAtEveryDenoteLevel`. -/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **Member-stability for a uniform-candidate type.**  If `typeCode` is reducible with a single candidate
`candidate` at every denote level, then a reducible member at one level is a reducible member at every level —
the source-level candidate agrees pointwise with the uniform `candidate` by determinism, so the member sits in
`candidate`, which is reducible at the target level.  Unconditional (no level threshold): the candidate never
drifts.  The member analogue of `uniformDomainPi_reducibleAtEveryDenoteLevel`. -/
theorem uniformType_memberStableAcrossDenoteLevels {scope : Nat} (env : Nat → Nat)
    {typeCode : RawTerm scope} {candidate : RawTerm scope → Prop}
    (uniformReducible : ∀ level : Nat, ReducibleTypeAtDenote env level typeCode candidate)
    {term : RawTerm scope} {sourceLevel : Nat}
    (memberAtSource : IsReducibleMemberAtDenote env sourceLevel typeCode term)
    (targetLevel : Nat) :
    IsReducibleMemberAtDenote env targetLevel typeCode term := by
  obtain ⟨sourceCandidate, sourceReducible, memberInSource⟩ := memberAtSource
  have candidatesAgree :=
    ReducibleTypeAtDenote.deterministic sourceReducible (uniformReducible sourceLevel)
  exact ⟨candidate, uniformReducible targetLevel, (candidatesAgree term).mp memberInSource⟩

/-- **Member-stability for a neutral type (witnessing instance).**  A weak-head-normal non-Π non-universe type
has the literally-uniform candidate `IsStronglyNormalizing` at every level (the `neutral` arm), so its members
are level-stable. -/
theorem neutralType_memberStableAcrossDenoteLevels {scope : Nat} (env : Nat → Nat)
    {typeCode : RawTerm scope}
    (noWeakHeadStep : ∀ reduct : RawTerm scope, ¬ WeakHeadStep typeCode reduct)
    (notPiType : typeCode.rootGenerator ≠ Generator.gen_piTyCode)
    (notUniverse : typeCode.rootGenerator ≠ Generator.gen_universeCode)
    {term : RawTerm scope} {sourceLevel : Nat}
    (memberAtSource : IsReducibleMemberAtDenote env sourceLevel typeCode term)
    (targetLevel : Nat) :
    IsReducibleMemberAtDenote env targetLevel typeCode term :=
  uniformType_memberStableAcrossDenoteLevels env
    (fun _level => ReducibleTypeStepDenote.neutral noWeakHeadStep notPiType notUniverse)
    memberAtSource targetLevel

end FX1Poly.Typed

#print axioms FX1Poly.Typed.uniformType_memberStableAcrossDenoteLevels
#print axioms FX1Poly.Typed.neutralType_memberStableAcrossDenoteLevels
