import FX1Poly.Typed.DenoteKeyedGeneralDomainPiArm

/-! Scratch probe: member-transfer across weak-head reduction (both directions) + the whnfExpand domain arm
    of the #752 memberStableToOuter dispatcher. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

-- backward (head-expansion): a member of the reduct is a member of the redex (via the whnfExpand constructor).
theorem IsReducibleMemberAtDenote.headExpand {scope : Nat} {env : Nat → Nat} {level : Nat}
    {typeCode reduct : RawTerm scope} {term : RawTerm scope}
    (weakHeadStep : WeakHeadStep typeCode reduct)
    (member : IsReducibleMemberAtDenote env level reduct term) :
    IsReducibleMemberAtDenote env level typeCode term :=
  let ⟨candidate, reducible, candidateTerm⟩ := member
  ⟨candidate, ReducibleTypeStepDenote.whnfExpand weakHeadStep reducible, candidateTerm⟩

-- forward: a member of the redex is a member of the reduct (the contractum keeps the same candidate).
theorem IsReducibleMemberAtDenote.weakHeadForward {scope : Nat} {env : Nat → Nat} {level : Nat}
    {typeCode reduct : RawTerm scope} {term : RawTerm scope}
    (weakHeadStep : WeakHeadStep typeCode reduct)
    (member : IsReducibleMemberAtDenote env level typeCode term) :
    IsReducibleMemberAtDenote env level reduct term :=
  let ⟨candidate, reducible, candidateTerm⟩ := member
  ⟨candidate, ReducibleTypeStepDenote.candidateAtWhnfReduct reducible weakHeadStep, candidateTerm⟩

-- the whnfExpand domain arm: member-stability to outerLevel transfers across a domain weak-head step.
theorem whnfExpandDomainMemberStableToOuter {scope : Nat} (env : Nat → Nat) (outerLevel : Nat)
    {domainCode reduct : RawTerm scope} (weakHeadStep : WeakHeadStep domainCode reduct)
    (reductStable : ∀ (sourceLevel : Nat) (argument : RawTerm scope),
        IsReducibleMemberAtDenote env sourceLevel reduct argument →
        IsReducibleMemberAtDenote env outerLevel reduct argument)
    (sourceLevel : Nat) (argument : RawTerm scope)
    (memberAtSource : IsReducibleMemberAtDenote env sourceLevel domainCode argument) :
    IsReducibleMemberAtDenote env outerLevel domainCode argument :=
  IsReducibleMemberAtDenote.headExpand weakHeadStep
    (reductStable sourceLevel argument
      (IsReducibleMemberAtDenote.weakHeadForward weakHeadStep memberAtSource))

#print axioms IsReducibleMemberAtDenote.headExpand
#print axioms IsReducibleMemberAtDenote.weakHeadForward
#print axioms whnfExpandDomainMemberStableToOuter

end FX1Poly.Typed
