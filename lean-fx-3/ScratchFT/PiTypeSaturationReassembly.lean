import FX1Poly.Typed.FundamentalAtAllPositiveArguments

namespace FX1Poly.Typed

open FX1Poly.Core
open FX1Poly.Foundation
open StepStar

-- Pi TYPE-saturation reassembly (inverse of domainOfPiType / codomainOfPiTypeAtAllPositiveArgument).
-- Conditional inductive arm (matching the existing conditional-arm style): given the domain all-positive,
-- domain members fuel-stable (domain IH), and codomain all-positive per all-positive arg (codomain IH),
-- the Pi type is reducible at all positive levels. Choice-free via reducibleMemberCandidate.
theorem ofPiType_probe {scope : Nat} {dom : RawTerm scope} {cod : RawTerm (scope + 1)}
    (domainAllPositive : IsReducibleTypeAtAllPositiveLevels dom)
    (domainMembersStable : ∀ {arg : RawTerm scope} {predLevel : Nat},
        IsReducibleMemberAt (predLevel + 1) dom arg → IsReducibleMemberAtAllPositiveLevels dom arg)
    (codomainAllPositive : ∀ {arg : RawTerm scope},
        IsReducibleMemberAtAllPositiveLevels dom arg →
        IsReducibleTypeAtAllPositiveLevels (RawTerm.subst0 cod arg)) :
    IsReducibleTypeAtAllPositiveLevels
      (.mkGen .gen_piTyCode () (.childCons dom (.childCons cod .childNil))) := by
  intro predLevel
  obtain ⟨domCand, domReducible⟩ := domainAllPositive predLevel
  refine ⟨_, ReducibleTypeStep.piType
    (fun arg => IsReducibleMemberAt (predLevel + 1) (RawTerm.subst0 cod arg))
    domReducible ?_⟩
  intro arg argInDomCand
  have argMember : IsReducibleMemberAt (predLevel + 1) dom arg := ⟨domCand, domReducible, argInDomCand⟩
  have codReducibleType : IsReducibleTypeAt (predLevel + 1) (RawTerm.subst0 cod arg) :=
    codomainAllPositive (domainMembersStable argMember) predLevel
  exact codReducibleType.reducibleMemberCandidate

end FX1Poly.Typed
