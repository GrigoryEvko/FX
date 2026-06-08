import FX1Poly.Typed.DenoteKeyedReducibility

/-! Scratch: the denote Π-ELIMINATION (application) member arm. If `functionTerm` is a denote-reducible member
of `Π domainCode codomainCode` and `argumentTerm` is a denote-reducible member of `domainCode`, then
`app functionTerm argumentTerm` is a denote-reducible member of `subst0 codomainCode argumentTerm`. Reads
directly off the `piType` candidate (a Π member IS a function whose application to a domain member lands in the
codomain candidate), via piTypeInversion + deterministic (to align the argument's candidate with the Π's
domain candidate). No backward-closure, no new machinery. -/

namespace FX1Poly.Typed
open FX1Poly.Core

theorem applicationMemberAtDenote {scope : Nat} (env : Nat → Nat) (level : Nat)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {functionTerm argumentTerm : RawTerm scope}
    (functionMember : IsReducibleMemberAtDenote env level
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) functionTerm)
    (argumentMember : IsReducibleMemberAtDenote env level domainCode argumentTerm) :
    IsReducibleMemberAtDenote env level (RawTerm.subst0 codomainCode argumentTerm)
      (.mkGen .gen_app () (.childCons functionTerm (.childCons argumentTerm .childNil))) := by
  obtain ⟨piCandidate, piReducible, functionInPi⟩ := functionMember
  obtain ⟨domainCandidate, codomainCandidate, _domainReducible, codomainReducible, piCandidateIff⟩ :=
    piReducible.piTypeInversion
  have functionApplies := (piCandidateIff functionTerm).mp functionInPi
  obtain ⟨argumentCandidate, argumentReducible, argumentInCandidate⟩ := argumentMember
  have argumentInDomain : domainCandidate argumentTerm :=
    (ReducibleTypeAtDenote.deterministic argumentReducible _domainReducible argumentTerm).mp
      argumentInCandidate
  exact ⟨codomainCandidate argumentTerm, codomainReducible argumentTerm argumentInDomain,
    functionApplies argumentTerm argumentInDomain⟩

end FX1Poly.Typed

#print axioms FX1Poly.Typed.applicationMemberAtDenote
