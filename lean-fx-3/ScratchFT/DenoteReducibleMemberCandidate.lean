import FX1Poly.Typed.DenoteKeyedReducibility

/-! Scratch: denote analogue of #490 (`ReducibleTypeAt.reducibleMemberCandidate`) — the canonical
member-predicate `IsReducibleMemberAtDenote env level typeCode` is itself the type's own candidate, over the
denote-keyed relation. The choice-free ENGINE the denote fundamental theorem's Π-formation arm needs: it turns
mere EXISTENCE of a codomain candidate (the IH's `∃`) into the FIXED canonical predicate, no `Classical.choice`.

Cleaner than the fuel original: `ReducibleTypeAtDenote env level := ReducibleTypeStepDenote env
(denoteBelowFamily env level)` is uniform in `level`, so NO `cases level` split (the fuel proof split only
because `ReducibleTypeAt 0`/`succ` unfold to different functors). -/

namespace FX1Poly.Typed
open FX1Poly.Core

/-- The canonical member-predicate is the type's own candidate (denote-keyed). -/
theorem ReducibleTypeAtDenote.reducibleMemberCandidate {scope : Nat} {env : Nat → Nat} {level : Nat}
    {typeCode : RawTerm scope} {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeAtDenote env level typeCode candidate) :
    ReducibleTypeAtDenote env level typeCode (IsReducibleMemberAtDenote env level typeCode) := by
  refine ReducibleTypeStepDenote.ofPointwiseIff reducible (fun term => ?_)
  constructor
  · intro candidateTerm
    exact ⟨candidate, reducible, candidateTerm⟩
  · intro member
    obtain ⟨otherCandidate, otherReducible, otherMembership⟩ := member
    exact (ReducibleTypeAtDenote.deterministic otherReducible reducible term).mp otherMembership

/-- Existence of a candidate suffices for the canonical member-predicate (denote-keyed). -/
theorem IsReducibleTypeAtDenote.reducibleMemberCandidate {scope : Nat} {env : Nat → Nat} {level : Nat}
    {typeCode : RawTerm scope} (reducibleType : IsReducibleTypeAtDenote env level typeCode) :
    ReducibleTypeAtDenote env level typeCode (IsReducibleMemberAtDenote env level typeCode) :=
  let ⟨_candidate, reducible⟩ := reducibleType
  reducible.reducibleMemberCandidate

end FX1Poly.Typed

#print axioms FX1Poly.Typed.ReducibleTypeAtDenote.reducibleMemberCandidate
#print axioms FX1Poly.Typed.IsReducibleTypeAtDenote.reducibleMemberCandidate
