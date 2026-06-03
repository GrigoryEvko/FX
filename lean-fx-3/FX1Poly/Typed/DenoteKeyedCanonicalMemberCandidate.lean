import FX1Poly.Typed.DenoteKeyedReducibility

/-! # FX1Poly/Typed/DenoteKeyedCanonicalMemberCandidate
    — the choice-free canonical-codomain engine over the denote-keyed relation (#490 denote analogue)

The denote-keyed analogue of `ReducibleTypeAt.reducibleMemberCandidate` (#490): the canonical member-predicate
`IsReducibleMemberAtDenote env level typeCode` (`fun term => ∃ C, ReducibleTypeAtDenote env level typeCode C ∧
C term`) is itself a candidate the type denotes.  This is the CHOICE-FREE ENGINE the denote fundamental
theorem's Π-formation arm (route D) needs: the Π codomain can be fed the FIXED function `fun argument =>
IsReducibleMemberAtDenote env level (subst0 codomainCode argument)` and the `piType` premise discharged per
argument from mere EXISTENCE of a candidate there — no `∃ candidate` extracted, hence no `Classical.choice`.

The proof is the `ofPointwiseIff` congruence-closure arm of the denote relation applied to any existing
candidate, with the pointwise equivalence supplied by `ReducibleTypeAtDenote.deterministic`: forward picks the
given candidate (`⟨candidate, reducible, …⟩`), backward collapses an arbitrary witness candidate onto it via
determinism.  Cleaner than the fuel original — `ReducibleTypeAtDenote env level := ReducibleTypeStepDenote env
(denoteBelowFamily env level)` is uniform in `level`, so there is NO `cases level` split (the fuel proof split
only because `ReducibleTypeAt 0` and `ReducibleTypeAt (n+1)` unfold to different functors).

## Zero-axiom verification

`ReducibleTypeStepDenote.ofPointwiseIff` is the relation's own congruence constructor (introduced pointwise,
never `funext`, so no `Quot.sound`); `ReducibleTypeAtDenote.deterministic` is the shipped determinism wrapper.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated
in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- **The canonical member-predicate is the type's own candidate (denote-keyed).**  For a reducible type, the
predicate `IsReducibleMemberAtDenote env level typeCode` is itself a candidate the type denotes — built from any
existing candidate by the `ofPointwiseIff` congruence arm, the pointwise equivalence from `deterministic`
(forward picks the given candidate; backward collapses an arbitrary witness candidate onto it). -/
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

/-- **Existence of a candidate suffices for the canonical member-predicate (denote-keyed).**  The
`IsReducibleTypeAtDenote` (`∃ candidate, …`) repackaging: a denote-reducible type denotes its own
member-predicate.  The form the dependent Π-formation arm consumes — it has existence, not a chosen
candidate. -/
theorem IsReducibleTypeAtDenote.reducibleMemberCandidate {scope : Nat} {env : Nat → Nat} {level : Nat}
    {typeCode : RawTerm scope} (reducibleType : IsReducibleTypeAtDenote env level typeCode) :
    ReducibleTypeAtDenote env level typeCode (IsReducibleMemberAtDenote env level typeCode) :=
  let ⟨_candidate, reducible⟩ := reducibleType
  reducible.reducibleMemberCandidate

end FX1Poly.Typed
