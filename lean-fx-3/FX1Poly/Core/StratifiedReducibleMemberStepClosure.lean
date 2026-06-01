import FX1Poly.Core.StratifiedReducibleMember

/-! # Foundation/PolyCell/Core/StratifiedReducibleMemberStepClosure
    — CR2 / CR3 closure lifted to the semantic-membership layer

`StratifiedReducibleMember` exposes CR1 at the membership layer
(`IsReducibleMemberAt.stronglyNormalizing`: every member strongly normalizes) but not the other two
Girard reducibility-candidate conditions.  This file lifts them from the `IsReducibilityCandidate`
bundle (`ReducibleTypeAt.isReducibilityCandidate`) to `IsReducibleMemberAt`:

  * `IsReducibleMemberAt.closedUnderStep` — **CR2** (forward closure): a reducible member stays a
    reducible member after one `Step` (same type, same candidate; the candidate's CR2 advances the
    membership witness).
  * `IsReducibleMemberAt.closedUnderStepStar` — the reflexive-transitive iteration of CR2 along a whole
    `StepStar` chain (a plain relation induction with the membership kept in the implication goal, so the
    inducted chain carries no fixed member hypothesis).
  * `IsReducibleMemberAt.neutralExpansion` — **CR3** (backward closure for neutrals): a neutral term all
    of whose one-step reducts are reducible members of a reducible type is itself a reducible member.  The
    reducts' memberships are realigned onto the type's own candidate by
    `ReducibleTypeAt.deterministic` before the candidate's CR3 fires.

These are the membership-layer closure bricks the fundamental theorem's neutral case (a stuck eliminator
or variable is a member once its reducts are) and any reduction-stable membership argument consume — the
forward (CR2) and backward-neutral (CR3) companions of the already-shipped CR1 membership corollary.

## Level and scope discipline

The `IsReducibilityCandidate` bundle is available only at a positive fuel (`predLevel + 1`) and a non-empty
scope (`RawTerm (scope + 1)`) — exactly the regime the all-positive-levels fundamental-theorem predicate
(`IsReducibleMemberAtAllPositiveLevels`) ranges over — so every lemma here is stated there, matching the
shipped `IsReducibleMemberAt.stronglyNormalizing`.

## Zero-axiom verification

Each proof destructures the membership existential, invokes one `IsReducibilityCandidate` field, and (for
CR3) realigns candidates by `ReducibleTypeAt.deterministic`; `closedUnderStepStar` is a structural
`StepStar` induction.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or
`omega`.  Gated per declaration in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

open StepStar

/-- **CR2 at the membership layer (forward closure under one `Step`).**  A reducible member of a type is
still a reducible member after the term takes a single reduction step: the classifier and its candidate are
unchanged, and the candidate's own CR2 (`IsReducibilityCandidate.closedUnderStep`) advances the membership
witness from the redex to its reduct. -/
theorem IsReducibleMemberAt.closedUnderStep {scope : Nat} {predLevel : Nat}
    {typeCode term reduct : RawTerm (scope + 1)}
    (member : IsReducibleMemberAt (predLevel + 1) typeCode term)
    (step : Step term reduct) :
    IsReducibleMemberAt (predLevel + 1) typeCode reduct := by
  obtain ⟨candidate, reducible, candidateTerm⟩ := member
  exact ⟨candidate, reducible,
    reducible.isReducibilityCandidate.closedUnderStep candidateTerm step⟩

/-- **CR2 iterated along a `StepStar` chain.**  Forward membership closure over a whole multi-step
reduction.  The membership witness is kept in the implication goal (`candidate source → candidate target`)
so the inducted chain carries no fixed member hypothesis over its source index; each `trans` head step is
discharged by the candidate's CR2. -/
theorem IsReducibleMemberAt.closedUnderStepStar {scope : Nat} {predLevel : Nat}
    {typeCode term reduct : RawTerm (scope + 1)}
    (member : IsReducibleMemberAt (predLevel + 1) typeCode term)
    (reduction : StepStar term reduct) :
    IsReducibleMemberAt (predLevel + 1) typeCode reduct := by
  obtain ⟨candidate, reducible, candidateTerm⟩ := member
  refine ⟨candidate, reducible, ?_⟩
  have candidateClosedStar : ∀ {source target : RawTerm (scope + 1)},
      StepStar source target → candidate source → candidate target := by
    intro source target chain
    induction chain with
    | refl => exact id
    | trans headStep _restChain ihRest =>
        exact fun candidateSource =>
          ihRest (reducible.isReducibilityCandidate.closedUnderStep candidateSource headStep)
  exact candidateClosedStar reduction candidateTerm

/-- **CR3 at the membership layer (backward closure for neutral terms).**  A neutral term every one-step
reduct of which is a reducible member of a reducible type is itself a reducible member.  The type supplies
its candidate; each reduct's membership (carried by an arbitrary witness candidate) is realigned onto that
candidate by `ReducibleTypeAt.deterministic`, after which the candidate's CR3
(`IsReducibilityCandidate.neutralExpansion`) admits the neutral term. -/
theorem IsReducibleMemberAt.neutralExpansion {scope : Nat} {predLevel : Nat}
    {typeCode term : RawTerm (scope + 1)}
    (typeReducible : IsReducibleTypeAt (predLevel + 1) typeCode)
    (neutral : IsNeutral term)
    (reductsMembers : ∀ reduct : RawTerm (scope + 1), Step term reduct →
      IsReducibleMemberAt (predLevel + 1) typeCode reduct) :
    IsReducibleMemberAt (predLevel + 1) typeCode term := by
  obtain ⟨candidate, reducible⟩ := typeReducible
  refine ⟨candidate, reducible,
    reducible.isReducibilityCandidate.neutralExpansion neutral ?_⟩
  intro reduct step
  obtain ⟨otherCandidate, otherReducible, otherMembership⟩ := reductsMembers reduct step
  exact (ReducibleTypeAt.deterministic otherReducible reducible reduct).mp otherMembership

end FX1Poly.Core
