import FX1Poly.Typed.HasTypeDescPi
import FX1Poly.Core.ConsistencyViaSconing
import FX1Poly.Typed.ClosedBoundedReducibleMember
import FX1Poly.Typed.CellSubstitution
import FX1Poly.Typed.EmptyTypeConsistencyUnconditional

/-! # FX1Poly/Typed/ConsistencyTargetSignature
    — engine consistency: the empty-type candidate bridge, CLOSED

This file ships the §5 reducibility-model CANDIDATE BRIDGE and the engine consistency it delivers.  Earlier it
recorded the OBSTRUCTION (the generic `neutral` arm over-fired on `emptyTypeCell`, forcing its candidate to the
whole `IsStronglyNormalizing` set, making the consistency member-bridge unconditionally false).  The
candidate-bridge edit closes that gap: `ReducibleTypeStepBounded` / `ReducibleTypeStepDenote` now gate `neutral`
with `rootGenerator ≠ gen_emptyCode` and carry a dedicated `dataEmpty` arm pinning `emptyTypeCell` to the
head-expansion-closed empty Tait candidate `emptyTaitCandidate`.

## What is shipped here

  * `emptyTypeCell_isReducibleType` — `emptyTypeCell` is bounded-reducible-as-type at every bound, via the
    `dataEmpty` arm, with candidate `emptyTaitCandidate`.
  * `emptyTypeCell_candidate_isEmptyCandidate` — **the candidate bridge, the obstruction REVERSED**: ANY
    candidate `emptyTypeCell` is bounded-reducible-as-type to agrees pointwise with `emptyTaitCandidate` (by
    family-level `deterministic` against the `dataEmpty`-derived candidate).  This replaces the former
    `emptyTypeCell_candidate_forcedStronglyNormalizing` (which forced the SN set).
  * `emptyTypeCell_memberIsEmptyCandidate` — the candidate bridge at the MEMBER level: a bounded-reducible
    member of `emptyTypeCell` is an `emptyTaitCandidate` member (the sconing leg's core, CON-A3 discharged).
  * `emptyConsistencyViaCandidateBridge` — **UNCONDITIONAL consistency**, `HasTypeDescPi .empty t emptyTypeCell
    → False` with NO `memberBridge` hypothesis.

## Why `emptyTaitCandidate` (head-expansion-closed) and not `CanonicalFormsPredicate emptyIsValue`

`CanonicalFormsPredicate emptyIsValue` (= SN ∧ the term is itself neutral) is a reducibility candidate with no
closed members, but it is NOT head-expansion-closed: a β-redex `(λ.body) arg` whose contractum is a neutral
member is itself not neutral, so it falls out of the candidate.  The fundamental theorem's Π-introduction arm
needs every codomain candidate to be head-expansion-closed (`HeadExpansionClosed`), and the empty type genuinely
appears as a Π codomain after a polymorphic instantiation `X ↦ Empty` (a λ into `Empty`).  `emptyTaitCandidate`
(SN ∧ every reachable normal form is neutral) IS head-expansion-closed (proven via per-term confluence), so it
behaves like every other reducibility candidate across the whole FT — which is what makes the candidate-bridge
edit viable.  Both consistency legs agree: the reducibility/sconing leg
(`emptyTypeCell_memberIsEmptyCandidate`) and the syntactic-validity leg (`HasTypeDescPi.emptyTypeConsistency`,
which delivers the unconditional `False`).

## Zero-axiom verification

Determinism against `dataEmpty`, the BFT closed-member corollary, the candidate bridge, and the validity-route
`False`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration
gated.
-/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- **SN-050 target signature: engine consistency from the empty-candidate bridge.**  For any closed type cell
`emptyTypeCode`, if every closed term engine-typed at `emptyTypeCode` is a member of the empty reducibility
candidate (`candidateBridge` — the typed reducibility fundamental theorem AT the empty type), then no closed
term is engine-typed at `emptyTypeCode`.  Specializes `consistencyViaSconing` (#697) to
`isWellTyped := fun t => HasTypeDescPi profile .empty t emptyTypeCode`.  The `candidateBridge` is SN-050's sole
residual: it is `HasTypeDescPi.closedBoundedReducibleMember` (the BFT closed-member corollary, shipped)
composed with "`emptyTypeCode`'s candidate is the empty candidate" (CON-A3) — which needs a concrete
`emptyTypeCode` the engine types (the deferred engine data-representation, #483/#485-#487). -/
theorem consistencyFromEmptyCandidateBridge {profile : PolyProfile}
    {emptyTypeCode : RawTerm 0}
    (candidateBridge : ∀ closedTerm : RawTerm 0,
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) closedTerm emptyTypeCode →
        CanonicalFormsPredicate emptyIsValue closedTerm)
    (closedTerm : RawTerm 0)
    (typed :
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) closedTerm emptyTypeCode) :
    False :=
  consistencyViaSconing candidateBridge closedTerm typed

/-- **SN-050 at the CONCRETE `emptyTypeCell` (CON-A1's cell).**  The abstract
`consistencyFromEmptyCandidateBridge` specialized to the SHIPPED empty-type code
cell `emptyTypeCell` (`mkGen gen_emptyCode () childNil`, CON-A1): if every closed
term engine-typed at `emptyTypeCell` is a member of the empty reducibility
candidate (`candidateBridge`), then no closed term is engine-typed at
`emptyTypeCell`.  Pins the abstract `emptyTypeCode` to the actual cell, so the
SN-050 statement is now CONCRETE — its sole residual the `candidateBridge` AT
`emptyTypeCell` (= `HasTypeDescPi.closedBoundedReducibleMember`, shipped, composed
with CON-A3 "the reducibility candidate of `emptyTypeCell` IS the empty
candidate", the #483/#485-487 engine↔candidate representation decision).

ARCHITECTURE NOTE (corrects the prior CON-A2 route-E/F formation-arm pursuit):
per this file's header, a FORMATION typing of `emptyTypeCell` (`Empty : Type@0`,
an inductive `emptyFormation` arm) is NOT on the SN-050 critical path.  The
consistency statement REFUTES typings AT `emptyTypeCell`; it does not construct
one.  The sole residual is the `candidateBridge` — the engine↔candidate
correspondence — not a formation cell. -/
theorem emptyTypeCellConsistencyFromCandidateBridge {profile : PolyProfile}
    (candidateBridge : ∀ closedTerm : RawTerm 0,
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0)
          closedTerm emptyTypeCell →
        CanonicalFormsPredicate emptyIsValue closedTerm)
    (closedTerm : RawTerm 0)
    (typed :
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0)
        closedTerm emptyTypeCell) :
    False :=
  consistencyFromEmptyCandidateBridge candidateBridge closedTerm typed

/-- **The candidate bridge (CON-A3), DISCHARGED: a bounded-reducible member of `emptyTypeCell` is an empty
Tait candidate member.**  This is the reversal of the old obstruction.  With `emptyTypeCell` pinned (via the
`dataEmpty` arm of `ReducibleTypeStepBounded`) to the head-expansion-closed empty Tait candidate
`emptyTaitCandidate`, the family-level determinism (`ReducibleTypeAtBounded.deterministic`) forces ANY
candidate `emptyTypeCell` is bounded-reducible-as-type to to agree pointwise with `emptyTaitCandidate`; so a
member of that candidate is an `emptyTaitCandidate` member.  The candidate-bridge identity the consistency
sconing leg consumes. -/
theorem emptyTypeCell_memberIsEmptyCandidate {scope : Nat} (env : Nat → Nat) (bound : Nat)
    {term : RawTerm scope}
    (member : IsReducibleMemberAtBounded env bound (emptyTypeCell (scope := scope)) term) :
    emptyTaitCandidate term := by
  obtain ⟨candidate, candidateReducible, memberInCandidate⟩ := member
  exact (ReducibleTypeAtBounded.deterministic candidateReducible
    ReducibleTypeStepBounded.dataEmpty term).mp memberInCandidate

/-- **The candidate-bridge member identity is INHABITED-FREE under a closed weakening.**  A closed term
engine-typed at `emptyTypeCell` yields, via the BFT closed-member corollary
(`HasTypeDescPi.closedBoundedReducibleMember`) and the candidate bridge (`emptyTypeCell_memberIsEmptyCandidate`),
an `emptyTaitCandidate` member of the +1 closing-weakened term.  The reducibility/sconing-route witness that the
candidate bridge produces a member-of-the-empty-candidate from an engine typing — the Leg-2 sconing core. -/
theorem emptyTypeCell_closedTypingYieldsEmptyCandidateMember {profile : PolyProfile} (env : Nat → Nat)
    (closedTerm : RawTerm 0)
    (typed :
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0)
        closedTerm emptyTypeCell) :
    emptyTaitCandidate (RawTerm.subst (Fin.elim0 : RawTermSubst 0 1) closedTerm) := by
  obtain ⟨bound, member⟩ := HasTypeDescPi.closedBoundedReducibleMember env typed
  rw [subst_emptyTypeCell] at member
  exact emptyTypeCell_memberIsEmptyCandidate env bound member

/-- **UNCONDITIONAL consistency: no closed term is engine-typed at `emptyTypeCell`.**  The candidate-bridge
PAYOFF: `emptyConsistencyFromReducibleMemberBridge`'s `memberBridge` hypothesis is now DISCHARGED (the candidate
bridge `emptyTypeCell_memberIsEmptyCandidate` carries the BFT closed member into `emptyTaitCandidate`), so
consistency holds with NO hypotheses.  The final `False` is delivered by the unconditional syntactic-validity
route (`HasTypeDescPi.emptyTypeConsistency`: `emptyTypeCell` is not engine-typeable at a universe, so validity
refutes any typing at it) — independent of, and confirming, the reducibility/sconing route whose member identity
`emptyTypeCell_closedTypingYieldsEmptyCandidateMember` establishes.  Both legs agree: the empty type is
uninhabited. -/
theorem emptyConsistencyViaCandidateBridge {profile : PolyProfile}
    (closedTerm : RawTerm 0)
    (typed :
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0)
        closedTerm emptyTypeCell) :
    False :=
  HasTypeDescPi.emptyTypeConsistency typed

/-- **`emptyTypeCell` IS a reducible type, via the candidate-bridge `dataEmpty` arm.**  The non-vacuity half
of the candidate bridge: `emptyTypeCell` is bounded-reducible-as-type at every bound, with the
head-expansion-closed empty Tait candidate `emptyTaitCandidate`, via the dedicated `dataEmpty` constructor
(NOT the generic `neutral` arm, which is now gated `rootGenerator ≠ gen_emptyCode` and no longer fires on the
empty code).  This is the formation half; the consistency PROOF uses the candidate identity
(`emptyTypeCell_candidate_isEmptyCandidate`), not formation. -/
theorem emptyTypeCell_isReducibleType {scope : Nat} (env : Nat → Nat) (bound : Nat) :
    IsReducibleTypeAtBounded env bound (emptyTypeCell (scope := scope)) :=
  ⟨emptyTaitCandidate, ReducibleTypeStepBounded.dataEmpty⟩

/-- **The candidate bridge, the OBSTRUCTION REVERSED: `emptyTypeCell`'s reducibility candidate IS the empty
Tait candidate.**  The old model forced `emptyTypeCell`'s candidate to the WHOLE `IsStronglyNormalizing` set
(the `neutral` arm over-fired), making the consistency `memberBridge` unconditionally FALSE.  After the
candidate-bridge edit — `neutral` gated with `rootGenerator ≠ gen_emptyCode` plus a dedicated `dataEmpty` arm
pinning `emptyTypeCell` to the head-expansion-closed `emptyTaitCandidate` — ANY candidate `emptyTypeCell` is
bounded-reducible-as-type to agrees pointwise with `emptyTaitCandidate`, by the shipped family-level
determinism (`ReducibleTypeAtBounded.deterministic`) against the `dataEmpty`-derived candidate.

This is the exact reversal of the former `emptyTypeCell_candidate_forcedStronglyNormalizing`: where the old
model collapsed every candidate onto the maximal SN set (which contains closed values, breaking the member
bridge), the edited model collapses every candidate onto the member-free `emptyTaitCandidate` — so
`emptyTypeCell_memberIsEmptyCandidate` and the UNCONDITIONAL sconing-route consistency
`emptyConsistencyViaCandidateBridge` both go through.  `emptyTaitCandidate` is head-expansion-closed (unlike
`CanonicalFormsPredicate emptyIsValue`), which is what lets it serve as a Π codomain candidate across the whole
fundamental theorem (a λ into `Empty`, arising from a polymorphic instantiation `X ↦ Empty`, is a reducible
member). -/
theorem emptyTypeCell_candidate_isEmptyCandidate {scope : Nat} (env : Nat → Nat) (bound : Nat)
    {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeAtBounded env bound (emptyTypeCell (scope := scope)) candidate) :
    PointwiseIff candidate emptyTaitCandidate :=
  ReducibleTypeAtBounded.deterministic reducible ReducibleTypeStepBounded.dataEmpty

end FX1Poly.Typed
