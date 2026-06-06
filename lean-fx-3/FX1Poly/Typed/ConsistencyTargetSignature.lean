import FX1Poly.Typed.HasTypeDescPi
import FX1Poly.Core.ConsistencyViaSconing
import FX1Poly.Typed.ClosedBoundedReducibleMember
import FX1Poly.Typed.CellSubstitution

/-! # FX1Poly/Typed/ConsistencyTargetSignature
    — SN-050 target signature: engine consistency from the empty-candidate bridge (CON-A0 spike verdict)

This file pins the EXACT residual obligation for SN-050 (`HasTypeDescPi .empty t Empty → False`, #553) and
records the CON-A0 architectural finding.

## What is already shipped (the consistency CONTENT, abstractly)

The reducibility/sconing layer carries consistency in full, parameterized over an ABSTRACT well-typedness
predicate:

  * `emptyCanonicalFormsCandidate` (#680) — the empty type's Tait candidate `CanonicalFormsPredicate
    emptyIsValue` with `emptyIsValue = fun _ => False`, a full reducibility candidate.
  * `emptyHasNoClosedMember` (#680, `#672`-free) — no closed term inhabits it (a closed member reduces to a
    value, but an empty value is a proof of `False`).
  * `consistencyViaSconing` (#697) — given the `fundamental` (closed well-typed empty term ⟹ empty-candidate
    member), every closed well-typed term of the empty type yields `False`.

## The CON-A0 finding (architecture redirect)

The data types (bool, Nat, pair, EMPTY, …) are NOT represented as engine cells: there is no `gen_bool`,
`gen_nat`, or `gen_empty` type-former in the 194-generator table (only VALUE generators like `gen_boolFalse`
and `gen_unit`).  Each data type IS its value-predicate reducibility candidate (`boolIsValue`, `IsNatValue`,
`emptyIsValue`).  Correspondingly, the typed engine `HasTypeDescPi` does NOT type data — `typingRuleDescOf`
is `some` only for `gen_piTyCode` / `gen_sigmaTyCode`, so `genFormationPi` fires only for Π/Σ.

Consequence: the plan's CON-A1/A2 ("`typingRuleDescOf` Empty-formation row", "HasTypeDescPi Γ EmptyType
Type@0") MISMODEL the architecture — they presuppose an `EmptyType` genFormation cell that does not exist,
and adding one is a full generator cascade (#483 "cascade-death").  The SAME engine↔candidate gap blocks ALL
of Phase A: canonicity (SN-047/048/049) equally needs the engine to type bool/Nat/data.  The metatheory is
done; the bottleneck is purely "the engine names + types data types, and the engine type's reducibility
candidate is the data candidate" — a Path-A engine-representation decision (#483 / #485-#487), NOT five
Empty-specific lemmas.

## The target signature

`consistencyFromEmptyCandidateBridge` specializes `consistencyViaSconing` to the ENGINE typing predicate,
abstracted over the (still-missing) `emptyTypeCode`.  It isolates SN-050's sole residual as the explicit
`candidateBridge` hypothesis: closed engine-typing at `emptyTypeCode` ⟹ empty-candidate membership.  That
bridge = the BFT closed-member corollary (`HasTypeDescPi.closedBoundedReducibleMember`, shipped) composed with
"`emptyTypeCode`'s reducibility candidate IS the empty candidate" (CON-A3) — the latter needing a concrete
`emptyTypeCode` the engine types.  So SN-050's final wire is a one-liner over this signature; the genuine work
is the engine data-representation, deliberately deferred here, not faked.

## Zero-axiom verification

A one-line composition of the shipped `consistencyViaSconing` with the engine typing predicate.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated.
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

/-- **SN-050 residual reduced to the CANDIDATE IDENTITY (CON-A3 core), wiring the shipped
FT closed-member corollary.**  `emptyTypeCellConsistencyFromCandidateBridge` left
`candidateBridge` (closed engine-typing AT `emptyTypeCell` ⟹ empty-candidate membership) as
the residual.  Here we discharge HALF of it with the SHIPPED
`HasTypeDescPi.closedBoundedReducibleMember` (the BFT closed-member corollary: a closed term
engine-typed at a closed classifier is a bounded-reducible member of that classifier under the
unique closing weakening), so the residual drops to the cleaner `memberBridge` — CON-A3 core:
a bounded-reducible member of `emptyTypeCell` is an empty-candidate member.

Given `memberBridge`, no closed term is engine-typed at `emptyTypeCell`.  Proof: the FT
closed-member corollary gives a bounded-reducible member at `subst Fin.elim0 emptyTypeCell`,
which `subst_emptyTypeCell` (the closed nullary leaf is substitution-invariant) simplifies to
`emptyTypeCell`; `memberBridge` carries it to an empty-candidate member of the closed term,
contradicting `emptyHasNoClosedMember` (#680).

`memberBridge` IS CON-A3 — the engine↔candidate representation identity (`emptyTypeCell`'s
FT-reducibility candidate is the empty candidate, #483/#485-487), now SN-050's sole remaining
residual with every other piece (FT closed-member, `subst_emptyTypeCell`, `emptyHasNoClosedMember`)
shipped and wired. -/
theorem emptyConsistencyFromReducibleMemberBridge {profile : PolyProfile} (env : Nat → Nat)
    (memberBridge : ∀ (closedTerm : RawTerm 0) (bound : Nat),
      IsReducibleMemberAtBounded env bound emptyTypeCell
          (RawTerm.subst (Fin.elim0 : RawTermSubst 0 1) closedTerm) →
        CanonicalFormsPredicate emptyIsValue closedTerm)
    (closedTerm : RawTerm 0)
    (typed :
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0)
        closedTerm emptyTypeCell) :
    False := by
  obtain ⟨bound, member⟩ := HasTypeDescPi.closedBoundedReducibleMember env typed
  rw [subst_emptyTypeCell] at member
  exact emptyHasNoClosedMember (memberBridge closedTerm bound member)

/-- **The CON-A3 OBSTRUCTION, mechanized: `emptyTypeCell`'s DEFAULT reducibility candidate is the
MAXIMAL one (`IsStronglyNormalizing`), NOT the empty candidate.**  `emptyTypeCell` is weak-head-normal
(no `WeakHeadStep` — `gen_emptyCode` heads no β/ι and has no children: every `WeakHeadStep`
constructor save the generic `rootIota` pins a concrete eliminable head ≠ `gen_emptyCode`, and
`rootIota`'s `IotaHeadStep` is uninhabited on `gen_emptyCode`), and its root generator is neither
`gen_piTyCode` nor `gen_universeCode`.  So the `ReducibleTypeStepBounded.neutral` arm fires and gives
`emptyTypeCell` the candidate `IsStronglyNormalizing` — the WHOLE SN set.

This is the precise reason CON-A3 (memberBridge in `emptyConsistencyFromReducibleMemberBridge`) is
FALSE under the default interpretation: `IsStronglyNormalizing` contains closed VALUES (e.g. a closed
`gen_lam`), which are NOT empty-candidate members (`CanonicalFormsPredicate emptyIsValue` = SN ∧
neutral-or-False-value = SN ∧ neutral, member-free among closed terms by #680).  So
`IsReducibleMemberAtBounded env bound emptyTypeCell` is INHABITED (any SN term) ⟹ memberBridge's
premise holds for closed values whose conclusion fails.  CON-A3 therefore requires an INTERPRETATION
CHANGE — excluding `emptyTypeCell` (data type codes) from the generic `neutral` arm (add a
`rootGenerator ≠ gen_emptyCode` side-condition) and a dedicated arm giving it the empty Tait candidate
— a structural edit to `ReducibleTypeStepBounded` cascading through its consumers (the
§5 engine↔candidate representation decision).  Positive corollary: `emptyTypeCell` IS a reducible
type (`IsReducibleTypeAtBounded`), the non-vacuity half, in the reducibility model.  (The candidate is
existentially hidden here; the `neutral` arm pins it to the WHOLE `IsStronglyNormalizing` set — the obstruction
described above.) -/
theorem emptyTypeCell_isReducibleType {scope : Nat} (env : Nat → Nat) (bound : Nat) :
    IsReducibleTypeAtBounded env bound (emptyTypeCell (scope := scope)) := by
  have noWeakHeadStep : ∀ reduct : RawTerm scope,
      ¬ WeakHeadStep (emptyTypeCell (scope := scope)) reduct := by
    intro reduct weakHeadStep
    dsimp only [emptyTypeCell] at weakHeadStep
    cases weakHeadStep with
    | rootIota iotaStep => cases iotaStep
  exact ⟨_, ReducibleTypeStepBounded.neutral noWeakHeadStep
    (by show Generator.gen_emptyCode ≠ Generator.gen_piTyCode; decide)
    (by show Generator.gen_emptyCode ≠ Generator.gen_universeCode; decide)⟩

/-- **The CON-A3 obstruction made AIRTIGHT: `emptyTypeCell`'s reducibility candidate is not merely
SN-by-default but FORCED to be the whole SN set.**  `emptyTypeCell_isReducibleType` exhibits ONE candidate
(`IsStronglyNormalizing`, via the `neutral` arm); this strengthens it to UNIQUENESS — ANY `candidate` with
`ReducibleTypeAtBounded env bound emptyTypeCell candidate` is `PointwiseIff IsStronglyNormalizing`, by the
shipped family-level determinism (`ReducibleTypeAtBounded.deterministic`) against that neutral-derived SN
candidate.

This closes the obstruction airtight: the `memberBridge` premise in `emptyConsistencyFromReducibleMemberBridge`
is UNCONDITIONALLY false in the current model.  There is NO escape via a smarter candidate — not even through
the congruence-closure `ofPointwiseIff` arm — because every candidate collapses (up to `PointwiseIff`) onto the
SN set, and the SN set contains closed VALUES (a closed `gen_lam`) that are never empty-candidate members
(`emptyHasNoClosedMember`, #680).  So `memberBridge` cannot be re-derived inside `ReducibleTypeStepBounded`; it
MANDATES the structural edit (a `rootGenerator ≠ gen_emptyCode` side-condition on `neutral` PLUS a dedicated
arm pinning `emptyTypeCell` to the empty Tait candidate), cascading through the forget bridge into
`ReducibleTypeStepDenote` and its consumers (#483/#485-487, the §5 engine↔candidate representation decision).
This is the precise certificate that CON-A3 is not a grind but a model change. -/
theorem emptyTypeCell_candidate_forcedStronglyNormalizing {scope : Nat} (env : Nat → Nat) (bound : Nat)
    {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeAtBounded env bound (emptyTypeCell (scope := scope)) candidate) :
    PointwiseIff candidate StepStar.IsStronglyNormalizing := by
  have noWeakHeadStep : ∀ reduct : RawTerm scope,
      ¬ WeakHeadStep (emptyTypeCell (scope := scope)) reduct := by
    intro reduct weakHeadStep
    dsimp only [emptyTypeCell] at weakHeadStep
    cases weakHeadStep with
    | rootIota iotaStep => cases iotaStep
  have stronglyNormalizingReducible :
      ReducibleTypeAtBounded env bound (emptyTypeCell (scope := scope)) StepStar.IsStronglyNormalizing :=
    ReducibleTypeStepBounded.neutral noWeakHeadStep
      (by show Generator.gen_emptyCode ≠ Generator.gen_piTyCode; decide)
      (by show Generator.gen_emptyCode ≠ Generator.gen_universeCode; decide)
  exact ReducibleTypeAtBounded.deterministic reducible stronglyNormalizingReducible

end FX1Poly.Typed
