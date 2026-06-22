import FX1Poly.Typed.Metatheory.Reducibility.Candidate.ReducibilityCandidateDesc
import FX1Poly.Core.Metatheory.Reducibility.Candidates.ReducibilityCandidate

/-! # FX1Poly/Typed/Metatheory/Reducibility/Candidate/CandidateDenotation
    — the candidate DENOTATION + the CandidateValidity obligation interface (FTGEN-1 proof layer)

`ReducibilityCandidateDesc` (the sibling file) names, as data, the SHAPE of every former's reducibility
candidate.  This file connects those shapes to the actual candidate predicates and to the validity obligation
each must satisfy — the half of FTGEN-1 that touches proofs, and the interface FTGEN-2 discharges per shape.

## The interface IS the kernel's Girard CR record (no new structure)

`CandidateValidity` is a `@[reducible]` alias of the shipped `FX1Poly.Core.IsReducibilityCandidate`
(ReducibilityCandidate.lean): CR1 `stronglyNormalizing` (members are SN), CR2 `closedUnderStep` (forward
closure under bare `Step`), CR3 `neutralExpansion` (a neutral whose every reduct is a member is a member).
Reusing it — rather than declaring a parallel record — keeps the arc speaking the kernel's vocabulary, so a
discharged obligation feeds the existing fundamental-theorem / canonicity machinery directly.

## What this file proves now (the two shape-generic validity facts)

  * `neutralSaturatedCandidate_valid` — the `neutralSaturated` shape's denotation is `IsStronglyNormalizing`,
    a valid candidate by the kernel's `isStronglyNormalizing_isReducibilityCandidate`.  This is the CR3 base
    every other candidate is carved from.
  * `derivedUnfoldCandidate_valid` — the `derivedUnfold` shape (e.g. `equivCode A B` DEFINED as the candidate
    of its unfolding `Σ(f:A→B), isEquiv f`) inherits validity from the unfolding for FREE, via the kernel's
    `respectsPointwiseIff`.  No new CR proof — the cheap univalence-RHS unlock, decoupled from whether the
    unfolding is also a definitional reduction (that is EXT-4).
  * `CandidateValidity.containsVariable` — re-exposes CR3 nonemptiness (every valid candidate holds the
    context variables) at the arc level.

## Per-shape denotation/validity roster (the FTGEN-2 worklist)

  * `neutralSaturated`  — `IsStronglyNormalizing`; VALID now (here).
  * `derivedUnfold`     — the unfolding's candidate; VALID now (here, given the unfolding valid).
  * `dependentProduct`  — the function-space candidate (`piType` arm); validity already proven for the Π arm
    in `Core/.../StratifiedReducibleTypeReducibilityCandidate`; FTGEN-2 keys it on the descriptor.
  * `inductiveSaturated`— the `dataFlat`/Tait saturated set; validity available via the data arm; FTGEN-2 +
    the eliminator-induction (FTGEN-11) consume the descriptor's constructor specs.
  * `universeCandidate` — the `universeCode` arm (level-gated); FTGEN-2.
  * `dependentSum`      — NEW Σ arm (no `sigmaType` arm yet); FTGEN-2.
  * `identitySaturated` — NEW (Id / idStrict); FTGEN-2 (FTGEN-7).
  * `relationalSaturated` — NEW (gel/bridge/transpension); FTGEN-2 (FTGEN-GEL).
  * `strictPropIrrelevant` — NEW (sprop); FTGEN-2 (EXT-6).
  * `coinductiveSaturated` / `quotientByRelation` / `propTruncated` / `modalCandidate` — reserved frontier;
    FTGEN-2 when their formers enter the bundle.

## Zero-axiom verification

A `@[reducible]` alias + two theorems that are direct applications of the shipped kernel CR lemmas
(`isStronglyNormalizing_isReducibilityCandidate`, `IsReducibilityCandidate.respectsPointwiseIff`,
`IsReducibilityCandidate.containsVariable`).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core
open StepStar

/-- **The candidate-validity obligation** for the FTGEN arc — definitionally the kernel's Girard reducibility
candidate `IsReducibilityCandidate` (CR1 strongly-normalizing / CR2 closed-under-step / CR3 neutral-expansion
over bare `Step`).  FTGEN-2 supplies one of these per `ReducibilityCandidateDesc` shape. -/
@[reducible] def CandidateValidity {scope : Nat} (candidate : RawTerm scope → Prop) : Prop :=
  IsReducibilityCandidate candidate

/-- The denotation of the `neutralSaturated` shape: the strong-normalization predicate — the CR3 base every
other candidate is carved from. -/
@[reducible] def neutralSaturatedCandidate (scope : Nat) : RawTerm scope → Prop :=
  IsStronglyNormalizing

/-- **★ The `neutralSaturated` denotation is a valid candidate.**  Directly the kernel base
`isStronglyNormalizing_isReducibilityCandidate`. -/
theorem neutralSaturatedCandidate_valid {scope : Nat} :
    CandidateValidity (neutralSaturatedCandidate scope) :=
  isStronglyNormalizing_isReducibilityCandidate

/-- **★ The `derivedUnfold` validity transfer — the equiv⇒Σ unlock.**  A candidate pointwise-equal to a valid
candidate is itself valid, so a former whose candidate is DEFINED as another former's (`equivCode A B` :=
`Σ(f:A→B), isEquiv f`) inherits CR1/CR2/CR3 for free.  Reuses the kernel `respectsPointwiseIff`; no new proof
obligation beyond the unfolding's own validity. -/
theorem derivedUnfoldCandidate_valid {scope : Nat}
    {unfoldCandidate derivedCandidate : RawTerm scope → Prop}
    (unfoldValid : CandidateValidity unfoldCandidate)
    (sameMembers : ∀ term : RawTerm scope, unfoldCandidate term ↔ derivedCandidate term) :
    CandidateValidity derivedCandidate :=
  unfoldValid.respectsPointwiseIff sameMembers

/-- Every valid candidate holds the context variables (CR3 nonemptiness) — the arc-level re-export of the
kernel `IsReducibilityCandidate.containsVariable`, the nonemptiness the formation/intro arms consume. -/
theorem CandidateValidity.containsVariable {scope : Nat} {candidate : RawTerm scope → Prop}
    (valid : CandidateValidity candidate) (index : Fin scope) :
    candidate (.mkGen .gen_var index .childNil) :=
  IsReducibilityCandidate.containsVariable valid index

end FX1Poly.Typed
