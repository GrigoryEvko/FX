import FX1Poly.Core.NeutralTerm
import FX1Poly.Core.StepStarConfluence
import FX1Poly.Core.StrongNormalizationLeaves

/-! # Foundation/PolyCell/Core/ReducibilityCandidate — Girard CR abstraction

A **reducibility candidate** (Girard) over the bare `Step` relation is a
predicate on raw terms closed under the three CR conditions:

* **CR1** — every reducible term is strongly normalizing;
* **CR2** — reducibility is preserved going forward under one `Step`;
* **CR3** — a *neutral* term all of whose one-step reducts are reducible is
  itself reducible (backward closure restricted to neutrals).

This is the second brick of the Tait reducibility machinery
(polycell.md §11.8.5), built on the concrete `IsNeutral` predicate (the first
brick).  lean-fx-3 has no MLTT `Ty` inductive — classifiers are
`.type`-sorted `RawTerm` cells — so the machinery is Girard candidates over
`RawTerm`, not a `Ty`-indexed predicate.
The candidate abstraction here is substrate-agnostic: it is a property of a
bare term-predicate, independent of how types eventually map to candidates.

The relation throughout is `StepStar`'s bare-`Step` `IsStronglyNormalizing`
(`Acc StepSuccessor`) — the same relation the per-redex SN closures and
`IsNeutral` are stated against (β+ι; η lives in its own files).

## Zero-axiom verification

A `Prop`-valued structure plus an `Acc`-inversion / `Acc.intro` witness — no
`axiom`, `sorry`, `propext`, `Quot.sound`.  Swept by
`#audit_namespace FX1Poly.Core` in `FX1PolyAudit/AuditCoreSubstrate.lean`.
-/

namespace FX1Poly.Core

open StepStar

/-- `IsReducibilityCandidate predicate` holds when `predicate` is a Girard
reducibility candidate over the bare `Step` relation: closed under the three
CR conditions (fields below). -/
structure IsReducibilityCandidate {scope : Nat}
    (predicate : RawTerm scope → Prop) : Prop where
  /-- CR1: every reducible term is strongly normalizing. -/
  stronglyNormalizing :
    ∀ {term : RawTerm scope}, predicate term → IsStronglyNormalizing term
  /-- CR2: reducibility is preserved forward by one `Step`. -/
  closedUnderStep :
    ∀ {term reduct : RawTerm scope},
      predicate term → Step term reduct → predicate reduct
  /-- CR3: a neutral term whose every one-step reduct is reducible is itself
  reducible. -/
  neutralExpansion :
    ∀ {term : RawTerm scope}, IsNeutral term →
      (∀ reduct : RawTerm scope, Step term reduct → predicate reduct) →
        predicate term

/-- The strong-normalization predicate is itself a reducibility candidate — the
base candidate the type-code interpretation is carved out of.

CR1 is the identity.  CR2 is one-step `Acc` inversion: a reduct of an
accessible term is one of its predecessors, hence accessible.  CR3 is
`Acc.intro`: a term whose every one-step reduct is SN is SN by definition — the
neutrality hypothesis is unused here (SN is the degenerate candidate where the
closure condition collapses to plain accessibility). -/
theorem isStronglyNormalizing_isReducibilityCandidate {scope : Nat} :
    IsReducibilityCandidate (scope := scope) IsStronglyNormalizing := by
  refine ⟨?stronglyNormalizing, ?closedUnderStep, ?neutralExpansion⟩
  case stronglyNormalizing =>
    intro term isStronglyNormalizingTerm
    exact isStronglyNormalizingTerm
  case closedUnderStep =>
    intro term reduct isStronglyNormalizingTerm stepToReduct
    cases isStronglyNormalizingTerm with
    | intro _ predecessorsAccessible =>
        exact predecessorsAccessible reduct stepToReduct
  case neutralExpansion =>
    intro term _termIsNeutral reductsStronglyNormalizing
    exact Acc.intro term reductsStronglyNormalizing

/-- **Reducibility candidacy respects pointwise equivalence.**  CR1/CR2/CR3 are all membership-defined, so
transporting the predicate across a pointwise `↔` preserves candidacy: each field rewrites its hypotheses
and conclusion through the equivalence at the relevant term.  This is the congruence the stratified
relation's `ofPointwiseIff` arm consumes to keep `isReducibilityCandidate` (and the canonical
member-predicate of the dependent fundamental theorem genuinely a candidate). -/
theorem IsReducibilityCandidate.respectsPointwiseIff {scope : Nat}
    {predicate canonicalPredicate : RawTerm scope → Prop}
    (candidate : IsReducibilityCandidate predicate)
    (equivalence : ∀ term : RawTerm scope, predicate term ↔ canonicalPredicate term) :
    IsReducibilityCandidate canonicalPredicate where
  stronglyNormalizing := fun member => candidate.stronglyNormalizing ((equivalence _).mpr member)
  closedUnderStep := fun member step =>
    (equivalence _).mp (candidate.closedUnderStep ((equivalence _).mpr member) step)
  neutralExpansion := fun neutralTerm reductsMembers =>
    (equivalence _).mp (candidate.neutralExpansion neutralTerm
      (fun reduct step => (equivalence reduct).mpr (reductsMembers reduct step)))

/-- Every reducibility candidate contains all variables.  A variable is neutral
(`IsNeutral.var`) and has no reducts (`noStep_var`), so CR3's "all one-step
reducts are reducible" premise holds vacuously.  This is the
candidate-nonemptiness fact the fundamental theorem's variable case and the
arrow candidate's CR1 both consume (the latter after weakening, to obtain a
fresh argument variable). -/
theorem IsReducibilityCandidate.containsVariable {scope : Nat}
    {predicate : RawTerm scope → Prop}
    (candidate : IsReducibilityCandidate predicate) (index : Fin scope) :
    predicate (.mkGen .gen_var index .childNil) :=
  candidate.neutralExpansion (IsNeutral.var index)
    (fun _reduct step => (noStep_var index step).elim)

end FX1Poly.Core
