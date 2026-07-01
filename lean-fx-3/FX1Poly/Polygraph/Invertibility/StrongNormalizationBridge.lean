import FX1Poly.Polygraph.Invertibility.WitnessClosure
import FX1Poly.Core.Metatheory.Reducibility.Candidates.ReducibilityCandidate

/-! # FX1Poly/Polygraph/Invertibility/StrongNormalizationBridge
    — ★ strong normalization IS the inductive fixpoint of the reduct witness operator.

This is the headline of the Henry–Loubaton ↔ Tait/Girard connection.  Instantiate the generic
`WitnessOperator` (`WitnessClosure.lean`) at the kernel's one-step reduction, with

  `reductWitnessOperator.apply family term := ∀ reduct, StepSuccessor reduct term → family reduct`

— a term is "witness-closed" exactly when all of its one-step reducts already satisfy `family`.  Its two
extremal fixpoints are then the two halves FX already ships:

  * **F1 (PROVEN, this file).**  `inductiveClosure reductWitnessOperator t ↔ IsStronglyNormalizing t`.
    The kernel's `IsStronglyNormalizing := Acc StepSuccessor` IS the least fixpoint of the reduct
    operator — the `Acc = least-fixpoint` coincidence, essentially `Acc.intro` (forward) and `Acc.rec`
    (backward).  So SN is the INDUCTIVE side of the HL23 witness-closure operator.

  * **Reducibility candidates on the coinductive side (PROVEN, this file).**  A Girard reducibility
    candidate's CR2 (forward step-closure) is LITERALLY the post-fixed condition
    `IsPostFixed reductWitnessOperator predicate`, so every candidate is contained in
    `coinductiveClosure reductWitnessOperator` — the greatest fixpoint.  Least = SN, greatest ⊇ every
    candidate: the two Tait/Girard structures sit at the two fixpoints of one operator.

No published work states SN and HL23 invertibility sets as the two fixpoints of a single witness-closure
operator; both halves are reachable here only because FX ships both `Acc`-based SN and the CR abstraction.

## Zero-axiom verification

The forward bridge is `Acc.intro` under the impredicative least-fixpoint universal; the backward bridge
is `Acc`-recursion (`induction ... with | intro`), the same clean pattern as `WeakNormalization.lean`.
The candidate lemmas are direct field projections.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/Polygraph/Invertibility/StrongNormalizationBridge.lean`.
-/

namespace FX1Poly.Polygraph.Invertibility

open FX1Poly.Core
open FX1Poly.Core.StepStar

/-- The **reduct witness operator** on raw terms: a family is applied to a term exactly when it already
holds of every one-step reduct.  Since `StepSuccessor reduct term := Step term reduct`, `apply family
term` is "all one-step reducts of `term` are in `family`" — the operator whose least fixpoint is strong
normalization and whose post-fixed families are the step-closed sets. -/
def reductWitnessOperator {scope : Nat} : WitnessOperator (RawTerm scope) where
  apply := fun family term => ∀ reduct, StepSuccessor reduct term → family reduct
  monotone := fun containment _term reductsInSmaller reduct step =>
    containment reduct (reductsInSmaller reduct step)

/-- **F1 forward.**  A member of the inductive closure of the reduct operator is strongly normalizing.
`IsStronglyNormalizing` is `apply`-closed — that closure step is exactly `Acc.intro` — so it contains the
least fixpoint. -/
theorem isStronglyNormalizing_of_inductiveClosure {scope : Nat} {term : RawTerm scope}
    (member : inductiveClosure reductWitnessOperator term) :
    IsStronglyNormalizing term := by
  refine member IsStronglyNormalizing ?_
  intro point reductsStronglyNormalizing
  exact Acc.intro point reductsStronglyNormalizing

/-- **F1 backward.**  A strongly normalizing term is a member of the inductive closure of the reduct
operator.  By `Acc`-recursion: the induction hypothesis gives closure-membership of every reduct, which
is exactly the `apply`-premise, so `inductiveClosure_closedUnderApply` rolls it up. -/
theorem inductiveClosure_of_isStronglyNormalizing {scope : Nat} {term : RawTerm scope}
    (terminates : IsStronglyNormalizing term) :
    inductiveClosure reductWitnessOperator term := by
  induction terminates with
  | intro current _accessiblePredecessors inductiveHypothesis =>
      exact inductiveClosure_closedUnderApply reductWitnessOperator
        (fun reduct step => inductiveHypothesis reduct step)

/-- ★ **F1: strong normalization IS the inductive fixpoint.**  The impredicative least fixpoint of the
reduct witness operator coincides with the kernel's `Acc`-based strong normalization.  This is the
`Acc = least-fixpoint` coincidence at the heart of the HL23 ↔ Tait bridge. -/
theorem inductiveClosure_reductWitnessOperator_iff_isStronglyNormalizing
    {scope : Nat} {term : RawTerm scope} :
    inductiveClosure reductWitnessOperator term ↔ IsStronglyNormalizing term :=
  ⟨isStronglyNormalizing_of_inductiveClosure, inductiveClosure_of_isStronglyNormalizing⟩

/-- **CR2 is post-fixedness.**  A Girard reducibility candidate's forward step-closure (CR2) says exactly
that the candidate predicate is a post-fixed family of the reduct operator: `predicate ⊆ apply
predicate`.  This identifies the CR abstraction with the coinductive (invertibility-set) side. -/
theorem reducibilityCandidate_isPostFixed_reductWitnessOperator
    {scope : Nat} {predicate : RawTerm scope → Prop}
    (candidate : IsReducibilityCandidate predicate) :
    IsPostFixed reductWitnessOperator predicate :=
  fun _term member _reduct step => candidate.closedUnderStep member step

/-- ★ **Reducibility candidates ⊆ the coinductive fixpoint.**  Every member of a Girard reducibility
candidate lies in `coinductiveClosure reductWitnessOperator` — the greatest fixpoint / maximal
step-closed family.  Combined with F1 (least fixpoint = SN), the two Tait/Girard structures occupy the
two extremal fixpoints of the single reduct witness operator. -/
theorem reducibilityCandidate_subset_coinductiveClosure
    {scope : Nat} {predicate : RawTerm scope → Prop}
    (candidate : IsReducibilityCandidate predicate) {term : RawTerm scope}
    (member : predicate term) :
    coinductiveClosure reductWitnessOperator term :=
  (reducibilityCandidate_isPostFixed_reductWitnessOperator candidate).subset_coinductiveClosure member

end FX1Poly.Polygraph.Invertibility
