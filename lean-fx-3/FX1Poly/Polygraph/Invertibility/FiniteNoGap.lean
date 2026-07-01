import FX1Poly.Polygraph.Invertibility.StrongNormalizationBridge

/-! # FX1Poly/Polygraph/Invertibility/FiniteNoGap
    — HL23 Cor 4.35: a well-founded guard collapses the coinductive fixpoint onto the inductive one.

Henry–Loubaton Cor 4.35 (the "no coinductive gap" corollary): under a well-foundedness/finiteness
hypothesis the greatest invertibility fixpoint coincides with the least one — there is no gap between the
coinductively-invertible and the inductively-invertible cells.  Here is the abstract, operator-level
version: if the operator is GUARDED by a relation whose members are all accessible, then every
coinductive-closure member is already an inductive-closure member, and (with the generic least ⊆ greatest
inclusion) the two fixpoints AGREE.

## What "guarded" means

`applyFromGuard` says: if every `guard`-predecessor of an element lies in a family, then the operator
already applies the family to that element.  For the reduct operator this holds tautologically with
`guard := StepSuccessor` (`apply` IS the guard-quantification), so `inductiveClosure_of_acc` recovers
"`Acc StepSuccessor` ⟹ SN" and the collapse specializes to FX.

## Honesty: the FX global discharge is a genuine non-theorem, left conditional

Discharging the hypothesis GLOBALLY for FX would require `WellFounded StepSuccessor` — raw β+ι strong
normalization — which is FALSE at the raw layer (`gen_natRec` / `gen_fixedPoint` admit infinite
reductions).  So `coinductiveClosure_reductWitnessOperator_collapses_of_wellFounded` is stated as a
machine-checked CONDITIONAL on that (globally-unavailable) premise; it fires only on a fragment where SN
already holds.  No global no-gap collapse is claimed.

## Zero-axiom verification

`Acc`-recursion (`inductiveClosure_of_acc`), `WellFounded.apply`, and the generic `WitnessClosure`
lemmas.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/Polygraph/Invertibility/FiniteNoGap.lean`.
-/

namespace FX1Poly.Polygraph.Invertibility

open FX1Poly.Core
open FX1Poly.Core.StepStar

/-- **The real content of Cor 4.35.**  If `operator` is guarded by `guard` (all `guard`-predecessors in a
family ⟹ the operator applies that family) and `element` is `guard`-accessible, then `element` is in the
inductive closure.  By well-founded recursion on the accessibility: the induction hypothesis supplies
closure-membership of every predecessor, `applyFromGuard` turns that into the `apply`-premise, and
`inductiveClosure_closedUnderApply` closes. -/
theorem inductiveClosure_of_acc {Carrier : Type} (operator : WitnessOperator Carrier)
    (guard : Carrier → Carrier → Prop)
    (applyFromGuard : ∀ (family : Carrier → Prop) (element : Carrier),
      (∀ predecessor, guard predecessor element → family predecessor) →
        operator.apply family element)
    {element : Carrier} (accessible : Acc guard element) :
    inductiveClosure operator element := by
  induction accessible with
  | intro current _guardStep inductiveHypothesis =>
      exact inductiveClosure_closedUnderApply operator
        (applyFromGuard (inductiveClosure operator) current inductiveHypothesis)

/-- **HL23 Cor 4.35 (abstract).**  If a guarded operator's guard is well-founded, the coinductive closure
is contained in the inductive one.  (Under well-foundedness the inductive side is total, so the
coinductive premise carries no extra information — this IS the "no coinductive gap" phenomenon; the
coinductive membership is accepted and discarded.) -/
theorem coinductiveClosure_subset_inductiveClosure_of_wellFounded {Carrier : Type}
    (operator : WitnessOperator Carrier) (guard : Carrier → Carrier → Prop)
    (applyFromGuard : ∀ (family : Carrier → Prop) (element : Carrier),
      (∀ predecessor, guard predecessor element → family predecessor) →
        operator.apply family element)
    (guardWellFounded : WellFounded guard) {element : Carrier}
    (_member : coinductiveClosure operator element) :
    inductiveClosure operator element :=
  inductiveClosure_of_acc operator guard applyFromGuard (guardWellFounded.apply element)

/-- ★ **No gap: the two fixpoints agree** under a well-founded guard.  Greatest = least when the operator
is well-founded — the crisp statement of "no coinductive gap" (`←` is the generic least ⊆ greatest, `→`
is Cor 4.35). -/
theorem fixpoints_agree_of_wellFounded {Carrier : Type}
    (operator : WitnessOperator Carrier) (guard : Carrier → Carrier → Prop)
    (applyFromGuard : ∀ (family : Carrier → Prop) (element : Carrier),
      (∀ predecessor, guard predecessor element → family predecessor) →
        operator.apply family element)
    (guardWellFounded : WellFounded guard) (element : Carrier) :
    coinductiveClosure operator element ↔ inductiveClosure operator element :=
  ⟨coinductiveClosure_subset_inductiveClosure_of_wellFounded operator guard applyFromGuard
      guardWellFounded,
   inductiveClosure_subset_coinductiveClosure operator⟩

/-- The reduct operator is guarded by `StepSuccessor` tautologically: `apply family term` IS "every
`StepSuccessor`-predecessor of `term` is in `family`".  This is the bridge that lets the abstract Cor
4.35 fire at FX's reduction. -/
theorem reductWitnessOperator_applyFromGuard {scope : Nat} :
    ∀ (family : RawTerm scope → Prop) (term : RawTerm scope),
      (∀ reduct, StepSuccessor reduct term → family reduct) →
        reductWitnessOperator.apply family term :=
  fun _family _term reductsInFamily => reductsInFamily

/-- **HL23 Cor 4.35 at the FX reduct operator (CONDITIONAL — see file docstring).**  IF the raw one-step
reduction is well-founded at `scope` (every raw term strongly normalizes) THEN the coinductive
invertibility fixpoint collapses onto strong normalization.

The premise `WellFounded StepSuccessor` is raw β+ι strong normalization, which is FALSE at the raw layer
(`gen_natRec` / `gen_fixedPoint` diverge), so this conditional has NO global discharge; it is stated
machine-checked-but-hypothetical to keep the claim honest rather than overclaim a global collapse.  On a
fragment where SN holds it reduces to the F1 bridge. -/
theorem coinductiveClosure_reductWitnessOperator_collapses_of_wellFounded {scope : Nat}
    (rawWellFounded : WellFounded (StepSuccessor (scope := scope)))
    {term : RawTerm scope} (member : coinductiveClosure reductWitnessOperator term) :
    IsStronglyNormalizing term :=
  isStronglyNormalizing_of_inductiveClosure
    (coinductiveClosure_subset_inductiveClosure_of_wellFounded reductWitnessOperator
      StepSuccessor reductWitnessOperator_applyFromGuard rawWellFounded member)

end FX1Poly.Polygraph.Invertibility
