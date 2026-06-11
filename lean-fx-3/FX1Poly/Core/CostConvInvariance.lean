import FX1Poly.Core.CostBound

/-! # FX1Poly/Core/CostConvInvariance
    — ★ the Conv-invariance NO-GO: cost is NOT a property of Conv classes (COST-4 brick 1)

The design-pinning refutation for cost-aware equivalence: definitional
equality (`Conv`) does NOT respect evaluation cost — a β-redex and its
reduct are convertible yet cost differently.  Any "cost-aware
equivalence" must therefore be STRICTLY FINER than `Conv`; it cannot be
recovered from the Conv class.  This is the mechanized form of the
calf/decalf observation that cost is an INTENSIONAL property destroyed
by extensional quotienting.

  * `StepStarN.eq_of_zero` — a counted chain of length zero is
    reflexivity (the inversion the characterization needs).
  * ★ `RawTerm.normalizeCost_eq_zero_iff_isStepNormalForm` — the
    canonical cost is zero EXACTLY on normal forms (both directions;
    the forward direction reads the exactness chain, the backward
    direction transports normality along the zero-length chain).
  * ★ `costIsNotConvInvariant` — THE NO-GO: two convertible closed
    terms (the identity-β redex and `unit`) with provably DIFFERENT
    canonical costs.  No computation through the accessibility
    witnesses is needed: `unit` costs zero by kernel evaluation, and
    the redex's cost is nonzero because zero cost would make it a
    normal form, contradicting its β-step.

Zero-axiom; gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Core

open Foundation

/-- A counted chain of length zero is reflexivity. -/
theorem StepStarN.eq_of_zero {scope : Nat} {firstTerm thirdTerm : RawTerm scope}
    (countedChain : StepStarN 0 firstTerm thirdTerm) : firstTerm = thirdTerm := by
  cases countedChain with
  | reflN _ => rfl

/-- Any counted chain FROM a normal form has length zero (the first step
of a nonzero chain contradicts normality).  All indices are variables,
so the case analysis is total and propext-clean. -/
theorem StepStarN.eq_zero_of_isStepNormalForm {scope : Nat} {chainLength : Nat}
    {firstTerm thirdTerm : RawTerm scope}
    (countedChain : StepStarN chainLength firstTerm thirdTerm)
    (firstNormal : RawTerm.isStepNormalForm firstTerm) :
    chainLength = 0 := by
  cases countedChain with
  | reflN _ => rfl
  | transN firstStep _restChain =>
      exact absurd firstStep
        (RawTerm.isStepNormalForm_blocks_step firstNormal _)

/-- A normal form has zero canonical cost (its exactness chain has
length zero). -/
theorem RawTerm.normalizeCost_eq_zero_of_isStepNormalForm {scope : Nat}
    {term : RawTerm scope} (accessible : Acc (@StepStar.StepSuccessor scope) term)
    (termNormal : RawTerm.isStepNormalForm term) :
    RawTerm.normalizeCost term accessible = 0 :=
  StepStarN.eq_zero_of_isStepNormalForm
    (RawTerm.normalizeCost_isExact term accessible) termNormal

/-- Zero canonical cost forces a normal form (the zero-length exactness
chain identifies the term with its computed normal form). -/
theorem RawTerm.isStepNormalForm_of_normalizeCost_eq_zero {scope : Nat}
    {term : RawTerm scope} (accessible : Acc (@StepStar.StepSuccessor scope) term)
    (zeroCost : RawTerm.normalizeCost term accessible = 0) :
    RawTerm.isStepNormalForm term := by
  have exactChain := RawTerm.normalizeCost_isExact term accessible
  rw [zeroCost] at exactChain
  rw [StepStarN.eq_of_zero exactChain]
  exact RawTerm.normalize_isStepNormalForm term accessible

/-- ★ **The zero-cost characterization**: the canonical evaluation cost
is zero exactly on normal forms. -/
theorem RawTerm.normalizeCost_eq_zero_iff_isStepNormalForm {scope : Nat}
    {term : RawTerm scope} (accessible : Acc (@StepStar.StepSuccessor scope) term) :
    RawTerm.normalizeCost term accessible = 0 ↔ RawTerm.isStepNormalForm term :=
  ⟨RawTerm.isStepNormalForm_of_normalizeCost_eq_zero accessible,
   RawTerm.normalizeCost_eq_zero_of_isStepNormalForm accessible⟩

/-- The identity-β fixture's cost is NONZERO — zero cost would make the
redex a normal form, contradicting its β-step.  No kernel evaluation
through the accessibility witness. -/
theorem identityBetaFixture_normalizeCost_ne_zero :
    RawTerm.normalizeCost identityBetaFixture identityBetaFixture_accessible ≠ 0 :=
  fun zeroCost =>
    absurd identityBetaFixture_stepsToUnit
      (RawTerm.isStepNormalForm_blocks_step
        (RawTerm.isStepNormalForm_of_normalizeCost_eq_zero
          identityBetaFixture_accessible zeroCost) _)

/-- ★ **THE NO-GO: cost is not Conv-invariant.**  Two convertible closed
kernel terms — the identity-β redex and its reduct `unit` — have
provably DIFFERENT canonical evaluation costs.  Cost-aware equivalence
is therefore strictly finer than definitional equality: it cannot be a
property of the Conv class. -/
theorem costIsNotConvInvariant :
    ∃ (left right : RawTerm 0)
      (leftAccessible : Acc (@StepStar.StepSuccessor 0) left)
      (rightAccessible : Acc (@StepStar.StepSuccessor 0) right),
      Conv left right
        ∧ RawTerm.normalizeCost left leftAccessible
            ≠ RawTerm.normalizeCost right rightAccessible :=
  ⟨identityBetaFixture, unitNormalFormFixture,
   identityBetaFixture_accessible, unitNormalFormFixture_accessible,
   ⟨unitNormalFormFixture,
     StepStar.trans identityBetaFixture_stepsToUnit
       (StepStar.refl unitNormalFormFixture),
     StepStar.refl unitNormalFormFixture⟩,
   fun costEq =>
     identityBetaFixture_normalizeCost_ne_zero
       (costEq.trans RawTerm.normalizeCost_unit_isZero)⟩

end FX1Poly.Core
