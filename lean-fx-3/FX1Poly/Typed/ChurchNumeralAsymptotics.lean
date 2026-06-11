import FX1Poly.Typed.TypedChurchNumeralAddition
import FX1Poly.Core.StepStarLength

/-! # FX1Poly/Typed/ChurchNumeralAsymptotics
    — ★ verified Church-numeral asymptotics: arithmetic DISPATCH is constant-time (COST-8)

The counted-chain (`StepStarN`) upgrade of the Church-numeral
computation corpus — the step counts are now THEOREMS:

  * `StepStarN.congAt` — the counted one-hole congruence lifter: a
    counted chain in a hole position lifts to a counted chain of the
    SAME length (the counted twin of `StepStar.congAt`).
  * ★ `churchNumeral_dispatchCounted` — the numeral DISPATCH costs
    EXACTLY 3 steps, INDEPENDENT of the numeral: for every depth `n`
    and any closed `A`, `f`, `x`,
    `(churchNumeral n) A f x  ↝³  f^n x` — the three β-redexes (type,
    step, base) are all the dispatch ever fires, because the iterate is
    produced BY SUBSTITUTION, not by unfolding.
  * ★ `churchAddition_dispatchCounted` — Church ADDITION dispatches in
    EXACTLY 6 steps for ALL `m`, `n`:
    `m A f (n A f x)  ↝⁶  f^(m+n) x` — the inner dispatch (3, lifted
    through the argument position at the same length) plus the outer
    dispatch (3); the index arithmetic is the shipped
    `iteratedApplication_add` EQUALITY, costing zero steps.
  * ★ `churchArithmetic_dispatchIsConstantTime` — the bundle headline:
    FX's term model performs Church-numeral arithmetic dispatch in
    VERIFIED CONSTANT time — the step counts (3 and 6) do not mention
    the operands.

## Honest scope boundary

These are ITERATE-level costs: the constant counts measure reaching the
result iterate `f^(m+n) x`, i.e. the cost of the ARITHMETIC itself.
Evaluating the iterate against a CONCRETE step function costs further
steps growing with the count — that is the cost of USING the result,
not of computing it.  Multiplication's dispatch is recursive
(linear in the left operand) and its counted closed form is the
remaining COST-8 brick.

Zero-axiom; gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

/-- **The counted one-hole congruence lifter**: a counted chain in a
hole position lifts to a counted chain of the SAME length (each step
wraps in the supplied congruence; the count is untouched). -/
theorem StepStarN.congAt {scope : Nat} {chainLength : Nat}
    {subjectStart subjectEnd : RawTerm scope}
    (oneHoleContext : RawTerm scope → RawTerm scope)
    (liftStepThroughHole : ∀ {filledStart filledEnd : RawTerm scope},
      Step filledStart filledEnd →
      Step (oneHoleContext filledStart) (oneHoleContext filledEnd))
    (innerChain : StepStarN chainLength subjectStart subjectEnd) :
    StepStarN chainLength (oneHoleContext subjectStart) (oneHoleContext subjectEnd) := by
  induction innerChain with
  | reflN visitedTerm => exact StepStarN.reflN _
  | transN headStep _restChain liftedRest =>
      exact StepStarN.transN (liftStepThroughHole headStep) liftedRest

/-- ★ **The Church-numeral dispatch costs EXACTLY 3 steps, independent
of the numeral**: the type-, step-, and base-β are all the dispatch ever
fires — the iterate `f^n x` is produced BY SUBSTITUTION.  The counted
twin of `churchNumeral_appliedReducesToIterate_general` (#1009), with
the same three reshaped β-contractums. -/
theorem churchNumeral_dispatchCounted (depth : Nat) (typeA handlerF baseX : RawTerm 0) :
    StepStarN 3
      (appCell (appCell (appCell (churchNumeralLambda depth) typeA) handlerF) baseX)
      (iteratedApplication depth handlerF baseX) := by
  have step1 : Step (appCell (churchNumeralLambda depth) typeA)
      (lamCell (piTyCodeCell typeA (RawTerm.weaken typeA))
        (lamCell (RawTerm.weaken typeA)
          (iteratedApplication depth
            (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
            (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2))))) := by
    rw [← churchNumeral_substType depth typeA]; exact Step.beta
  have step2 : Step
      (appCell (lamCell (piTyCodeCell typeA (RawTerm.weaken typeA))
        (lamCell (RawTerm.weaken typeA)
          (iteratedApplication depth
            (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
            (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2))))) handlerF)
      (lamCell typeA
        (iteratedApplication depth (RawTerm.weaken handlerF)
          (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))) := by
    rw [← churchNumeral_substStep depth typeA handlerF]; exact Step.beta
  have step3 : Step
      (appCell (lamCell typeA
        (iteratedApplication depth (RawTerm.weaken handlerF)
          (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))) baseX)
      (iteratedApplication depth handlerF baseX) := by
    rw [← iteratedApplication_subst0_weaken_step depth handlerF baseX]; exact Step.beta
  exact StepStarN.transN
    (Step.cong .gen_app ()
      (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
        (.childCons baseX .childNil)
        (Step.cong .gen_app ()
          (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
            (.childCons handlerF .childNil) step1))))
    (StepStarN.transN
      (Step.cong .gen_app ()
        (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
          (.childCons baseX .childNil) step2))
      (StepStarN.transN step3
        (StepStarN.reflN (iteratedApplication depth handlerF baseX))))

/-- ★ **Church ADDITION dispatches in EXACTLY 6 steps for ALL operands**:
the inner numeral's 3-step dispatch lifts through the argument position
at the SAME length, the outer numeral's 3-step dispatch follows, and the
index arithmetic (`f^m (f^n x) = f^(m+n) x`) is an EQUALITY costing zero
steps.  The verified statement that the COST of Church addition does not
depend on the numbers being added. -/
theorem churchAddition_dispatchCounted (countLeft countRight : Nat)
    (typeA handlerF baseX : RawTerm 0) :
    StepStarN 6
      (appCell (appCell (appCell (churchNumeralLambda countLeft) typeA) handlerF)
        (appCell (appCell (appCell (churchNumeralLambda countRight) typeA) handlerF) baseX))
      (iteratedApplication (countLeft + countRight) handlerF baseX) := by
  have liftedInner : StepStarN 3
      (appCell (appCell (appCell (churchNumeralLambda countLeft) typeA) handlerF)
        (appCell (appCell (appCell (churchNumeralLambda countRight) typeA) handlerF) baseX))
      (appCell (appCell (appCell (churchNumeralLambda countLeft) typeA) handlerF)
        (iteratedApplication countRight handlerF baseX)) :=
    StepStarN.congAt
      (fun hole => appCell
        (appCell (appCell (churchNumeralLambda countLeft) typeA) handlerF) hole)
      (fun argStep => Step.appArgCong _ argStep)
      (churchNumeral_dispatchCounted countRight typeA handlerF baseX)
  have outerCounted : StepStarN 3
      (appCell (appCell (appCell (churchNumeralLambda countLeft) typeA) handlerF)
        (iteratedApplication countRight handlerF baseX))
      (iteratedApplication countLeft handlerF
        (iteratedApplication countRight handlerF baseX)) :=
    churchNumeral_dispatchCounted countLeft typeA handlerF
      (iteratedApplication countRight handlerF baseX)
  have composed := StepStarN.trans_compose liftedInner outerCounted
  rw [(iteratedApplication_add countLeft countRight handlerF baseX).symm] at composed
  exact composed

/-- ★ **Church-numeral arithmetic dispatch is VERIFIED CONSTANT time**:
the numeral dispatch costs exactly 3 steps and addition exactly 6 — the
counts do not mention the operands.  The cost of the ARITHMETIC is
constant; only USING the resulting iterate against a concrete step
function costs steps growing with the count. -/
theorem churchArithmetic_dispatchIsConstantTime :
    (∀ (depth : Nat) (typeA handlerF baseX : RawTerm 0),
        StepStarN 3
          (appCell (appCell (appCell (churchNumeralLambda depth) typeA) handlerF) baseX)
          (iteratedApplication depth handlerF baseX))
      ∧ (∀ (countLeft countRight : Nat) (typeA handlerF baseX : RawTerm 0),
          StepStarN 6
            (appCell (appCell (appCell (churchNumeralLambda countLeft) typeA) handlerF)
              (appCell (appCell (appCell (churchNumeralLambda countRight) typeA)
                handlerF) baseX))
            (iteratedApplication (countLeft + countRight) handlerF baseX)) :=
  ⟨churchNumeral_dispatchCounted, churchAddition_dispatchCounted⟩

end FX1Poly.Typed
