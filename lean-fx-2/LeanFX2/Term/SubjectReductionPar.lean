import LeanFX2.Term.SubjectReductionGeneral
import LeanFX2.Reduction.ParStar

/-! # SubjectReductionPar — TODO POLYCELL: BODY DISABLED

Body depends on Step.parStar / RawStep.par.rename_inj_inv (from wrapped
Reduction/ParStar.lean and RawParWeakenInv/HeadlineRenameInjInv.lean).
Replacement: FXcdLemma / FXConv view defs per polycell.md §5.
-/

/- TODO POLYCELL: original body preserved as block comment


/-! # Term/SubjectReductionPar — parallel-step subject reduction for closed types

Mirrors `Step.preserves_isClosedTy` (`Term/SubjectReductionGeneral.lean`)
at the `Step.par` parallel-reduction relation.  Says: if the source of
a `Step.par` step has a closed type, the target has the same closed
type.

## Why this exists

The single-step SR theorem `Step.preserves_isClosedTy` covers the
sequential reduction relation.  Many kernel constructions — including
`CONVTRANS-C`'s universal chain lift dispatcher `RawStep.par.lift_full_term`
and the upcoming Phase A1 follow-up of `DispatchAtom` with closed-typed
sub-terms — need the parallel-step counterpart.  Both relations preserve
closed types for the same structural reason: every typed constructor
producing a closed source type either has a closed target by ctor
shape, or the closed-typed equation propagates through the same
substitution invariance lemma.

## Root status

Zero-axiom.  Single induction over `Step.par`'s 129 ctors discharged
by the same `all_goals first | ...` tactic combo used by
`Step.preserves_isClosedTy`. -/

namespace LeanFX2

variable {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}

/-- Closed-type subject reduction at `Step.par`: every parallel step
from a source typed at a closed type produces a target with the same
closed type.

Parallel of `Step.preserves_isClosedTy`.  Same tactic recipe: induct
on the parallel step, then in each ctor case discharge via one of:

* `exact sourceIsClosed` — the case has no type change.
* `subst sourceIsClosed; rfl` — the case is reflexive after subst.
* `rfl` — definitional collapse after the ctor's typing rule.
* `subst0_raw_invariance_isClosedTy` — substitution-driven cases.
* `Ty.weaken_subst_singleton` — singleton-binder cases.
* `cases sourceClosed` — type-changing reductions that contradict
  the closed-type witness (`Step.par` analogues of `eqType` /
  `eqArrow` if any). -/
theorem Step.par.preserves_isClosedTy
    {sourceType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetType : Ty level scope}
    {targetTerm : Term context targetType targetRaw}
    {closedType : Ty level scope}
    (sourceClosed : IsClosedTy closedType)
    (parallelStep : Step.par sourceTerm targetTerm)
    (sourceIsClosed : sourceType = closedType) :
    targetType = closedType := by
  induction parallelStep
  all_goals
    first
      | exact sourceIsClosed
      | (subst sourceIsClosed; rfl)
      | rfl
      | exact Ty.subst0_raw_invariance_isClosedTy _ _ _ _
                sourceClosed sourceIsClosed
      | (subst sourceIsClosed; exact Ty.weaken_subst_singleton _ _ _)
      | (subst sourceIsClosed; cases sourceClosed)

/-- Closed-type subject reduction at `Step.parStar`: every parallel
chain from a closed-typed source produces a target with the same
closed type.  Trivial chain induction. -/
theorem Step.parStar.preserves_isClosedTy
    {sourceType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetType : Ty level scope}
    {targetTerm : Term context targetType targetRaw}
    {closedType : Ty level scope}
    (sourceClosed : IsClosedTy closedType)
    (chain : Step.parStar sourceTerm targetTerm)
    (sourceIsClosed : sourceType = closedType) :
    targetType = closedType := by
  induction chain with
  | refl _ => exact sourceIsClosed
  | trans head _ tailIH =>
      exact tailIH (Step.par.preserves_isClosedTy sourceClosed head sourceIsClosed)

end LeanFX2

-/
