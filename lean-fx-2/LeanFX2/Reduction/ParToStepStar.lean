import LeanFX2.Reduction.StepStarCongLifters
import LeanFX2.Reduction.ParRed.ParInductive.Inductive

/-! # Reduction/ParToStepStar — parallel reduction into the single-step
RT closure.

The easy inclusion `StepStar ⊆ Step.parStar` is `StepStar.toParStar`
(Reduction/StepStarToPar).  This file works the HARD reverse — every
`Step.par` is contained in the single-step reflexive-transitive
closure `StepStar` — which, composed across a `Step.parStar` chain,
closes `StepStar = Step.parStar` and unblocks the literal Conv = par
characterization (#2029).

## Why the full headline is blocked at open types

A single-step `Step` congruence constructor (`Step.optionSomeValue`,
`Step.modIntroInner`, ...) requires its inner source and target at the
SAME type.  Inside a `StepStar` chain the intermediate types can drift,
so lifting the chain through a constructor needs subject reduction to
pin it at its starting type.  General subject reduction
(`Step.preserves_isClosedTy`) holds only at closed types
(`IsClosedTy`, Foundation/IsClosedTy).  Every `Step.par` congruence /
β / ι arm carries a fully arbitrary component type (e.g.
`Step.par.optionSome` has `{elementType : Ty level scope}` with no
closedness constraint), so the cong-lifters in
`Reduction/StepStarCongLifters` require an `IsClosedTy` witness that
the arbitrary arm cannot supply.  This is the same wall that blocks
the `unblock-A.dispatch.*` family documented in
`Foundation/IsClosedTy.lean`: closing the open-type cong arms needs an
`IsClosedRawTerm`-style companion predicate (var-0-freeness of raw
payloads) that does not yet ship.

## What ships here (total, zero-hypothesis)

The four univalence / funext rfl-fragment leaf families close
unconditionally: their `Step.par` source has no inner parallel-step
premise (it is a leaf-canonical value), so each maps to a single
`Step` via `StepStar.fromStep`.  These are the typed mirrors of the
same arms in `Step.toPar`.

The closed-type cong arms compose via
`Reduction/StepStarCongLifters`; they are exposed there as reusable
`StepStar.<ctor>_lift` lemmas rather than re-stated here. -/

namespace LeanFX2

/-! ## Univalence / funext rfl-fragment leaves

Each of these `Step.par` arms reduces a leaf-canonical value to its
canonical rfl form in exactly one step; the matching single-step
`Step` constructor produces the same source/target, so
`StepStar.fromStep` is the whole proof. -/

/-- The canonical universe-level identity-equivalence parallel-reduces
to the canonical identity-equivalence — contained in the single-step
RT closure via `Step.eqType`. -/
theorem Step.par.eqType_toStepStar
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (carrier : Ty level scope)
    (carrierRaw : RawTerm scope) :
    StepStar
      (Term.equivReflIdAtId (context := context)
                            innerLevel innerLevelLt carrier carrierRaw)
      (Term.equivReflId (context := context) carrier) :=
  StepStar.fromStep (Step.eqType innerLevel innerLevelLt carrier carrierRaw)

/-- The canonical Id-typed funext witness at arrow types
parallel-reduces to the canonical pointwise-refl funext witness —
contained in the single-step RT closure via `Step.eqArrow`. -/
theorem Step.par.eqArrow_toStepStar
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    (applyRaw : RawTerm (scope + 1)) :
    StepStar
      (Term.funextReflAtId (context := context)
                           domainType codomainType applyRaw)
      (Term.funextRefl (context := context)
                       domainType codomainType applyRaw) :=
  StepStar.fromStep (Step.eqArrow domainType codomainType applyRaw)

/-- The heterogeneous univalence witness parallel-reduces to its
underlying equivalence witness — contained in the single-step RT
closure via `Step.eqTypeHet`. -/
theorem Step.par.eqTypeHet_toStepStar
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    {carrierA carrierB : Ty level scope}
    (carrierARaw carrierBRaw : RawTerm scope)
    {forwardRaw backwardRaw : RawTerm scope}
    (equivWitness :
      Term context (Ty.equiv carrierA carrierB)
        (RawTerm.equivIntro forwardRaw backwardRaw)) :
    StepStar
      (Term.uaIntroHet innerLevel innerLevelLt carrierARaw carrierBRaw equivWitness)
      equivWitness :=
  StepStar.fromStep
    (Step.eqTypeHet innerLevel innerLevelLt carrierARaw carrierBRaw equivWitness)

/-- The heterogeneous funext witness parallel-reduces to the canonical
pointwise-refl funext witness at the left apply payload — contained in
the single-step RT closure via `Step.eqArrowHet`. -/
theorem Step.par.eqArrowHet_toStepStar
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    (applyARaw applyBRaw : RawTerm (scope + 1)) :
    StepStar
      (Term.funextIntroHet (context := context)
                           domainType codomainType applyARaw applyBRaw)
      (Term.funextRefl (context := context)
                       domainType codomainType applyARaw) :=
  StepStar.fromStep
    (Step.eqArrowHet domainType codomainType applyARaw applyBRaw)

end LeanFX2
