import LeanFX2.Reducibility.StableBase

/-! # LeanFX2.Reducibility.NeutralSNFoundation.PiSigma

Variables vacuous SN + Π/Σ neutral-head preservation.  Covers
`var_isStronglyNormalizing`, `var_has_no_progress`, and the `app` /
`fst` / `snd` neutral & var-shape variants.

## Root status

Layer 3 metatheory leaf.  First slice of NeutralSNFoundation. -/

namespace LeanFX2

/-! ## K12.20.C neutral & natSucc SN preservation

Two more raw-level SN lemmas continuing the K12.19.B/K12.20.A
pattern:

* `RawTerm.var_isStronglyNormalizing` — every variable is SN.
  Variables have no β/ι rules (no destructor fires on a variable
  head); the only `RawStep.par` from `RawTerm.var position` is
  `refl` (per `var_inv` in `RawParInversion`), so the parProgress
  disequality contradiction discharges the SN closure.  Foundational
  for CR3: variables are neutral terms with no progress steps, so
  CR3's premise is vacuously satisfied → variables are reducible at
  every SN-direct Ty arm.

* `RawTerm.natSucc_isStronglyNormalizing` — `natSucc predecessor`
  is SN whenever the predecessor is.  Same single-subterm structural
  induction as `lam_isStronglyNormalizing`: `natSucc_inv` step
  inversion + `RawTerm.natSucc` ctor-injectivity.
-/

/-- Variables are strongly normalizing.  No `RawStep.par` ctor has
a variable as source other than `refl`, so any `parProgress` step
contradicts. -/
theorem RawTerm.var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope) :
    RawTerm.isStronglyNormalizing (RawTerm.var position) :=
  RawTerm.isStronglyNormalizing.intro (RawTerm.var position)
    (fun _ progressStep =>
      (progressStep.2 (RawStep.par.var_inv progressStep.1).symm).elim)

/-- Variables have no non-trivial parallel-progress reducts.  This is
the vacuous CR3 base fact for `RawTerm.IsNeutral.var`: once the CR3
proof recurses over types, the premise `∀ target, var → target →
Reducible target` is never queried for an actual target. -/
theorem RawTerm.var_has_no_progress {scope : Nat}
    (position : Fin scope) :
    ∀ target : RawTerm scope,
      ¬ RawStep.parProgress (RawTerm.var position) target := by
  intro target progressStep
  exact progressStep.2 (RawStep.par.var_inv progressStep.1).symm

/-- Application with a neutral function head is strongly normalizing
when both the head and argument are strongly normalizing.

The beta arm is impossible because `RawTerm.IsNeutral.par_preserves`
keeps every parallel reduct of the function head neutral, and neutral
terms are never lambda-shaped.  The congruence arm recurses on the
function progress when the head changes, otherwise on the argument
progress. -/
theorem RawTerm.app_neutral_isStronglyNormalizing {scope : Nat}
    {functionRaw argumentRaw : RawTerm scope}
    (functionIsNeutral : RawTerm.IsNeutral functionRaw)
    (functionIsSN : RawTerm.isStronglyNormalizing functionRaw)
    (argumentIsSN : RawTerm.isStronglyNormalizing argumentRaw) :
    RawTerm.isStronglyNormalizing
      (RawTerm.app functionRaw argumentRaw) := by
  induction functionIsSN generalizing argumentRaw with
  | intro currentFunction _ functionInduction =>
    induction argumentIsSN with
    | intro currentArgument argumentClosure argumentInduction =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.app currentFunction currentArgument) ?_
      intro target progressStep
      rcases RawStep.par.app_inv progressStep.1 with
        ⟨functionTarget, argumentTarget, targetEq,
          functionStep, argumentStep⟩
        | ⟨bodyTarget, _argumentTarget, _targetEq,
            functionStep, _argumentStep⟩
      · subst targetEq
        have functionTargetIsNeutral :
            RawTerm.IsNeutral functionTarget :=
          RawTerm.IsNeutral.par_preserves functionIsNeutral functionStep
        have argumentTargetIsSN :
            RawTerm.isStronglyNormalizing argumentTarget := by
          by_cases argumentEq : currentArgument = argumentTarget
          · subst argumentEq
            exact RawTerm.isStronglyNormalizing.intro
              currentArgument argumentClosure
          · exact argumentClosure argumentTarget
              ⟨argumentStep, argumentEq⟩
        by_cases functionEq : currentFunction = functionTarget
        · subst functionEq
          by_cases argumentEq : currentArgument = argumentTarget
          · subst argumentEq
            exact (progressStep.2 rfl).elim
          · exact argumentInduction argumentTarget
              ⟨argumentStep, argumentEq⟩
        · exact functionInduction functionTarget
            ⟨functionStep, functionEq⟩
            functionTargetIsNeutral
            argumentTargetIsSN
      · exact (RawTerm.IsNeutral.not_lam
          (RawTerm.IsNeutral.par_preserves functionIsNeutral functionStep)
          (bodyRaw := bodyTarget) rfl).elim

/-- First projection with a neutral pair head is strongly normalizing
when the head is strongly normalizing.

The pair beta arm is impossible because any parallel reduct of a
neutral head stays neutral, and neutral terms are never pair-shaped.
The congruence arm recurses on head progress. -/
theorem RawTerm.fst_neutral_isStronglyNormalizing {scope : Nat}
    {pairRaw : RawTerm scope}
    (pairIsNeutral : RawTerm.IsNeutral pairRaw)
    (pairIsSN : RawTerm.isStronglyNormalizing pairRaw) :
    RawTerm.isStronglyNormalizing (RawTerm.fst pairRaw) := by
  induction pairIsSN with
  | intro currentPair _ pairInduction =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.fst currentPair) ?_
    intro target progressStep
    rcases RawStep.par.fst_inv progressStep.1 with
      ⟨pairTarget, targetEq, pairStep⟩
      | ⟨firstTarget, secondTarget, _targetEq, pairStep⟩
    · have pairTargetIsNeutral : RawTerm.IsNeutral pairTarget :=
        RawTerm.IsNeutral.par_preserves pairIsNeutral pairStep
      by_cases pairEq : currentPair = pairTarget
      · subst pairEq
        subst targetEq
        exact (progressStep.2 rfl).elim
      · subst targetEq
        exact pairInduction pairTarget
          ⟨pairStep, pairEq⟩ pairTargetIsNeutral
    · exact (RawTerm.IsNeutral.not_pair
        (RawTerm.IsNeutral.par_preserves pairIsNeutral pairStep)
        (firstRaw := firstTarget) (secondRaw := secondTarget) rfl).elim

/-- Second projection with a neutral pair head is strongly normalizing
when the head is strongly normalizing. -/
theorem RawTerm.snd_neutral_isStronglyNormalizing {scope : Nat}
    {pairRaw : RawTerm scope}
    (pairIsNeutral : RawTerm.IsNeutral pairRaw)
    (pairIsSN : RawTerm.isStronglyNormalizing pairRaw) :
    RawTerm.isStronglyNormalizing (RawTerm.snd pairRaw) := by
  induction pairIsSN with
  | intro currentPair _ pairInduction =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.snd currentPair) ?_
    intro target progressStep
    rcases RawStep.par.snd_inv progressStep.1 with
      ⟨pairTarget, targetEq, pairStep⟩
      | ⟨firstTarget, secondTarget, _targetEq, pairStep⟩
    · have pairTargetIsNeutral : RawTerm.IsNeutral pairTarget :=
        RawTerm.IsNeutral.par_preserves pairIsNeutral pairStep
      by_cases pairEq : currentPair = pairTarget
      · subst pairEq
        subst targetEq
        exact (progressStep.2 rfl).elim
      · subst targetEq
        exact pairInduction pairTarget
          ⟨pairStep, pairEq⟩ pairTargetIsNeutral
    · exact (RawTerm.IsNeutral.not_pair
        (RawTerm.IsNeutral.par_preserves pairIsNeutral pairStep)
        (firstRaw := firstTarget) (secondRaw := secondTarget) rfl).elim

/-- **K12.20.AS neutral-app SN preservation**.  `RawTerm.app (var pos)
arg` is strongly normalizing whenever `arg` is.

This is the first **neutral-head application** SN helper — the
foundational building block for compound-Ty CR3 (variables are
Reducible at every type), which is in turn the prerequisite for
`ReducibleSubst.lift` / `.singleton` and the K12.20-head fundamental
theorem case for `Term.lam` proper.

Proof: induction on `arg`'s SN witness.  Step inversion of
`RawStep.par (app (var pos) currentArg) target` via `app_inv` gives
two arms: (1) cong on both subterms — `var pos` only par-reduces to
itself via `var_inv`, so the function position is rigid; the
argument-position cong is discharged by the inductive hypothesis on
the SN-progress of `currentArg`.  (2) shallow/deep β — would require
`var pos` par-reducing to a `lam` form, which `var_inv` rules out
via `RawTerm.noConfusion` on the resulting `var = lam` equation. -/
theorem RawTerm.app_var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope)
    {argRaw : RawTerm scope}
    (argIsSN : RawTerm.isStronglyNormalizing argRaw) :
    RawTerm.isStronglyNormalizing
      (RawTerm.app (RawTerm.var position) argRaw) := by
  induction argIsSN with
  | intro currentArg _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.app (RawTerm.var position) currentArg) ?_
    intro target progressStep
    rcases RawStep.par.app_inv progressStep.1 with
      ⟨functionTarget, argumentTarget, targetEq, functionStep, argumentStep⟩
      | ⟨bodyTarget, argumentTarget, _targetEq, functionStep, _argumentStep⟩
    · have functionEq : functionTarget = RawTerm.var position :=
        (RawStep.par.var_inv functionStep)
      subst functionEq
      subst targetEq
      have argumentDistinct :
          currentArg ≠ argumentTarget := fun argumentEq =>
        progressStep.2
          (congrArg (RawTerm.app (RawTerm.var position)) argumentEq)
      exact inductiveHypothesis argumentTarget
        ⟨argumentStep, argumentDistinct⟩
    · exact (by
        have varEqLam :
            RawTerm.lam bodyTarget = RawTerm.var position :=
          (RawStep.par.var_inv functionStep)
        nomatch varEqLam)

/-- **K12.20.AT.1 neutral fst SN preservation**.  `RawTerm.fst
(var pos)` is strongly normalizing.  Sister to `app_var`; `fst` is
a unary destructor for Σ pairs, β fires only when the inner term
par-reduces to `pair _ _`.  For variable inner, `var_inv` rules
that out — `var pos` only par-reduces to itself, never to a pair.
The cong arm is vacuous: the scrutinee is fixed, so no progress
step exists; `parProgress`'s source-≠-target requirement contradicts
`var_inv`. -/
theorem RawTerm.fst_var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope) :
    RawTerm.isStronglyNormalizing
      (RawTerm.fst (RawTerm.var position)) := by
  refine RawTerm.isStronglyNormalizing.intro
    (RawTerm.fst (RawTerm.var position)) ?_
  intro target progressStep
  rcases RawStep.par.fst_inv progressStep.1 with
    ⟨pairTarget, targetEq, pairStep⟩
    | ⟨firstTarget, secondTarget, _targetEq, pairStep⟩
  · have pairEq : pairTarget = RawTerm.var position :=
      (RawStep.par.var_inv pairStep)
    subst pairEq
    subst targetEq
    exact (progressStep.2 rfl).elim
  · exact (by
      have varEqPair :
          RawTerm.pair firstTarget secondTarget = RawTerm.var position :=
        (RawStep.par.var_inv pairStep)
      nomatch varEqPair)

/-- **K12.20.AT.2 neutral snd SN preservation**.  Sister to
`fst_var`; same proof shape, dual Σ projection. -/
theorem RawTerm.snd_var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope) :
    RawTerm.isStronglyNormalizing
      (RawTerm.snd (RawTerm.var position)) := by
  refine RawTerm.isStronglyNormalizing.intro
    (RawTerm.snd (RawTerm.var position)) ?_
  intro target progressStep
  rcases RawStep.par.snd_inv progressStep.1 with
    ⟨pairTarget, targetEq, pairStep⟩
    | ⟨firstTarget, secondTarget, _targetEq, pairStep⟩
  · have pairEq : pairTarget = RawTerm.var position :=
      (RawStep.par.var_inv pairStep)
    subst pairEq
    subst targetEq
    exact (progressStep.2 rfl).elim
  · exact (by
      have varEqPair :
          RawTerm.pair firstTarget secondTarget = RawTerm.var position :=
        (RawStep.par.var_inv pairStep)
      nomatch varEqPair)


end LeanFX2
