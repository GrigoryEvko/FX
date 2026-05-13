import LeanFX2.Reducibility.StableBase

/-! # LeanFX2.Reducibility.NeutralSNFoundation — K12.20.C foundation

Part 1 of the K12.20.C raw-level "neutral & natSucc SN preservation"
cascade.  Covers the foundation: variable SN, neutral-headed
application / projection / ι-recursor SN preservation.

## What ships

* `RawTerm.var_isStronglyNormalizing` — variables are vacuously
  SN (no `RawStep.par` ctor has a variable as source other than
  refl).
* `RawTerm.var_has_no_progress` — vacuous CR3 base fact.
* `RawTerm.app_neutral_isStronglyNormalizing` — application with
  a neutral function head is SN when both head and argument are
  SN.  The beta arm is impossible because
  `RawTerm.IsNeutral.par_preserves` (from Neutral.lean) keeps
  every reduct of the function neutral.
* `RawTerm.fst_neutral_isStronglyNormalizing` /
  `RawTerm.snd_neutral_isStronglyNormalizing` — Σ-projections
  on neutral pair.
* Neutral / `_var` variants for boolElim, natElim, natRec,
  listElim, optionMatch, eitherMatch, pathApp, glueElim,
  refineElim, recordProj, codataDest, equivApp, equivApply,
  idJ, oeqJ, idStrictRec ι-recursors.

Pattern: each `_neutral` or `_var` SN lemma is a structural
induction on the SN evidence of the sub-terms, using
`RawStep.par.X_inv` inversion plus `RawTerm.IsNeutral.par_preserves`
to discharge the impossible beta cases.

## Root status

Layer 3 metatheory leaf.  Builds on `Reducibility.Neutral` for
neutrality preservation.  Consumed by `NeutralSNHott`,
`NeutralSNIntro`, `NeutralSNClosure`, and the K12.20.U3 generic
CR3 dispatch. -/

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

/-- **K12.20.AU neutral boolElim SN preservation**.  `RawTerm.boolElim
(var pos) thenBranch elseBranch` is SN when both branches are SN.

First ternary neutral-head SN helper.  boolElim has three subterms
plus two ι rules (`iotaBoolElimTrue` / `False` for true/false
scrutinees).  Variable scrutinee blocks both ι rules via `var_inv`
(var doesn't par-reduce to `boolTrue` or `boolFalse`).  Cong arm
has all three subterms moving in parallel; with the scrutinee
rigid, the effective movement is binary on (thenBranch, elseBranch)
— nested induction like `pair_isStronglyNormalizing`.

Per `feedback_lean_induction_universal_motive.md`: state the
`elseBranch`-side universal in the conclusion to keep the IH wide
across nested induction on the two branches. -/
theorem RawTerm.boolElim_var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope)
    {thenBranch : RawTerm scope}
    (thenIsSN : RawTerm.isStronglyNormalizing thenBranch) :
    ∀ {elseBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing elseBranch →
      RawTerm.isStronglyNormalizing
        (RawTerm.boolElim (RawTerm.var position) thenBranch elseBranch) := by
  induction thenIsSN with
  | intro currentThen _ thenIH =>
    intro elseBranch elseIsSN
    induction elseIsSN with
    | intro currentElse elseClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.boolElim (RawTerm.var position) currentThen currentElse) ?_
      intro target progressStep
      rcases RawStep.par.boolElim_inv progressStep.1 with
        ⟨scrutineeTarget, thenTarget, elseTarget, targetEq,
          scrutineeStep, thenStep, elseStep⟩
        | (⟨thenTarget, _targetEq, scrutineeStep, _thenStep⟩
          | ⟨elseTarget, _targetEq, scrutineeStep, _elseStep⟩)
      · have scrutineeEq :
            scrutineeTarget = RawTerm.var position :=
          (RawStep.par.var_inv scrutineeStep)
        subst scrutineeEq
        subst targetEq
        by_cases thenEq : currentThen = thenTarget
        · subst thenEq
          have elseDistinct :
              currentElse ≠ elseTarget := fun elseEq =>
            progressStep.2 (congrArg
              (RawTerm.boolElim (RawTerm.var position) currentThen) elseEq)
          exact innerIH elseTarget ⟨elseStep, elseDistinct⟩
        · have thenProgress :
              RawStep.parProgress currentThen thenTarget :=
            ⟨thenStep, thenEq⟩
          by_cases elseEq : currentElse = elseTarget
          · subst elseEq
            exact thenIH thenTarget thenProgress
              (RawTerm.isStronglyNormalizing.intro currentElse elseClosure)
          · exact thenIH thenTarget thenProgress
              (elseClosure elseTarget ⟨elseStep, elseEq⟩)
      · exact (by
          have varEqTrue :
              RawTerm.var position = RawTerm.boolTrue :=
            (RawStep.par.var_inv scrutineeStep).symm
          nomatch varEqTrue)
      · exact (by
          have varEqFalse :
              RawTerm.var position = RawTerm.boolFalse :=
            (RawStep.par.var_inv scrutineeStep).symm
          nomatch varEqFalse)

/-- Boolean eliminator SN preservation.  This is the generic version
behind the neutral `boolElim_var` helper: congruence arms recurse through
the three SN subterms, while true/false ι arms return the corresponding
branch target. -/
theorem RawTerm.boolElim_isStronglyNormalizing {scope : Nat}
    {thenBranch : RawTerm scope}
    (thenIsSN : RawTerm.isStronglyNormalizing thenBranch) :
    ∀ {elseBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing elseBranch →
    ∀ {scrutinee : RawTerm scope},
      RawTerm.isStronglyNormalizing scrutinee →
      RawTerm.isStronglyNormalizing
        (RawTerm.boolElim scrutinee thenBranch elseBranch) := by
  induction thenIsSN with
  | intro currentThen thenClosure thenIH =>
    intro elseBranch elseIsSN
    induction elseIsSN with
    | intro currentElse elseClosure elseIH =>
      intro scrutinee scrutineeIsSN
      induction scrutineeIsSN with
      | intro currentScrutinee scrutineeClosure scrutineeIH =>
        refine RawTerm.isStronglyNormalizing.intro
          (RawTerm.boolElim currentScrutinee currentThen currentElse) ?_
        intro target progressStep
        cases RawStep.par.boolElim_inv progressStep.1 with
        | inl congruentStep =>
          rcases congruentStep with
            ⟨scrutineeTarget, thenTarget, elseTarget, targetEq,
              scrutineeStep, thenStep, elseStep⟩
          subst targetEq
          by_cases thenEq : currentThen = thenTarget
          · subst thenEq
            by_cases elseEq : currentElse = elseTarget
            · subst elseEq
              by_cases scrutineeEq : currentScrutinee = scrutineeTarget
              · subst scrutineeEq
                exact (progressStep.2 rfl).elim
              · exact scrutineeIH scrutineeTarget
                  ⟨scrutineeStep, scrutineeEq⟩
            · have scrutineeTargetIsSN :
                  RawTerm.isStronglyNormalizing scrutineeTarget := by
                by_cases scrutineeEq : currentScrutinee = scrutineeTarget
                · subst scrutineeEq
                  exact RawTerm.isStronglyNormalizing.intro currentScrutinee
                    scrutineeClosure
                · exact scrutineeClosure scrutineeTarget
                    ⟨scrutineeStep, scrutineeEq⟩
              exact elseIH elseTarget ⟨elseStep, elseEq⟩
                scrutineeTargetIsSN
          · have elseTargetIsSN :
                RawTerm.isStronglyNormalizing elseTarget := by
              by_cases elseEq : currentElse = elseTarget
              · subst elseEq
                exact RawTerm.isStronglyNormalizing.intro currentElse
                  elseClosure
              · exact elseClosure elseTarget ⟨elseStep, elseEq⟩
            have scrutineeTargetIsSN :
                RawTerm.isStronglyNormalizing scrutineeTarget := by
              by_cases scrutineeEq : currentScrutinee = scrutineeTarget
              · subst scrutineeEq
                exact RawTerm.isStronglyNormalizing.intro currentScrutinee
                  scrutineeClosure
              · exact scrutineeClosure scrutineeTarget
                  ⟨scrutineeStep, scrutineeEq⟩
            exact thenIH thenTarget ⟨thenStep, thenEq⟩
              elseTargetIsSN scrutineeTargetIsSN
        | inr iotaStep =>
          cases iotaStep with
          | inl trueStep =>
            rcases trueStep with
              ⟨thenTarget, targetEq, _scrutineeStep, thenStep⟩
            rw [targetEq]
            by_cases thenEq : currentThen = thenTarget
            · subst thenEq
              exact RawTerm.isStronglyNormalizing.intro currentThen
                thenClosure
            · exact thenClosure thenTarget ⟨thenStep, thenEq⟩
          | inr falseStep =>
            rcases falseStep with
              ⟨elseTarget, targetEq, _scrutineeStep, elseStep⟩
            rw [targetEq]
            by_cases elseEq : currentElse = elseTarget
            · subst elseEq
              exact RawTerm.isStronglyNormalizing.intro currentElse
                elseClosure
            · exact elseClosure elseTarget ⟨elseStep, elseEq⟩

/-- **K12.20.AV.1 neutral natElim SN preservation**.  Sister to
`boolElim_var`; nat-recursor with variable scrutinee.

Same nested-induction template as `boolElim_var`: variable
scrutinee blocks both ι rules (`iotaNatElimZero` requires
`var → natZero`, `iotaNatElimSucc` requires `var → natSucc _`),
the cong arm collapses to binary movement on (zeroBranch,
succBranch). -/
theorem RawTerm.natElim_var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope)
    {zeroBranch : RawTerm scope}
    (zeroIsSN : RawTerm.isStronglyNormalizing zeroBranch) :
    ∀ {succBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing succBranch →
      RawTerm.isStronglyNormalizing
        (RawTerm.natElim (RawTerm.var position) zeroBranch succBranch) := by
  induction zeroIsSN with
  | intro currentZero _ zeroIH =>
    intro succBranch succIsSN
    induction succIsSN with
    | intro currentSucc succClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.natElim (RawTerm.var position) currentZero currentSucc) ?_
      intro target progressStep
      rcases RawStep.par.natElim_inv progressStep.1 with
        ⟨scrutineeTarget, zeroTarget, succTarget, targetEq,
          scrutineeStep, zeroStep, succStep⟩
        | (⟨zeroTarget, _targetEq, scrutineeStep, _zeroStep⟩
          | ⟨predRaw, succTarget, _targetEq, scrutineeStep, _succStep⟩)
      · have scrutineeEq :
            scrutineeTarget = RawTerm.var position :=
          (RawStep.par.var_inv scrutineeStep)
        subst scrutineeEq
        subst targetEq
        by_cases zeroEq : currentZero = zeroTarget
        · subst zeroEq
          have succDistinct :
              currentSucc ≠ succTarget := fun succEq =>
            progressStep.2 (congrArg
              (RawTerm.natElim (RawTerm.var position) currentZero) succEq)
          exact innerIH succTarget ⟨succStep, succDistinct⟩
        · have zeroProgress :
              RawStep.parProgress currentZero zeroTarget :=
            ⟨zeroStep, zeroEq⟩
          by_cases succEq : currentSucc = succTarget
          · subst succEq
            exact zeroIH zeroTarget zeroProgress
              (RawTerm.isStronglyNormalizing.intro currentSucc succClosure)
          · exact zeroIH zeroTarget zeroProgress
              (succClosure succTarget ⟨succStep, succEq⟩)
      · exact (by
          have varEqZero :
              RawTerm.var position = RawTerm.natZero :=
            (RawStep.par.var_inv scrutineeStep).symm
          nomatch varEqZero)
      · exact (by
          have varEqSucc :
              RawTerm.var position = RawTerm.natSucc predRaw :=
            (RawStep.par.var_inv scrutineeStep).symm
          nomatch varEqSucc)

/-- **K12.20.AV.2 neutral natRec SN preservation**.  Sister to
`natElim_var`; nat recursor (motive-dependent) with variable
scrutinee.  Same proof shape; the succ-ι rule rebuilds the
target into `app (app succ predRaw) (natRec predRaw zero succ)`
but inversion still requires `scrutinee → natSucc predRaw`,
which `var_inv` rules out. -/
theorem RawTerm.natRec_var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope)
    {zeroBranch : RawTerm scope}
    (zeroIsSN : RawTerm.isStronglyNormalizing zeroBranch) :
    ∀ {succBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing succBranch →
      RawTerm.isStronglyNormalizing
        (RawTerm.natRec (RawTerm.var position) zeroBranch succBranch) := by
  induction zeroIsSN with
  | intro currentZero _ zeroIH =>
    intro succBranch succIsSN
    induction succIsSN with
    | intro currentSucc succClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.natRec (RawTerm.var position) currentZero currentSucc) ?_
      intro target progressStep
      rcases RawStep.par.natRec_inv progressStep.1 with
        ⟨scrutineeTarget, zeroTarget, succTarget, targetEq,
          scrutineeStep, zeroStep, succStep⟩
        | (⟨zeroTarget, _targetEq, scrutineeStep, _zeroStep⟩
          | ⟨predRaw, zeroTarget, succTarget,
              _targetEq, scrutineeStep, _zeroStep, _succStep⟩)
      · have scrutineeEq :
            scrutineeTarget = RawTerm.var position :=
          (RawStep.par.var_inv scrutineeStep)
        subst scrutineeEq
        subst targetEq
        by_cases zeroEq : currentZero = zeroTarget
        · subst zeroEq
          have succDistinct :
              currentSucc ≠ succTarget := fun succEq =>
            progressStep.2 (congrArg
              (RawTerm.natRec (RawTerm.var position) currentZero) succEq)
          exact innerIH succTarget ⟨succStep, succDistinct⟩
        · have zeroProgress :
              RawStep.parProgress currentZero zeroTarget :=
            ⟨zeroStep, zeroEq⟩
          by_cases succEq : currentSucc = succTarget
          · subst succEq
            exact zeroIH zeroTarget zeroProgress
              (RawTerm.isStronglyNormalizing.intro currentSucc succClosure)
          · exact zeroIH zeroTarget zeroProgress
              (succClosure succTarget ⟨succStep, succEq⟩)
      · exact (by
          have varEqZero :
              RawTerm.var position = RawTerm.natZero :=
            (RawStep.par.var_inv scrutineeStep).symm
          nomatch varEqZero)
      · exact (by
          have varEqSucc :
              RawTerm.var position = RawTerm.natSucc predRaw :=
            (RawStep.par.var_inv scrutineeStep).symm
          nomatch varEqSucc)

/-- **K12.20.AW.1 neutral listElim SN preservation**.  Sister to
the K12.20.AU/AV eliminator family; parametric-list recursor.

Variable scrutinee blocks both ι rules — `iotaListElimNil` needs
`var → listNil`, `iotaListElimCons` needs `var → listCons _ _` —
discharged via `var_inv` on each ι arm. -/
theorem RawTerm.listElim_var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope)
    {nilBranch : RawTerm scope}
    (nilIsSN : RawTerm.isStronglyNormalizing nilBranch) :
    ∀ {consBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing consBranch →
      RawTerm.isStronglyNormalizing
        (RawTerm.listElim (RawTerm.var position) nilBranch consBranch) := by
  induction nilIsSN with
  | intro currentNil _ nilIH =>
    intro consBranch consIsSN
    induction consIsSN with
    | intro currentCons consClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.listElim (RawTerm.var position) currentNil currentCons) ?_
      intro target progressStep
      rcases RawStep.par.listElim_inv progressStep.1 with
        ⟨scrutineeTarget, nilTarget, consTarget, targetEq,
          scrutineeStep, nilStep, consStep⟩
        | (⟨nilTarget, _targetEq, scrutineeStep, _nilStep⟩
          | ⟨headRaw, tailRaw, consTarget,
              _targetEq, scrutineeStep, _consStep⟩)
      · have scrutineeEq :
            scrutineeTarget = RawTerm.var position :=
          (RawStep.par.var_inv scrutineeStep)
        subst scrutineeEq
        subst targetEq
        by_cases nilEq : currentNil = nilTarget
        · subst nilEq
          have consDistinct :
              currentCons ≠ consTarget := fun consEq =>
            progressStep.2 (congrArg
              (RawTerm.listElim (RawTerm.var position) currentNil) consEq)
          exact innerIH consTarget ⟨consStep, consDistinct⟩
        · have nilProgress :
              RawStep.parProgress currentNil nilTarget :=
            ⟨nilStep, nilEq⟩
          by_cases consEq : currentCons = consTarget
          · subst consEq
            exact nilIH nilTarget nilProgress
              (RawTerm.isStronglyNormalizing.intro currentCons consClosure)
          · exact nilIH nilTarget nilProgress
              (consClosure consTarget ⟨consStep, consEq⟩)
      · exact (by
          have varEqNil :
              RawTerm.var position = RawTerm.listNil :=
            (RawStep.par.var_inv scrutineeStep).symm
          nomatch varEqNil)
      · exact (by
          have varEqCons :
              RawTerm.var position = RawTerm.listCons headRaw tailRaw :=
            (RawStep.par.var_inv scrutineeStep).symm
          nomatch varEqCons)

/-- List elimination with a neutral scrutinee is strongly normalizing
when the scrutinee and both branches are strongly normalizing.

The list ι arms are impossible because every parallel reduct of the
neutral scrutinee stays neutral, and neutral terms are never `listNil`
or `listCons` shaped.  The congruence arm recurses lexicographically on
scrutinee, nil-branch, and cons-branch progress. -/
theorem RawTerm.listElim_neutral_isStronglyNormalizing {scope : Nat}
    {scrutineeRaw nilBranch consBranch : RawTerm scope}
    (scrutineeIsNeutral : RawTerm.IsNeutral scrutineeRaw)
    (scrutineeIsSN : RawTerm.isStronglyNormalizing scrutineeRaw)
    (nilIsSN : RawTerm.isStronglyNormalizing nilBranch)
    (consIsSN : RawTerm.isStronglyNormalizing consBranch) :
    RawTerm.isStronglyNormalizing
      (RawTerm.listElim scrutineeRaw nilBranch consBranch) := by
  induction scrutineeIsSN generalizing nilBranch consBranch with
  | intro currentScrutinee _ scrutineeInduction =>
    induction nilIsSN generalizing consBranch with
    | intro currentNil nilClosure nilInduction =>
      induction consIsSN with
      | intro currentCons consClosure consInduction =>
        refine RawTerm.isStronglyNormalizing.intro
          (RawTerm.listElim currentScrutinee currentNil currentCons) ?_
        intro target progressStep
        rcases RawStep.par.listElim_inv progressStep.1 with
          ⟨scrutineeTarget, nilTarget, consTarget, targetEq,
            scrutineeStep, nilStep, consStep⟩
          | (⟨_nilTarget, _targetEq, scrutineeStep, _nilStep⟩
            | ⟨headRaw, tailRaw, _consTarget, _targetEq,
                scrutineeStep, _consStep⟩)
        · subst targetEq
          have scrutineeTargetIsNeutral :
              RawTerm.IsNeutral scrutineeTarget :=
            RawTerm.IsNeutral.par_preserves scrutineeIsNeutral
              scrutineeStep
          have nilTargetIsSN :
              RawTerm.isStronglyNormalizing nilTarget := by
            by_cases nilEq : currentNil = nilTarget
            · subst nilEq
              exact RawTerm.isStronglyNormalizing.intro
                currentNil nilClosure
            · exact nilClosure nilTarget ⟨nilStep, nilEq⟩
          have consTargetIsSN :
              RawTerm.isStronglyNormalizing consTarget := by
            by_cases consEq : currentCons = consTarget
            · subst consEq
              exact RawTerm.isStronglyNormalizing.intro
                currentCons consClosure
            · exact consClosure consTarget ⟨consStep, consEq⟩
          by_cases scrutineeEq : currentScrutinee = scrutineeTarget
          · subst scrutineeEq
            by_cases nilEq : currentNil = nilTarget
            · subst nilEq
              by_cases consEq : currentCons = consTarget
              · subst consEq
                exact (progressStep.2 rfl).elim
              · exact consInduction consTarget ⟨consStep, consEq⟩
            · exact nilInduction nilTarget ⟨nilStep, nilEq⟩
                consTargetIsSN
          · exact scrutineeInduction scrutineeTarget
              ⟨scrutineeStep, scrutineeEq⟩
              scrutineeTargetIsNeutral nilTargetIsSN consTargetIsSN
        · exact (RawTerm.IsNeutral.not_listNil
            (RawTerm.IsNeutral.par_preserves scrutineeIsNeutral
              scrutineeStep) rfl).elim
        · exact (RawTerm.IsNeutral.not_listCons
            (RawTerm.IsNeutral.par_preserves scrutineeIsNeutral
              scrutineeStep)
            (headRaw := headRaw) (tailRaw := tailRaw) rfl).elim

/-- **K12.20.AW.2 neutral optionMatch SN preservation**.  Sister
to `listElim_var`; option-eliminator with variable scrutinee.
Same proof shape; ι rules need `var → optionNone` and
`var → optionSome _`. -/
theorem RawTerm.optionMatch_var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope)
    {noneBranch : RawTerm scope}
    (noneIsSN : RawTerm.isStronglyNormalizing noneBranch) :
    ∀ {someBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing someBranch →
      RawTerm.isStronglyNormalizing
        (RawTerm.optionMatch (RawTerm.var position) noneBranch someBranch) := by
  induction noneIsSN with
  | intro currentNone _ noneIH =>
    intro someBranch someIsSN
    induction someIsSN with
    | intro currentSome someClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.optionMatch (RawTerm.var position) currentNone currentSome) ?_
      intro target progressStep
      rcases RawStep.par.optionMatch_inv progressStep.1 with
        ⟨scrutineeTarget, noneTarget, someTarget, targetEq,
          scrutineeStep, noneStep, someStep⟩
        | (⟨noneTarget, _targetEq, scrutineeStep, _noneStep⟩
          | ⟨valueRaw, someTarget, _targetEq, scrutineeStep, _someStep⟩)
      · have scrutineeEq :
            scrutineeTarget = RawTerm.var position :=
          (RawStep.par.var_inv scrutineeStep)
        subst scrutineeEq
        subst targetEq
        by_cases noneEq : currentNone = noneTarget
        · subst noneEq
          have someDistinct :
              currentSome ≠ someTarget := fun someEq =>
            progressStep.2 (congrArg
              (RawTerm.optionMatch (RawTerm.var position) currentNone) someEq)
          exact innerIH someTarget ⟨someStep, someDistinct⟩
        · have noneProgress :
              RawStep.parProgress currentNone noneTarget :=
            ⟨noneStep, noneEq⟩
          by_cases someEq : currentSome = someTarget
          · subst someEq
            exact noneIH noneTarget noneProgress
              (RawTerm.isStronglyNormalizing.intro currentSome someClosure)
          · exact noneIH noneTarget noneProgress
              (someClosure someTarget ⟨someStep, someEq⟩)
      · exact (by
          have varEqNone :
              RawTerm.var position = RawTerm.optionNone :=
            (RawStep.par.var_inv scrutineeStep).symm
          nomatch varEqNone)
      · exact (by
          have varEqSome :
              RawTerm.var position = RawTerm.optionSome valueRaw :=
            (RawStep.par.var_inv scrutineeStep).symm
          nomatch varEqSome)

/-- Option matching with a neutral scrutinee is strongly normalizing
when the scrutinee and both branches are strongly normalizing.

The option ι arms are impossible because every parallel reduct of the
neutral scrutinee stays neutral, and neutral terms are never
`optionNone` or `optionSome` shaped.  The congruence arm recurses across
scrutinee, none-branch, and some-branch progress. -/
theorem RawTerm.optionMatch_neutral_isStronglyNormalizing {scope : Nat}
    {scrutineeRaw noneBranch someBranch : RawTerm scope}
    (scrutineeIsNeutral : RawTerm.IsNeutral scrutineeRaw)
    (scrutineeIsSN : RawTerm.isStronglyNormalizing scrutineeRaw)
    (noneIsSN : RawTerm.isStronglyNormalizing noneBranch)
    (someIsSN : RawTerm.isStronglyNormalizing someBranch) :
    RawTerm.isStronglyNormalizing
      (RawTerm.optionMatch scrutineeRaw noneBranch someBranch) := by
  induction scrutineeIsSN generalizing noneBranch someBranch with
  | intro currentScrutinee _ scrutineeInduction =>
    induction noneIsSN generalizing someBranch with
    | intro currentNone noneClosure noneInduction =>
      induction someIsSN with
      | intro currentSome someClosure someInduction =>
        refine RawTerm.isStronglyNormalizing.intro
          (RawTerm.optionMatch currentScrutinee currentNone currentSome) ?_
        intro target progressStep
        rcases RawStep.par.optionMatch_inv progressStep.1 with
          ⟨scrutineeTarget, noneTarget, someTarget, targetEq,
            scrutineeStep, noneStep, someStep⟩
          | (⟨_noneTarget, _targetEq, scrutineeStep, _noneStep⟩
            | ⟨valueRaw, _someTarget, _targetEq,
                scrutineeStep, _someStep⟩)
        · subst targetEq
          have scrutineeTargetIsNeutral :
              RawTerm.IsNeutral scrutineeTarget :=
            RawTerm.IsNeutral.par_preserves scrutineeIsNeutral
              scrutineeStep
          have noneTargetIsSN :
              RawTerm.isStronglyNormalizing noneTarget := by
            by_cases noneEq : currentNone = noneTarget
            · subst noneEq
              exact RawTerm.isStronglyNormalizing.intro
                currentNone noneClosure
            · exact noneClosure noneTarget ⟨noneStep, noneEq⟩
          have someTargetIsSN :
              RawTerm.isStronglyNormalizing someTarget := by
            by_cases someEq : currentSome = someTarget
            · subst someEq
              exact RawTerm.isStronglyNormalizing.intro
                currentSome someClosure
            · exact someClosure someTarget ⟨someStep, someEq⟩
          by_cases scrutineeEq : currentScrutinee = scrutineeTarget
          · subst scrutineeEq
            by_cases noneEq : currentNone = noneTarget
            · subst noneEq
              by_cases someEq : currentSome = someTarget
              · subst someEq
                exact (progressStep.2 rfl).elim
              · exact someInduction someTarget ⟨someStep, someEq⟩
            · exact noneInduction noneTarget ⟨noneStep, noneEq⟩
                someTargetIsSN
          · exact scrutineeInduction scrutineeTarget
              ⟨scrutineeStep, scrutineeEq⟩
              scrutineeTargetIsNeutral noneTargetIsSN someTargetIsSN
        · exact (RawTerm.IsNeutral.not_optionNone
            (RawTerm.IsNeutral.par_preserves scrutineeIsNeutral
              scrutineeStep) rfl).elim
        · exact (RawTerm.IsNeutral.not_optionSome
            (RawTerm.IsNeutral.par_preserves scrutineeIsNeutral
              scrutineeStep)
            (valueRaw := valueRaw) rfl).elim

/-- **K12.20.AW.3 neutral eitherMatch SN preservation**.  Sister
to `listElim_var` / `optionMatch_var`; either-eliminator with
variable scrutinee.  Both ι rules carry a payload value (no
nullary constructor on either side), so both demand
`var → eitherInl _` / `var → eitherInr _` — both blocked by
`var_inv`. -/
theorem RawTerm.eitherMatch_var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope)
    {leftBranch : RawTerm scope}
    (leftIsSN : RawTerm.isStronglyNormalizing leftBranch) :
    ∀ {rightBranch : RawTerm scope},
      RawTerm.isStronglyNormalizing rightBranch →
      RawTerm.isStronglyNormalizing
        (RawTerm.eitherMatch (RawTerm.var position) leftBranch rightBranch) := by
  induction leftIsSN with
  | intro currentLeft _ leftIH =>
    intro rightBranch rightIsSN
    induction rightIsSN with
    | intro currentRight rightClosure innerIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.eitherMatch (RawTerm.var position)
          currentLeft currentRight) ?_
      intro target progressStep
      rcases RawStep.par.eitherMatch_inv progressStep.1 with
        ⟨scrutineeTarget, leftTarget, rightTarget, targetEq,
          scrutineeStep, leftStep, rightStep⟩
        | (⟨valueRaw, leftTarget, _targetEq, scrutineeStep, _leftStep⟩
          | ⟨valueRaw, rightTarget, _targetEq, scrutineeStep, _rightStep⟩)
      · have scrutineeEq :
            scrutineeTarget = RawTerm.var position :=
          (RawStep.par.var_inv scrutineeStep)
        subst scrutineeEq
        subst targetEq
        by_cases leftEq : currentLeft = leftTarget
        · subst leftEq
          have rightDistinct :
              currentRight ≠ rightTarget := fun rightEq =>
            progressStep.2 (congrArg
              (RawTerm.eitherMatch (RawTerm.var position) currentLeft) rightEq)
          exact innerIH rightTarget ⟨rightStep, rightDistinct⟩
        · have leftProgress :
              RawStep.parProgress currentLeft leftTarget :=
            ⟨leftStep, leftEq⟩
          by_cases rightEq : currentRight = rightTarget
          · subst rightEq
            exact leftIH leftTarget leftProgress
              (RawTerm.isStronglyNormalizing.intro currentRight rightClosure)
          · exact leftIH leftTarget leftProgress
              (rightClosure rightTarget ⟨rightStep, rightEq⟩)
      · exact (by
          have varEqInl :
              RawTerm.var position = RawTerm.eitherInl valueRaw :=
            (RawStep.par.var_inv scrutineeStep).symm
          nomatch varEqInl)
      · exact (by
          have varEqInr :
              RawTerm.var position = RawTerm.eitherInr valueRaw :=
            (RawStep.par.var_inv scrutineeStep).symm
          nomatch varEqInr)

/-- Either matching with a neutral scrutinee is strongly normalizing
when the scrutinee and both branches are strongly normalizing.

The either ι arms are impossible because every parallel reduct of the
neutral scrutinee stays neutral, and neutral terms are never
`eitherInl` or `eitherInr` shaped.  The congruence arm recurses across
scrutinee, left branch, and right branch progress. -/
theorem RawTerm.eitherMatch_neutral_isStronglyNormalizing {scope : Nat}
    {scrutineeRaw leftBranch rightBranch : RawTerm scope}
    (scrutineeIsNeutral : RawTerm.IsNeutral scrutineeRaw)
    (scrutineeIsSN : RawTerm.isStronglyNormalizing scrutineeRaw)
    (leftIsSN : RawTerm.isStronglyNormalizing leftBranch)
    (rightIsSN : RawTerm.isStronglyNormalizing rightBranch) :
    RawTerm.isStronglyNormalizing
      (RawTerm.eitherMatch scrutineeRaw leftBranch rightBranch) := by
  induction scrutineeIsSN generalizing leftBranch rightBranch with
  | intro currentScrutinee _ scrutineeInduction =>
    induction leftIsSN generalizing rightBranch with
    | intro currentLeft leftClosure leftInduction =>
      induction rightIsSN with
      | intro currentRight rightClosure rightInduction =>
        refine RawTerm.isStronglyNormalizing.intro
          (RawTerm.eitherMatch currentScrutinee currentLeft currentRight) ?_
        intro target progressStep
        rcases RawStep.par.eitherMatch_inv progressStep.1 with
          ⟨scrutineeTarget, leftTarget, rightTarget, targetEq,
            scrutineeStep, leftStep, rightStep⟩
          | (⟨valueRaw, _leftTarget, _targetEq,
                scrutineeStep, _leftStep⟩
            | ⟨valueRaw, _rightTarget, _targetEq,
                scrutineeStep, _rightStep⟩)
        · subst targetEq
          have scrutineeTargetIsNeutral :
              RawTerm.IsNeutral scrutineeTarget :=
            RawTerm.IsNeutral.par_preserves scrutineeIsNeutral
              scrutineeStep
          have leftTargetIsSN :
              RawTerm.isStronglyNormalizing leftTarget := by
            by_cases leftEq : currentLeft = leftTarget
            · subst leftEq
              exact RawTerm.isStronglyNormalizing.intro
                currentLeft leftClosure
            · exact leftClosure leftTarget ⟨leftStep, leftEq⟩
          have rightTargetIsSN :
              RawTerm.isStronglyNormalizing rightTarget := by
            by_cases rightEq : currentRight = rightTarget
            · subst rightEq
              exact RawTerm.isStronglyNormalizing.intro
                currentRight rightClosure
            · exact rightClosure rightTarget ⟨rightStep, rightEq⟩
          by_cases scrutineeEq : currentScrutinee = scrutineeTarget
          · subst scrutineeEq
            by_cases leftEq : currentLeft = leftTarget
            · subst leftEq
              by_cases rightEq : currentRight = rightTarget
              · subst rightEq
                exact (progressStep.2 rfl).elim
              · exact rightInduction rightTarget ⟨rightStep, rightEq⟩
            · exact leftInduction leftTarget ⟨leftStep, leftEq⟩
                rightTargetIsSN
          · exact scrutineeInduction scrutineeTarget
              ⟨scrutineeStep, scrutineeEq⟩
              scrutineeTargetIsNeutral leftTargetIsSN rightTargetIsSN
        · exact (RawTerm.IsNeutral.not_eitherInl
            (RawTerm.IsNeutral.par_preserves scrutineeIsNeutral
              scrutineeStep)
            (valueRaw := valueRaw) rfl).elim
        · exact (RawTerm.IsNeutral.not_eitherInr
            (RawTerm.IsNeutral.par_preserves scrutineeIsNeutral
              scrutineeStep)
            (valueRaw := valueRaw) rfl).elim

/-- **K12.20.AX.1 neutral pathApp SN preservation**.  Direct analogue
of `app_var`: var sits in the path-term slot, interval argument is
SN witness.  `pathApp_inv` gives 2 arms (cong + β); β arm requires
`pathTerm → pathLam _`, defeated by `var_inv` + nomatch on the
resulting `var = pathLam _` equation. -/
theorem RawTerm.pathApp_var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope)
    {intervalArgRaw : RawTerm scope}
    (intervalIsSN : RawTerm.isStronglyNormalizing intervalArgRaw) :
    RawTerm.isStronglyNormalizing
      (RawTerm.pathApp (RawTerm.var position) intervalArgRaw) := by
  induction intervalIsSN with
  | intro currentInterval _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.pathApp (RawTerm.var position) currentInterval) ?_
    intro target progressStep
    rcases RawStep.par.pathApp_inv progressStep.1 with
      ⟨pathTarget, intervalTarget, targetEq, pathStep, intervalStep⟩
      | ⟨bodyTarget, _intervalTarget, _targetEq, pathStep, _intervalStep⟩
    · have pathEq : pathTarget = RawTerm.var position :=
        (RawStep.par.var_inv pathStep)
      subst pathEq
      subst targetEq
      have intervalDistinct :
          currentInterval ≠ intervalTarget := fun intervalEq =>
        progressStep.2
          (congrArg (RawTerm.pathApp (RawTerm.var position)) intervalEq)
      exact inductiveHypothesis intervalTarget
        ⟨intervalStep, intervalDistinct⟩
    · exact (by
        have varEqPathLam :
            RawTerm.pathLam bodyTarget = RawTerm.var position :=
          (RawStep.par.var_inv pathStep)
        nomatch varEqPathLam)

/-- Path application with a neutral path head is strongly normalizing
when both the path head and interval argument are strongly normalizing.

The path beta arms are impossible because every parallel reduct of the
neutral head stays neutral, and neutral terms are never `pathLam`-
shaped.  The congruence arm recurses on head progress or interval
progress. -/
theorem RawTerm.pathApp_neutral_isStronglyNormalizing {scope : Nat}
    {pathRaw intervalArgRaw : RawTerm scope}
    (pathIsNeutral : RawTerm.IsNeutral pathRaw)
    (pathIsSN : RawTerm.isStronglyNormalizing pathRaw)
    (intervalIsSN : RawTerm.isStronglyNormalizing intervalArgRaw) :
    RawTerm.isStronglyNormalizing
      (RawTerm.pathApp pathRaw intervalArgRaw) := by
  induction pathIsSN generalizing intervalArgRaw with
  | intro currentPath _ pathInduction =>
    induction intervalIsSN with
    | intro currentInterval intervalClosure intervalInduction =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.pathApp currentPath currentInterval) ?_
      intro target progressStep
      rcases RawStep.par.pathApp_inv progressStep.1 with
        ⟨pathTarget, intervalTarget, targetEq, pathStep, intervalStep⟩
        | ⟨bodyTarget, _intervalTarget, _targetEq,
            pathStep, _intervalStep⟩
      · subst targetEq
        have pathTargetIsNeutral : RawTerm.IsNeutral pathTarget :=
          RawTerm.IsNeutral.par_preserves pathIsNeutral pathStep
        have intervalTargetIsSN :
            RawTerm.isStronglyNormalizing intervalTarget := by
          by_cases intervalEq : currentInterval = intervalTarget
          · subst intervalEq
            exact RawTerm.isStronglyNormalizing.intro
              currentInterval intervalClosure
          · exact intervalClosure intervalTarget
              ⟨intervalStep, intervalEq⟩
        by_cases pathEq : currentPath = pathTarget
        · subst pathEq
          by_cases intervalEq : currentInterval = intervalTarget
          · subst intervalEq
            exact (progressStep.2 rfl).elim
          · exact intervalInduction intervalTarget
              ⟨intervalStep, intervalEq⟩
        · exact pathInduction pathTarget
            ⟨pathStep, pathEq⟩
            pathTargetIsNeutral
            intervalTargetIsSN
      · exact (RawTerm.IsNeutral.not_pathLam
          (RawTerm.IsNeutral.par_preserves pathIsNeutral pathStep)
          (bodyRaw := bodyTarget) rfl).elim

/-- Glue elimination with a neutral glued value is strongly normalizing
when the glued value is strongly normalizing.

The Glue beta arms are impossible because every parallel reduct of the
neutral glued value stays neutral, and neutral terms are never
`glueIntro`-shaped.  The congruence arm recurses on glued-value
progress. -/
theorem RawTerm.glueElim_neutral_isStronglyNormalizing {scope : Nat}
    {gluedRaw : RawTerm scope}
    (gluedIsNeutral : RawTerm.IsNeutral gluedRaw)
    (gluedIsSN : RawTerm.isStronglyNormalizing gluedRaw) :
    RawTerm.isStronglyNormalizing (RawTerm.glueElim gluedRaw) := by
  induction gluedIsSN with
  | intro currentGlued _ gluedInduction =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.glueElim currentGlued) ?_
    intro target progressStep
    rcases RawStep.par.glueElim_inv progressStep.1 with
      ⟨gluedTarget, targetEq, gluedStep⟩
      | ⟨baseTarget, partialTarget, _targetEq, gluedStep⟩
    · have gluedTargetIsNeutral : RawTerm.IsNeutral gluedTarget :=
        RawTerm.IsNeutral.par_preserves gluedIsNeutral gluedStep
      by_cases gluedEq : currentGlued = gluedTarget
      · subst gluedEq
        subst targetEq
        exact (progressStep.2 rfl).elim
      · subst targetEq
        exact gluedInduction gluedTarget
          ⟨gluedStep, gluedEq⟩ gluedTargetIsNeutral
    · exact (RawTerm.IsNeutral.not_glueIntro
        (RawTerm.IsNeutral.par_preserves gluedIsNeutral gluedStep)
        (baseRaw := baseTarget) (partialRaw := partialTarget) rfl).elim

/-- Refinement elimination with a neutral refined value is strongly
normalizing when the refined value is strongly normalizing.

The refinement beta arms are impossible because every parallel reduct
of the neutral refined value stays neutral, and neutral terms are never
`refineIntro`-shaped.  The congruence arm recurses on refined-value
progress. -/
theorem RawTerm.refineElim_neutral_isStronglyNormalizing {scope : Nat}
    {refinedRaw : RawTerm scope}
    (refinedIsNeutral : RawTerm.IsNeutral refinedRaw)
    (refinedIsSN : RawTerm.isStronglyNormalizing refinedRaw) :
    RawTerm.isStronglyNormalizing (RawTerm.refineElim refinedRaw) := by
  induction refinedIsSN with
  | intro currentRefined _ refinedInduction =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.refineElim currentRefined) ?_
    intro target progressStep
    rcases RawStep.par.refineElim_inv progressStep.1 with
      ⟨refinedTarget, targetEq, refinedStep⟩
      | ⟨valueTarget, proofTarget, _targetEq, refinedStep⟩
    · have refinedTargetIsNeutral :
          RawTerm.IsNeutral refinedTarget :=
        RawTerm.IsNeutral.par_preserves refinedIsNeutral refinedStep
      by_cases refinedEq : currentRefined = refinedTarget
      · subst refinedEq
        subst targetEq
        exact (progressStep.2 rfl).elim
      · subst targetEq
        exact refinedInduction refinedTarget
          ⟨refinedStep, refinedEq⟩ refinedTargetIsNeutral
    · exact (RawTerm.IsNeutral.not_refineIntro
        (RawTerm.IsNeutral.par_preserves refinedIsNeutral refinedStep)
        (valueRaw := valueTarget) (proofRaw := proofTarget) rfl).elim

/-- Record projection with a neutral record value is strongly
normalizing when the record value is strongly normalizing.

The record beta arms are impossible because every parallel reduct of
the neutral record value stays neutral, and neutral terms are never
`recordIntro`-shaped.  The congruence arm recurses on record-value
progress. -/
theorem RawTerm.recordProj_neutral_isStronglyNormalizing {scope : Nat}
    {recordRaw : RawTerm scope}
    (recordIsNeutral : RawTerm.IsNeutral recordRaw)
    (recordIsSN : RawTerm.isStronglyNormalizing recordRaw) :
    RawTerm.isStronglyNormalizing (RawTerm.recordProj recordRaw) := by
  induction recordIsSN with
  | intro currentRecord _ recordInduction =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.recordProj currentRecord) ?_
    intro target progressStep
    rcases RawStep.par.recordProj_inv progressStep.1 with
      ⟨recordTarget, targetEq, recordStep⟩
      | ⟨fieldTarget, _targetEq, recordStep⟩
    · have recordTargetIsNeutral :
          RawTerm.IsNeutral recordTarget :=
        RawTerm.IsNeutral.par_preserves recordIsNeutral recordStep
      by_cases recordEq : currentRecord = recordTarget
      · subst recordEq
        subst targetEq
        exact (progressStep.2 rfl).elim
      · subst targetEq
        exact recordInduction recordTarget
          ⟨recordStep, recordEq⟩ recordTargetIsNeutral
    · exact (RawTerm.IsNeutral.not_recordIntro
        (RawTerm.IsNeutral.par_preserves recordIsNeutral recordStep)
        (fieldRaw := fieldTarget) rfl).elim

/-- Codata observation with a neutral codata value is strongly
normalizing when the codata value is strongly normalizing.

The codata beta arms are impossible because every parallel reduct of
the neutral codata value stays neutral, and neutral terms are never
`codataUnfold`-shaped.  The congruence arm recurses on codata-value
progress. -/
theorem RawTerm.codataDest_neutral_isStronglyNormalizing {scope : Nat}
    {codataRaw : RawTerm scope}
    (codataIsNeutral : RawTerm.IsNeutral codataRaw)
    (codataIsSN : RawTerm.isStronglyNormalizing codataRaw) :
    RawTerm.isStronglyNormalizing (RawTerm.codataDest codataRaw) := by
  induction codataIsSN with
  | intro currentCodata _ codataInduction =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.codataDest currentCodata) ?_
    intro target progressStep
    rcases RawStep.par.codataDest_inv progressStep.1 with
      ⟨codataTarget, targetEq, codataStep⟩
      | ⟨stateTarget, transitionTarget, _targetEq, codataStep⟩
    · have codataTargetIsNeutral :
          RawTerm.IsNeutral codataTarget :=
        RawTerm.IsNeutral.par_preserves codataIsNeutral codataStep
      by_cases codataEq : currentCodata = codataTarget
      · subst codataEq
        subst targetEq
        exact (progressStep.2 rfl).elim
      · subst targetEq
        exact codataInduction codataTarget
          ⟨codataStep, codataEq⟩ codataTargetIsNeutral
    · exact (RawTerm.IsNeutral.not_codataUnfold
        (RawTerm.IsNeutral.par_preserves codataIsNeutral codataStep)
        (initialRaw := stateTarget) (transitionRaw := transitionTarget)
        rfl).elim

/-- Equivalence application with a neutral equivalence head is strongly
normalizing when both the equivalence head and argument are strongly
normalizing.

Unlike raw application, `equivApp` has no beta arm at the raw layer;
`RawStep.par.equivApp_inv` is congruence-only.  The proof therefore
recurses on head progress or argument progress, with the no-progress
case discharged by the strict progress witness. -/
theorem RawTerm.equivApp_neutral_isStronglyNormalizing {scope : Nat}
    {equivRaw argumentRaw : RawTerm scope}
    (equivIsNeutral : RawTerm.IsNeutral equivRaw)
    (equivIsSN : RawTerm.isStronglyNormalizing equivRaw)
    (argumentIsSN : RawTerm.isStronglyNormalizing argumentRaw) :
    RawTerm.isStronglyNormalizing
      (RawTerm.equivApp equivRaw argumentRaw) := by
  induction equivIsSN generalizing argumentRaw with
  | intro currentEquiv _ equivInduction =>
    induction argumentIsSN with
    | intro currentArgument argumentClosure argumentInduction =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.equivApp currentEquiv currentArgument) ?_
      intro target progressStep
      obtain ⟨equivTarget, argumentTarget, targetEq,
          equivStep, argumentStep⟩ :=
        RawStep.par.equivApp_inv progressStep.1
      subst targetEq
      have equivTargetIsNeutral :
          RawTerm.IsNeutral equivTarget :=
        RawTerm.IsNeutral.par_preserves equivIsNeutral equivStep
      have argumentTargetIsSN :
          RawTerm.isStronglyNormalizing argumentTarget := by
        by_cases argumentEq : currentArgument = argumentTarget
        · subst argumentEq
          exact RawTerm.isStronglyNormalizing.intro
            currentArgument argumentClosure
        · exact argumentClosure argumentTarget
            ⟨argumentStep, argumentEq⟩
      by_cases equivEq : currentEquiv = equivTarget
      · subst equivEq
        by_cases argumentEq : currentArgument = argumentTarget
        · subst argumentEq
          exact (progressStep.2 rfl).elim
        · exact argumentInduction argumentTarget
            ⟨argumentStep, argumentEq⟩
      · exact equivInduction equivTarget
          ⟨equivStep, equivEq⟩
          equivTargetIsNeutral
          argumentTargetIsSN

/-- **K12.20.AX.2 neutral equivApp SN preservation**.  Sister to
`pathApp_var`; var sits in the equiv-term slot, argument is the SN
witness.  `equivApp_inv` is cong-only (no β rule at raw layer yet),
so no nomatch defense needed — the cong arm alone preserves SN
via inductive hypothesis. -/
theorem RawTerm.equivApp_var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope)
    {argumentRaw : RawTerm scope}
    (argumentIsSN : RawTerm.isStronglyNormalizing argumentRaw) :
    RawTerm.isStronglyNormalizing
      (RawTerm.equivApp (RawTerm.var position) argumentRaw) := by
  induction argumentIsSN with
  | intro currentArgument _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.equivApp (RawTerm.var position) currentArgument) ?_
    intro target progressStep
    obtain ⟨equivTarget, argumentTarget, targetEq, equivStep, argumentStep⟩ :=
      RawStep.par.equivApp_inv progressStep.1
    have equivEq : equivTarget = RawTerm.var position :=
      (RawStep.par.var_inv equivStep)
    subst equivEq
    subst targetEq
    have argumentDistinct :
        currentArgument ≠ argumentTarget := fun argumentEq =>
      progressStep.2
        (congrArg (RawTerm.equivApp (RawTerm.var position)) argumentEq)
    exact inductiveHypothesis argumentTarget
      ⟨argumentStep, argumentDistinct⟩

/-- Equivalence application is strongly normalizing when both subterms are.

Unlike raw application, `equivApp` has no β arm at the raw layer; every
parallel reduct is a congruent reduct of the equivalence term and
argument. -/
theorem RawTerm.equivApp_isStronglyNormalizing {scope : Nat}
    {equivRaw argumentRaw : RawTerm scope}
    (equivIsSN : RawTerm.isStronglyNormalizing equivRaw)
    (argumentIsSN : RawTerm.isStronglyNormalizing argumentRaw) :
    RawTerm.isStronglyNormalizing
      (RawTerm.equivApp equivRaw argumentRaw) := by
  induction equivIsSN generalizing argumentRaw with
  | intro currentEquiv _ equivIH =>
    induction argumentIsSN with
    | intro currentArgument argumentClosure argumentIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.equivApp currentEquiv currentArgument) ?_
      intro target progressStep
      obtain ⟨equivTarget, argumentTarget, targetEq,
          equivStep, argumentStep⟩ :=
        RawStep.par.equivApp_inv progressStep.1
      subst targetEq
      have argumentTargetIsSN :
          RawTerm.isStronglyNormalizing argumentTarget := by
        by_cases argumentEq : currentArgument = argumentTarget
        · subst argumentEq
          exact RawTerm.isStronglyNormalizing.intro
            currentArgument argumentClosure
        · exact argumentClosure argumentTarget
            ⟨argumentStep, argumentEq⟩
      by_cases equivEq : currentEquiv = equivTarget
      · subst equivEq
        by_cases argumentEq : currentArgument = argumentTarget
        · subst argumentEq
          exact (progressStep.2 rfl).elim
        · exact argumentIH argumentTarget
            ⟨argumentStep, argumentEq⟩
      · exact equivIH equivTarget
          ⟨equivStep, equivEq⟩ argumentTargetIsSN

/-- Typed wrapper for congruence-only equivalence application SN. -/
theorem Term.equivApp_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierA carrierB : Ty level scope}
    {equivRaw argumentRaw : RawTerm scope}
    {equivTerm : Term context (Ty.equiv carrierA carrierB) equivRaw}
    {argumentTerm : Term context carrierA argumentRaw}
    (equivIsSN : Term.isStronglyNormalizing equivTerm)
    (argumentIsSN : Term.isStronglyNormalizing argumentTerm) :
    Term.isStronglyNormalizing
      (Term.equivApp equivTerm argumentTerm) :=
  RawTerm.equivApp_isStronglyNormalizing equivIsSN argumentIsSN

/-- Equivalence application is strongly normalizing when both subterms are.

`RawTerm.equivApply` is the univalence-target application form.  Its raw
parallel reduction is mostly binary congruence, with ua-refl beta arms that
return a reduct of the source argument.  Thus the proof is the same binary
SN induction as `hcomp`, except the beta arms discharge directly from the
argument SN witness. -/
theorem RawTerm.equivApply_isStronglyNormalizing {scope : Nat}
    {equivRaw argumentRaw : RawTerm scope}
    (equivIsSN : RawTerm.isStronglyNormalizing equivRaw)
    (argumentIsSN : RawTerm.isStronglyNormalizing argumentRaw) :
    RawTerm.isStronglyNormalizing
      (RawTerm.equivApply equivRaw argumentRaw) := by
  induction equivIsSN generalizing argumentRaw with
  | intro currentEquiv _ equivInduction =>
    induction argumentIsSN with
    | intro currentArgument argumentClosure argumentInduction =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.equivApply currentEquiv currentArgument) ?_
      intro target progressStep
      rcases RawStep.par.equivApply_inv progressStep.1 with
        ⟨equivTarget, argumentTarget, targetEq, equivStep, argumentStep⟩
        | ⟨_witnessSource, _witnessTarget, sourceTarget, _equivEq,
            targetEq, _witnessStep, argumentStep⟩
        | ⟨_witnessTarget, sourceTarget, targetEq, _equivStep,
            argumentStep⟩
      · subst targetEq
        have argumentTargetIsSN :
            RawTerm.isStronglyNormalizing argumentTarget := by
          by_cases argumentEq : currentArgument = argumentTarget
          · subst argumentEq
            exact RawTerm.isStronglyNormalizing.intro
              currentArgument argumentClosure
          · exact argumentClosure argumentTarget
              ⟨argumentStep, argumentEq⟩
        by_cases equivEq : currentEquiv = equivTarget
        · subst equivEq
          by_cases argumentEq : currentArgument = argumentTarget
          · subst argumentEq
            exact (progressStep.2 rfl).elim
          · exact argumentInduction argumentTarget
              ⟨argumentStep, argumentEq⟩
        · exact equivInduction equivTarget
            ⟨equivStep, equivEq⟩ argumentTargetIsSN
      · rw [targetEq]
        by_cases argumentEq : currentArgument = sourceTarget
        · rw [← argumentEq]
          exact RawTerm.isStronglyNormalizing.intro
            currentArgument argumentClosure
        · exact argumentClosure sourceTarget
            ⟨argumentStep, argumentEq⟩
      · rw [targetEq]
        by_cases argumentEq : currentArgument = sourceTarget
        · rw [← argumentEq]
          exact RawTerm.isStronglyNormalizing.intro
            currentArgument argumentClosure
        · exact argumentClosure sourceTarget
            ⟨argumentStep, argumentEq⟩

/-- Typed wrapper for `RawTerm.equivApply_isStronglyNormalizing`. -/
theorem Term.equivApply_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierA carrierB : Ty level scope}
    {equivRaw argumentRaw : RawTerm scope}
    {equivTerm : Term context (Ty.equiv carrierA carrierB) equivRaw}
    {argumentTerm : Term context carrierA argumentRaw}
    (equivIsSN : Term.isStronglyNormalizing equivTerm)
    (argumentIsSN : Term.isStronglyNormalizing argumentTerm) :
    Term.isStronglyNormalizing
      (Term.equivApply equivTerm argumentTerm) :=
  RawTerm.equivApply_isStronglyNormalizing equivIsSN argumentIsSN

/-- **K12.20.AX.3 neutral idJ SN preservation**.  HOTT J eliminator
with variable witness (the equality being eliminated).  `idJ_inv`
gives 2 arms (cong + iotaIdJRefl); ι arm requires
`witness → refl _`, defeated by `var_inv` + nomatch on
`var = refl _`.  Variable sits in the SECOND slot since
`Term.idJ baseCase witness` destructs `witness`. -/
theorem RawTerm.idJ_var_isStronglyNormalizing {scope : Nat}
    (position : Fin scope)
    {baseCaseRaw : RawTerm scope}
    (baseCaseIsSN : RawTerm.isStronglyNormalizing baseCaseRaw) :
    RawTerm.isStronglyNormalizing
      (RawTerm.idJ baseCaseRaw (RawTerm.var position)) := by
  induction baseCaseIsSN with
  | intro currentBase _ inductiveHypothesis =>
    refine RawTerm.isStronglyNormalizing.intro
      (RawTerm.idJ currentBase (RawTerm.var position)) ?_
    intro target progressStep
    rcases RawStep.par.idJ_inv progressStep.1 with
      ⟨baseTarget, witnessTarget, targetEq, baseStep, witnessStep⟩
      | ⟨witnessRaw, _baseTarget, _targetEq, witnessStep, _baseStep⟩
    · have witnessEq : witnessTarget = RawTerm.var position :=
        (RawStep.par.var_inv witnessStep)
      subst witnessEq
      subst targetEq
      have baseDistinct :
          currentBase ≠ baseTarget := fun baseEq =>
        progressStep.2
          (congrArg (fun base => RawTerm.idJ base (RawTerm.var position))
            baseEq)
      exact inductiveHypothesis baseTarget
        ⟨baseStep, baseDistinct⟩
    · exact (by
        have varEqRefl :
            RawTerm.var position = RawTerm.refl witnessRaw :=
          (RawStep.par.var_inv witnessStep).symm
        nomatch varEqRefl)

/-- Identity eliminator with a neutral witness is strongly normalizing
when the witness and base case are strongly normalizing.

The refl-ι arm is impossible because every parallel reduct of the
neutral witness stays neutral, and neutral terms are never `refl`
shaped.  The congruence arm recurses on witness progress or base-case
progress. -/
theorem RawTerm.idJ_neutral_isStronglyNormalizing {scope : Nat}
    {baseCaseRaw witnessRaw : RawTerm scope}
    (witnessIsNeutral : RawTerm.IsNeutral witnessRaw)
    (witnessIsSN : RawTerm.isStronglyNormalizing witnessRaw)
    (baseCaseIsSN : RawTerm.isStronglyNormalizing baseCaseRaw) :
    RawTerm.isStronglyNormalizing
      (RawTerm.idJ baseCaseRaw witnessRaw) := by
  induction witnessIsSN generalizing baseCaseRaw with
  | intro currentWitness _ witnessInduction =>
    induction baseCaseIsSN with
    | intro currentBase baseClosure baseInduction =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.idJ currentBase currentWitness) ?_
      intro target progressStep
      rcases RawStep.par.idJ_inv progressStep.1 with
        ⟨baseTarget, witnessTarget, targetEq,
          baseStep, witnessStep⟩
        | ⟨witnessReflRaw, _baseTarget, _targetEq,
            witnessStep, _baseStep⟩
      · subst targetEq
        have witnessTargetIsNeutral :
            RawTerm.IsNeutral witnessTarget :=
          RawTerm.IsNeutral.par_preserves witnessIsNeutral witnessStep
        have baseTargetIsSN :
            RawTerm.isStronglyNormalizing baseTarget := by
          by_cases baseEq : currentBase = baseTarget
          · subst baseEq
            exact RawTerm.isStronglyNormalizing.intro
              currentBase baseClosure
          · exact baseClosure baseTarget ⟨baseStep, baseEq⟩
        by_cases witnessEq : currentWitness = witnessTarget
        · subst witnessEq
          by_cases baseEq : currentBase = baseTarget
          · subst baseEq
            exact (progressStep.2 rfl).elim
          · exact baseInduction baseTarget ⟨baseStep, baseEq⟩
        · exact witnessInduction witnessTarget
            ⟨witnessStep, witnessEq⟩
            witnessTargetIsNeutral baseTargetIsSN
      · exact (RawTerm.IsNeutral.not_refl
          (RawTerm.IsNeutral.par_preserves witnessIsNeutral witnessStep)
          (witnessRaw := witnessReflRaw) rfl).elim


end LeanFX2
