import FX1Poly.Core.RawTermOccurrenceSubst
import FX1Poly.Typed.GradedIntroPremiseSpike

/-! # FX1Poly/Typed/GradedBetaSubjectReductionGhost — NATIVE-22: graded β-SR respects the usage bound (ghost)

NATIVE-20 made the introduction table carry a per-binder usage grade and the dispatcher demand
`gradedBinderChecks rule.binderUsage body`; NATIVE-21 shipped the quantitative-substitution metatheory
(the `weaken_succ` de Bruijn shift primitive + the ghost subst lemmas).  This file lands graded subject
reduction for the GHOST grade, table-generically: when a `.zero`-graded introduction β-reduces, the
argument is ERASED — the reduct uses it zero times, exactly the usage bound the `.zero` grade demands.

The `.zero` graded check is `gradedBinderChecks .zero body = (occurrenceCountAt body 0 = 0)` — the binder
is used zero times.  The genuine content is connecting that binder-occurrence fact to the SUBSTITUTION:
when `body` does not use the binder, `subst0 body arg` is independent of `arg` and its occurrence profile
is `body`'s shifted down.

  * **`RawTerm.strengthen_eq_some_of_occurrenceZero`** — ★ the new bridge: `occurrenceCountAt body 0 = 0`
    implies `body` STRENGTHENS (`strengthen body = some _`).  Via a generic
    `partialRenameSucceeds_of_occurrenceZero` mutual induction: a partial renaming that fails only at the
    dropped position succeeds on a body that does not use that position (the occurrence count there is
    `0`), transported through binders by `iterateLiftRawFailsOnlyAtRaised`.
  * **`RawTerm.occurrenceCountAt_subst0_ghost`** — ★ the ghost β-SR equation: `occurrenceCountAt body 0 =
    0` implies `occurrenceCountAt (subst0 body arg) p = occurrenceCountAt body p.succ` for every position
    `p` and every argument `arg` — the reduct counts `body` shifted down, with ZERO contribution from
    `arg`.  Chains the bridge with NATIVE-21's `subst0_of_strengthens`, `strengthen_sound`, `weaken_succ`.
  * **`gradedGhostBetaErasesArgument`** — the table-generic graded SR: a graded introduction whose binder
    grade forces `gradedBinderChecks .zero body` β-reduces with the argument's contribution erased — the
    `.zero` usage bound is respected.  Generic over the future `.zero` row (pathLam-ghost, NATIVE-23).
  * **`gradedGhostBetaErasesArgument_weakenWitness`** — non-vacuous: the canonical ghost body
    `weaken sourceTerm` (NATIVE-03) reduces with its argument erased, agreeing with NATIVE-21's
    `subst0_weaken`.

The AFFINE (`.one`) / general case needs the full master substitution equation `occ (subst0 body arg) p =
occ body p.succ + occ body 0 * occ arg p` (NATIVE-21's deferred half), built on the same `weaken_succ`
shift primitive; that is the remaining graded-SR work.

## Zero-axiom

The bridge induction mirrors the shipped `partialRenameResult_rename_some` family (structural over the
term/children spine; the var case cases on the singleton Bool value — propext-clean; `Nat`-add-zero split
by `cases` on the recursion argument + `Nat.noConfusion`).  The ghost equation and the graded bundle are
`rw`/`Eq.trans` of the shipped lemmas.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Core

open FX1Poly.Foundation

universe u v

/-- Propext-clean `Nat`-add-zero split (the iff `Nat.add_eq_zero` leaks propext/Classical/Quot.sound). -/
private theorem natAddZeroSplit {leftSummand rightSummand : Nat}
    (sumIsZero : leftSummand + rightSummand = 0) :
    leftSummand = 0 ∧ rightSummand = 0 := by
  cases rightSummand with
  | zero => exact ⟨sumIsZero, rfl⟩
  | succ priorRight => exact Nat.noConfusion sumIsZero

/-- Propext-clean `some ≠ none` eliminator: maps the impossible equation through `Option.isSome` to a
`Bool` constructor clash (`Option.noConfusion` itself misfires on a universe metavariable here). -/
private def someEqNoneElim {valueType : Type u} {motiveType : Sort v} {value : valueType}
    (isContradiction : some value = none) : motiveType :=
  Bool.noConfusion (congrArg Option.isSome isContradiction)

/-- One binder lift preserves the "fails only at the dropped position" condition: a partial renaming that
returns `none` only at `dropPosition` lifts to one that returns `none` only at `Fin.succ dropPosition`
(position `0` is the fresh bound variable, always `some`). -/
theorem PartialRawRenaming.liftFailsOnlyAtSucc {sourceScope targetScope : Nat}
    {partialRenaming : PartialRawRenaming sourceScope targetScope}
    {dropPosition : Fin sourceScope}
    (failsOnly : ∀ candidatePosition : Fin sourceScope,
      partialRenaming candidatePosition = none → candidatePosition = dropPosition) :
    ∀ liftedPosition : Fin (sourceScope + 1),
      PartialRawRenaming.lift partialRenaming liftedPosition = none
        → liftedPosition = Fin.succ dropPosition := by
  intro liftedPosition liftIsNone
  cases liftedPosition with
  | mk positionValue positionBound =>
      cases positionValue with
      | zero =>
          exact someEqNoneElim
            ((rfl : PartialRawRenaming.lift partialRenaming ⟨0, positionBound⟩
                = some ⟨0, Nat.zero_lt_succ targetScope⟩).symm.trans liftIsNone)
      | succ priorValue =>
          have priorBound : priorValue < sourceScope := Nat.lt_of_succ_lt_succ positionBound
          cases hInner : partialRenaming ⟨priorValue, priorBound⟩ with
          | some targetPosition =>
              have liftIsSome :
                  PartialRawRenaming.lift partialRenaming ⟨priorValue + 1, positionBound⟩
                    = some (Fin.succ targetPosition) := by
                show (match partialRenaming ⟨priorValue, priorBound⟩ with
                      | some tp => some (Fin.succ tp)
                      | none => none) = some (Fin.succ targetPosition)
                rw [hInner]
              exact someEqNoneElim (liftIsSome.symm.trans liftIsNone)
          | none =>
              have priorIsDrop :
                  (⟨priorValue, priorBound⟩ : Fin sourceScope) = dropPosition :=
                failsOnly ⟨priorValue, priorBound⟩ hInner
              exact Fin.eq_of_val_eq
                (congrArg (· + 1) (congrArg Fin.val priorIsDrop))

/-- Iterated binder lifting preserves the "fails only at the raised dropped position" condition. -/
theorem iterateLiftRawFailsOnlyAtRaised {sourceScope targetScope : Nat}
    {partialRenaming : PartialRawRenaming sourceScope targetScope}
    {dropPosition : Fin sourceScope}
    (failsOnly : ∀ candidatePosition : Fin sourceScope,
      partialRenaming candidatePosition = none → candidatePosition = dropPosition) :
    ∀ (binderShift : Nat) (liftedPosition : Fin (sourceScope + binderShift)),
      iterateLiftRaw partialRenaming binderShift liftedPosition = none
        → liftedPosition = RawVarSet.raiseParentPosition binderShift dropPosition
  | 0, liftedPosition => by
      rw [RawVarSet.raiseParentPosition_zero]
      exact failsOnly liftedPosition
  | binderShift + 1, liftedPosition => by
      rw [RawVarSet.raiseParentPosition_succ]
      exact PartialRawRenaming.liftFailsOnlyAtSucc
        (iterateLiftRawFailsOnlyAtRaised failsOnly binderShift) liftedPosition

mutual

/-- **A body that does not use the dropped position survives a fails-only-there partial renaming.**  If
`partialRenaming` returns `none` only at `dropPosition`, and `body` has zero occurrences of
`dropPosition`, then the partial-rename result succeeds.  The generic engine behind the strengthening
bridge. -/
theorem RawTerm.partialRenameSucceeds_of_occurrenceZero {sourceScope targetScope : Nat}
    (partialRenaming : PartialRawRenaming sourceScope targetScope)
    (dropPosition : Fin sourceScope)
    (failsOnly : ∀ candidatePosition : Fin sourceScope,
      partialRenaming candidatePosition = none → candidatePosition = dropPosition)
    (body : RawTerm sourceScope)
    (unused : RawTerm.occurrenceCountAt body dropPosition = 0) :
    (RawTerm.partialRenameResult partialRenaming body).hasSucceeded = true :=
  match body with
  | .mkGen generator payload children => by
      by_cases generatorIsVar : generator = .gen_var
      · subst generatorIsVar
        cases children
        have payloadNeDrop : payload ≠ dropPosition := by
          intro payloadEqDrop
          have countIsOne :
              RawTerm.occurrenceCountAt
                (.mkGen .gen_var payload .childNil) dropPosition = 1 := by
            rw [← payloadEqDrop]
            exact RawTerm.occurrenceCountAt_var_self payload
          rw [countIsOne] at unused
          exact Nat.noConfusion unused
        show (RawTerm.partialRenameResult partialRenaming
          (.mkGen .gen_var payload .childNil)).hasSucceeded = true
        dsimp only [RawTerm.partialRenameResult]
        rw [dif_pos rfl]
        cases hPartial : partialRenaming payload with
        | none => exact absurd (failsOnly payload hPartial) payloadNeDrop
        | some targetPosition => rfl
      · show (RawTerm.partialRenameResult partialRenaming
          (.mkGen generator payload children)).hasSucceeded = true
        dsimp only [RawTerm.partialRenameResult]
        rw [dif_neg generatorIsVar]
        have childrenUnused :
            RawTermChildren.occurrenceCountAt children dropPosition = 0 := by
          have unfolded :
              RawTerm.occurrenceCountAt (.mkGen generator payload children) dropPosition
                = RawTermChildren.occurrenceCountAt children dropPosition := by
            dsimp only [RawTerm.occurrenceCountAt]
            rw [dif_neg generatorIsVar]
          rw [← unfolded]; exact unused
        exact RawTermChildren.partialRenameSucceeds_of_occurrenceZero
          partialRenaming dropPosition failsOnly children childrenUnused

/-- Children-spine version of `RawTerm.partialRenameSucceeds_of_occurrenceZero`. -/
theorem RawTermChildren.partialRenameSucceeds_of_occurrenceZero {sourceScope targetScope : Nat}
    {binderShifts : List Nat}
    (partialRenaming : PartialRawRenaming sourceScope targetScope)
    (dropPosition : Fin sourceScope)
    (failsOnly : ∀ candidatePosition : Fin sourceScope,
      partialRenaming candidatePosition = none → candidatePosition = dropPosition)
    (children : RawTermChildren binderShifts sourceScope)
    (unused : RawTermChildren.occurrenceCountAt children dropPosition = 0) :
    (RawTermChildren.partialRenameResult partialRenaming children).hasSucceeded = true :=
  match binderShifts, children with
  | [], .childNil => rfl
  | binderShift :: _restShifts, .childCons childHead childTail => by
      have splitUnused :
          RawTerm.occurrenceCountAt childHead
              (RawVarSet.raiseParentPosition binderShift dropPosition) = 0 ∧
          RawTermChildren.occurrenceCountAt childTail dropPosition = 0 :=
        natAddZeroSplit unused
      show ((RawTerm.partialRenameResult
              (iterateLiftRaw partialRenaming binderShift) childHead).hasSucceeded &&
            (RawTermChildren.partialRenameResult partialRenaming childTail).hasSucceeded) = true
      rw [RawTerm.partialRenameSucceeds_of_occurrenceZero
            (iterateLiftRaw partialRenaming binderShift)
            (RawVarSet.raiseParentPosition binderShift dropPosition)
            (iterateLiftRawFailsOnlyAtRaised failsOnly binderShift)
            childHead splitUnused.left,
          RawTermChildren.partialRenameSucceeds_of_occurrenceZero
            partialRenaming dropPosition failsOnly childTail splitUnused.right]
      rfl

end

/-- **★ The strengthening bridge.**  A `body` that does not use the newest variable
(`occurrenceCountAt body 0 = 0`) STRENGTHENS — `strengthen body = some extracted` for some `extracted`.
The `dropNewest` partial renaming fails only at position `0`, which `body` does not use. -/
theorem RawTerm.strengthen_eq_some_of_occurrenceZero {scope : Nat}
    (body : RawTerm (scope + 1))
    (unused : RawTerm.occurrenceCountAt body ⟨0, Nat.succ_pos scope⟩ = 0) :
    ∃ extracted : RawTerm scope, RawTerm.strengthen body = some extracted := by
  have succeeded :
      (RawTerm.partialRenameResult PartialRawRenaming.dropNewest body).hasSucceeded = true :=
    RawTerm.partialRenameSucceeds_of_occurrenceZero PartialRawRenaming.dropNewest
      ⟨0, Nat.succ_pos scope⟩
      (fun candidatePosition dropIsNone => by
        cases candidatePosition with
        | mk positionValue positionBound =>
            cases positionValue with
            | zero => exact Fin.eq_of_val_eq rfl
            | succ priorValue =>
                exact someEqNoneElim
                  ((rfl : PartialRawRenaming.dropNewest ⟨priorValue + 1, positionBound⟩
                      = some ⟨priorValue, Nat.lt_of_succ_lt_succ positionBound⟩).symm.trans
                    dropIsNone))
      body unused
  refine ⟨(RawTerm.partialRenameResult PartialRawRenaming.dropNewest body).term, ?_⟩
  dsimp only [RawTerm.strengthen, RawTerm.partialRename?, PartialRenameTermResult.toOption]
  rw [succeeded]
  rfl

/-- **★ Ghost β subject reduction (quantitative).**  When `body` does not use the substituted binder
(`occurrenceCountAt body 0 = 0`, the `.zero` graded check), `subst0 body arg` counts at every position
exactly what `body` counts one position up — the argument is ERASED, contributing ZERO occurrences.
Chains the strengthening bridge with NATIVE-21's `subst0_of_strengthens` / `strengthen_sound` /
`weaken_succ`. -/
theorem RawTerm.occurrenceCountAt_subst0_ghost {scope : Nat}
    (body : RawTerm (scope + 1)) (rawArg : RawTerm scope)
    (unused : RawTerm.occurrenceCountAt body ⟨0, Nat.succ_pos scope⟩ = 0)
    (position : Fin scope) :
    RawTerm.occurrenceCountAt (RawTerm.subst0 body rawArg) position
      = RawTerm.occurrenceCountAt body (Fin.succ position) := by
  obtain ⟨extracted, strengthens⟩ := RawTerm.strengthen_eq_some_of_occurrenceZero body unused
  have weakenedBody : RawTerm.weaken extracted = body :=
    RawTerm.strengthen_sound body extracted strengthens
  rw [RawTerm.occurrenceCountAt_subst0_of_strengthens body extracted rawArg strengthens,
    ← weakenedBody, RawTerm.occurrenceCountAt_weaken_succ]

end FX1Poly.Core

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Modal

/-- **★ Table-generic graded ghost β subject reduction.**  An introduction body that passes the GHOST
graded check (`gradedBinderChecks .zero body`, i.e. the binder is used zero times) β-reduces with its
argument ERASED: `subst0 body arg` counts at every position exactly what `body` counts one up, ZERO
contribution from `arg`.  This is graded SR for the `.zero` grade — the reduct respects the usage bound
(the argument is used zero times).  Generic over the future `.zero` introduction row (NATIVE-23 ghost
pathLam). -/
theorem gradedGhostBetaErasesArgument {scope : Nat}
    (body : RawTerm (scope + 1)) (rawArg : RawTerm scope)
    (ghostChecked : gradedBinderChecks UsageGrade.zero body)
    (position : Fin scope) :
    RawTerm.occurrenceCountAt (RawTerm.subst0 body rawArg) position
      = RawTerm.occurrenceCountAt body (Fin.succ position) :=
  -- `gradedBinderChecks .zero body` is definitionally `occurrenceCountAt body 0 = 0`.
  RawTerm.occurrenceCountAt_subst0_ghost body rawArg ghostChecked position

/-- **★ Non-vacuous witness.**  The canonical ghost body `weaken sourceTerm` (NATIVE-03's
`gradedIntro_ghost_ofWeakened`) reduces with its argument erased: `subst0 (weaken sourceTerm) arg`
counts exactly what `sourceTerm` counts — agreeing with NATIVE-21's `subst0_weaken`, now derived through
the GENERAL ghost β-SR (not the syntactic-weaken shortcut). -/
theorem gradedGhostBetaErasesArgument_weakenWitness {scope : Nat}
    (sourceTerm : RawTerm scope) (rawArg : RawTerm scope) (position : Fin scope) :
    RawTerm.occurrenceCountAt
        (RawTerm.subst0 (RawTerm.weaken sourceTerm) rawArg) position
      = RawTerm.occurrenceCountAt sourceTerm position := by
  rw [gradedGhostBetaErasesArgument (RawTerm.weaken sourceTerm) rawArg
        (RawTerm.occurrenceCountAt_weaken_zeroPosition sourceTerm) position,
    RawTerm.occurrenceCountAt_weaken_succ]

end FX1Poly.Typed
