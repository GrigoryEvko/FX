import FX1Poly.Core.RawTermFreeVars
import FX1Poly.Core.RawTermFoldNonVarCommute

/-! # FX1Poly/Core/RawTermOccurrenceRename — occurrence counting under renaming
    (the GRADE-0 lemma: a weakened term never uses the fresh position — OP1-INT brick 6 substrate)

`RawTerm.occurrenceCountAt` is the kernel's quantitative usage gate (the affine premise of the
graded bridge `pathIntro` row).  This file ships its first piece of RENAMING metatheory:

  * **`occurrenceCountAt_rename_avoided`** (mutual with the children version) — if a renaming
    never produces `avoidedPosition`, the renamed term has ZERO occurrences at
    `avoidedPosition`.  The induction threads the avoidance hypothesis through binder
    crossings: one `RawRenaming.lift` step avoids `Fin.succ avoidedPosition`
    (`liftAvoidsSucc`), and `iterateLiftRaw` under a `binderShift`-binder child avoids the
    `raiseParentPosition`-raised position (`iterateLiftRawAvoidsRaised`).
  * **`occurrenceCountAt_weaken_zeroPosition`** — ★ the GRADE-0 headline: `weaken t` uses the
    newest position ZERO times.  This is what discharges the graded `pathIntro` affine premise
    for EVERY dimension-constant bridge body (`occurrenceCountAt (weaken t) 0 = 0 ≤ 1`),
    turning the reflexivity-bridge construction fully symbolic.

## Zero-axiom

The mutual pair is structural over the term/children spine (the `freeVars_iff_uses` precedent
in `RawTermFreeVars`); the var case computes the fold's variable branch by `dif_pos rfl` and
refutes the singleton hit from the avoidance hypothesis (`if_neg`); the non-var case routes
through `rename_mkGen_of_ne_var` + `dif_neg`; the spine case converts the folded head back to
`rename` by the `rfl`-lemma `rename_eq_fold` and sums two zeros.  `Fin` equalities go through
`Fin.eq_of_val_eq` on definitionally-computed `val`s (`Fin.cast`/`Fin.natAdd`/`Fin.succ` are
`val`-transparent) — no `Fin.cases`/`Fin.casesOn` (the propext trap).  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Audit-gated in
`FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-- One binder lift preserves position avoidance: a renaming that never hits
`avoidedPosition` lifts to one that never hits `Fin.succ avoidedPosition` (position `0` maps
to `0 ≠ succ _`; raised positions reduce to the unlifted avoidance). -/
theorem RawRenaming.liftAvoidsSucc {sourceScope targetScope : Nat}
    {someRenaming : RawRenaming sourceScope targetScope} {avoidedPosition : Fin targetScope}
    (avoids : ∀ sourcePosition : Fin sourceScope,
      someRenaming sourcePosition ≠ avoidedPosition) :
    ∀ liftedPosition : Fin (sourceScope + 1),
      RawRenaming.lift someRenaming liftedPosition ≠ Fin.succ avoidedPosition := by
  intro liftedPosition
  cases liftedPosition with
  | mk positionValue positionBound =>
      cases positionValue with
      | zero =>
          intro absurdEq
          exact Nat.noConfusion (congrArg Fin.val absurdEq)
      | succ priorValue =>
          intro absurdEq
          have innerValEq :
              (someRenaming ⟨priorValue, Nat.lt_of_succ_lt_succ positionBound⟩).val
                = avoidedPosition.val :=
            Nat.succ.inj (congrArg Fin.val absurdEq)
          exact avoids ⟨priorValue, Nat.lt_of_succ_lt_succ positionBound⟩
            (Fin.eq_of_val_eq innerValEq)

/-- Raising through zero binders is the identity (the `val`s differ only by `Nat.zero_add`). -/
theorem RawVarSet.raiseParentPosition_zero {scope : Nat} (parentPosition : Fin scope) :
    RawVarSet.raiseParentPosition 0 parentPosition = parentPosition :=
  Fin.eq_of_val_eq (Nat.zero_add parentPosition.val)

/-- Raising through one more binder is `Fin.succ` of the prior raise (the `val`s differ only
by `Nat.succ_add`). -/
theorem RawVarSet.raiseParentPosition_succ {scope : Nat} (binderShift : Nat)
    (parentPosition : Fin scope) :
    RawVarSet.raiseParentPosition (binderShift + 1) parentPosition
      = Fin.succ (RawVarSet.raiseParentPosition binderShift parentPosition) :=
  Fin.eq_of_val_eq (Nat.succ_add binderShift parentPosition.val)

/-- Iterated binder lifting preserves avoidance at the raised position: the per-child
transport of the avoidance hypothesis through a `binderShift`-binder crossing. -/
theorem iterateLiftRawAvoidsRaised {sourceScope targetScope : Nat}
    {someRenaming : RawRenaming sourceScope targetScope} {avoidedPosition : Fin targetScope}
    (avoids : ∀ sourcePosition : Fin sourceScope,
      someRenaming sourcePosition ≠ avoidedPosition) :
    ∀ (binderShift : Nat) (liftedPosition : Fin (sourceScope + binderShift)),
      iterateLiftRaw someRenaming binderShift liftedPosition
        ≠ RawVarSet.raiseParentPosition binderShift avoidedPosition
  | 0, liftedPosition => by
      rw [RawVarSet.raiseParentPosition_zero]
      exact avoids liftedPosition
  | binderShift + 1, liftedPosition => by
      rw [RawVarSet.raiseParentPosition_succ]
      exact RawRenaming.liftAvoidsSucc
        (iterateLiftRawAvoidsRaised avoids binderShift) liftedPosition

mutual

/-- **Renaming under avoidance has zero occurrences.**  If `someRenaming` never produces
`avoidedPosition`, the renamed term does not use it — quantitatively. -/
theorem RawTerm.occurrenceCountAt_rename_avoided {sourceScope targetScope : Nat}
    (someRenaming : RawRenaming sourceScope targetScope)
    (sourceTerm : RawTerm sourceScope) (avoidedPosition : Fin targetScope)
    (avoids : ∀ sourcePosition : Fin sourceScope,
      someRenaming sourcePosition ≠ avoidedPosition) :
    RawTerm.occurrenceCountAt
      (RawTerm.rename someRenaming sourceTerm) avoidedPosition = 0 :=
  match sourceTerm with
  | .mkGen generator payload children => by
      by_cases generatorIsVar : generator = .gen_var
      · subst generatorIsVar
        show RawTerm.occurrenceCountAt
          (fold GenAlgebra.canonical someRenaming
            (.mkGen .gen_var payload children)) avoidedPosition = 0
        dsimp only [fold]
        rw [dif_pos rfl]
        show RawTerm.occurrenceCountAt
          (.mkGen .gen_var (someRenaming payload) .childNil) avoidedPosition = 0
        dsimp only [RawTerm.occurrenceCountAt]
        rw [dif_pos rfl]
        have missesSingleton :
            ¬ (RawVarSet.singleton (someRenaming payload) avoidedPosition = true) := by
          intro singletonHit
          exact avoids payload
            ((RawVarSet.contains_singleton_iff
              (someRenaming payload) avoidedPosition).mp singletonHit).symm
        show (if RawVarSet.singleton (someRenaming payload) avoidedPosition = true
          then 1 else 0) = 0
        rw [if_neg missesSingleton]
      · rw [RawTerm.rename_mkGen_of_ne_var someRenaming generatorIsVar payload children]
        dsimp only [RawTerm.occurrenceCountAt]
        rw [dif_neg generatorIsVar]
        exact RawTermChildren.occurrenceCountAt_rename_avoided
          someRenaming children avoidedPosition avoids

/-- Children-spine version: each child's head is counted at the raised position under the
lifted renaming, where avoidance transports by `iterateLiftRawAvoidsRaised`. -/
theorem RawTermChildren.occurrenceCountAt_rename_avoided {sourceScope targetScope : Nat}
    {binderShifts : List Nat}
    (someRenaming : RawRenaming sourceScope targetScope)
    (sourceChildren : RawTermChildren binderShifts sourceScope)
    (avoidedPosition : Fin targetScope)
    (avoids : ∀ sourcePosition : Fin sourceScope,
      someRenaming sourcePosition ≠ avoidedPosition) :
    RawTermChildren.occurrenceCountAt
      (RawTermChildren.rename someRenaming sourceChildren) avoidedPosition = 0 :=
  match binderShifts, sourceChildren with
  | [], .childNil => rfl
  | binderShift :: _restShifts, .childCons childHead childTail => by
      show RawTerm.occurrenceCountAt
          (fold GenAlgebra.canonical
            (iterateLiftRaw someRenaming binderShift) childHead)
          (RawVarSet.raiseParentPosition binderShift avoidedPosition) +
        RawTermChildren.occurrenceCountAt
          (foldChildren GenAlgebra.canonical someRenaming childTail)
          avoidedPosition = 0
      rw [← RawTerm.rename_eq_fold, ← RawTermChildren.rename_eq_foldChildren]
      rw [RawTerm.occurrenceCountAt_rename_avoided
            (iterateLiftRaw someRenaming binderShift) childHead
            (RawVarSet.raiseParentPosition binderShift avoidedPosition)
            (iterateLiftRawAvoidsRaised avoids binderShift),
          RawTermChildren.occurrenceCountAt_rename_avoided
            someRenaming childTail avoidedPosition avoids]

end

/-- **★ The GRADE-0 headline: a weakened term never uses the newest position.**  The
quantitative content of weakening — `weaken t` is dimension-constant at position `0` — which
discharges the graded `pathIntro` affine premise (`0 ≤ 1`) for EVERY constant bridge body. -/
theorem RawTerm.occurrenceCountAt_weaken_zeroPosition {scope : Nat}
    (sourceTerm : RawTerm scope) :
    RawTerm.occurrenceCountAt (RawTerm.weaken sourceTerm) ⟨0, Nat.succ_pos scope⟩ = 0 := by
  rw [RawTerm.weaken_eq_rename]
  exact RawTerm.occurrenceCountAt_rename_avoided RawRenaming.weaken sourceTerm
    ⟨0, Nat.succ_pos scope⟩
    (fun sourcePosition absurdEq => Nat.noConfusion (congrArg Fin.val absurdEq))

end FX1Poly.Core
