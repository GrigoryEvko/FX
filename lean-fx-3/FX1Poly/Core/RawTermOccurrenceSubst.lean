import FX1Poly.Core.RawTermOccurrenceRename
import FX1Poly.Core.RawTermStrengthen

/-! # FX1Poly/Core/RawTermOccurrenceSubst — quantitative substitution (occurrenceCountAt of subst0)

NATIVE-21.  `RawTerm.occurrenceCountAt` is the kernel's quantitative usage gate (the affine premise of
the graded intro layer, NATIVE-20).  Graded subject reduction (NATIVE-22) fires β
`(λ.body) arg ↝ subst0 body arg` and must know how the binder's usage grade bounds the substituted
argument's occurrences.  This file ships the quantitative-substitution metatheory:

  * **`occurrenceCountAt_rename_image`** (mutual with the children version) — the EXACT-HIT companion
    of the shipped MISS lemma `occurrenceCountAt_rename_avoided`: when a renaming hits `targetPosition`
    EXACTLY at `sourcePosition`, the renamed term has the SAME occurrence count at `targetPosition` that
    the source has at `sourcePosition`.  The genuinely-new induction; transports the exact-hit
    hypothesis through binder crossings (`liftHitsSucc` / `iterateLiftRawHitsRaised`).
  * **`occurrenceCountAt_weaken_succ`** — ★ the shift primitive: `weaken t` (= `rename Fin.succ`) at the
    raised position `Fin.succ r` counts exactly what `t` counts at `r`.  With the shipped
    `occurrenceCountAt_weaken_zeroPosition` (count `0` at the freshest position) this FULLY characterizes
    occurrences under weakening — the de Bruijn shift the master substitution equation needs.
  * **`occurrenceCountAt_subst0_weaken`** — ★ the GHOST quantitative substitution lemma:
    `subst0 (weaken body) arg` has the SAME occurrence count at every position as `body` — a
    dimension-constant (ghost, `.zero`-graded) body uses the binder zero times, so `arg` contributes
    NOTHING.  Closed-form, via the shipped `weaken_subst_singleton` (`subst0 (weaken b) arg = b`).
  * **`occurrenceCountAt_subst0_of_strengthens`** — the general ghost case: any body that STRENGTHENS
    (does not use the binder) erases `arg` under `subst0`, so its occurrence counts are the
    strengthened body's — via the shipped `strengthen_commutes_subst0`.
  * **`occurrenceCountAt_subst0_weaken_self`** — non-vacuous witness: `subst0 (weaken (var 0)) arg` still
    counts `var 0` exactly once.

The remaining master equation `occ (subst0 body arg) p = occ body p.succ + occ body 0 * occ arg p`
(the AFFINE/general arg-multiplicity half) is the NATIVE-22 prerequisite built on the `weaken_succ`
shift primitive landed here.

## Zero-axiom

The image induction mirrors the shipped `occurrenceCountAt_rename_avoided` (structural over the
term/children spine; the var case routes the singleton through `RawVarSet.contains_singleton_iff` and
`if_pos`/`if_neg`; `Fin` equalities go through `Fin.eq_of_val_eq` on definitionally-computed `val`s — no
`Fin.cases` propext trap).  The corollaries are `rw` of the shipped subst/strengthen identities.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Audit-gated in
`FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-- One binder lift transports an EXACT-HIT hypothesis: a renaming that hits `targetPosition` exactly
at `sourcePosition` lifts to one that hits `Fin.succ targetPosition` exactly at `Fin.succ sourcePosition`
(position `0` is the fresh bound variable, hitting neither succ). -/
theorem RawRenaming.liftHitsSucc {sourceScope targetScope : Nat}
    {someRenaming : RawRenaming sourceScope targetScope}
    {sourcePosition : Fin sourceScope} {targetPosition : Fin targetScope}
    (hits : ∀ candidatePosition : Fin sourceScope,
      someRenaming candidatePosition = targetPosition ↔ candidatePosition = sourcePosition) :
    ∀ liftedPosition : Fin (sourceScope + 1),
      RawRenaming.lift someRenaming liftedPosition = Fin.succ targetPosition
        ↔ liftedPosition = Fin.succ sourcePosition := by
  intro liftedPosition
  cases liftedPosition with
  | mk positionValue positionBound =>
      cases positionValue with
      | zero =>
          constructor
          · intro hitsSucc
            exact Nat.noConfusion (congrArg Fin.val hitsSucc)
          · intro isSucc
            exact Nat.noConfusion (congrArg Fin.val isSucc)
      | succ priorValue =>
          have priorBound : priorValue < sourceScope := Nat.lt_of_succ_lt_succ positionBound
          constructor
          · intro hitsSucc
            have innerHit :
                (someRenaming ⟨priorValue, priorBound⟩).val = targetPosition.val :=
              Nat.succ.inj (congrArg Fin.val hitsSucc)
            have priorIsSource :
                (⟨priorValue, priorBound⟩ : Fin sourceScope) = sourcePosition :=
              (hits ⟨priorValue, priorBound⟩).mp (Fin.eq_of_val_eq innerHit)
            exact Fin.eq_of_val_eq
              (congrArg (· + 1) (congrArg Fin.val priorIsSource))
          · intro isSucc
            have priorIsSource :
                (⟨priorValue, priorBound⟩ : Fin sourceScope) = sourcePosition :=
              Fin.eq_of_val_eq (Nat.succ.inj (congrArg Fin.val isSucc))
            have rawHit :
                someRenaming ⟨priorValue, priorBound⟩ = targetPosition :=
              (hits ⟨priorValue, priorBound⟩).mpr priorIsSource
            exact Fin.eq_of_val_eq
              (congrArg (· + 1) (congrArg Fin.val rawHit))

/-- Iterated binder lifting transports the exact-hit hypothesis to the raised positions: the per-child
analogue of `iterateLiftRawAvoidsRaised`. -/
theorem iterateLiftRawHitsRaised {sourceScope targetScope : Nat}
    {someRenaming : RawRenaming sourceScope targetScope}
    {sourcePosition : Fin sourceScope} {targetPosition : Fin targetScope}
    (hits : ∀ candidatePosition : Fin sourceScope,
      someRenaming candidatePosition = targetPosition ↔ candidatePosition = sourcePosition) :
    ∀ (binderShift : Nat) (liftedPosition : Fin (sourceScope + binderShift)),
      iterateLiftRaw someRenaming binderShift liftedPosition
          = RawVarSet.raiseParentPosition binderShift targetPosition
        ↔ liftedPosition = RawVarSet.raiseParentPosition binderShift sourcePosition
  | 0, liftedPosition => by
      rw [RawVarSet.raiseParentPosition_zero, RawVarSet.raiseParentPosition_zero]
      exact hits liftedPosition
  | binderShift + 1, liftedPosition => by
      rw [RawVarSet.raiseParentPosition_succ, RawVarSet.raiseParentPosition_succ]
      exact RawRenaming.liftHitsSucc
        (iterateLiftRawHitsRaised hits binderShift) liftedPosition

mutual

/-- **Renaming under an exact hit preserves the occurrence count.**  If `someRenaming` hits
`targetPosition` EXACTLY at `sourcePosition` (`= ↔ =`), then the renamed term's count at
`targetPosition` equals the source term's count at `sourcePosition`.  The exact-hit companion of
`occurrenceCountAt_rename_avoided`. -/
theorem RawTerm.occurrenceCountAt_rename_image {sourceScope targetScope : Nat}
    (someRenaming : RawRenaming sourceScope targetScope)
    (sourceTerm : RawTerm sourceScope)
    (sourcePosition : Fin sourceScope) (targetPosition : Fin targetScope)
    (hits : ∀ candidatePosition : Fin sourceScope,
      someRenaming candidatePosition = targetPosition ↔ candidatePosition = sourcePosition) :
    RawTerm.occurrenceCountAt (RawTerm.rename someRenaming sourceTerm) targetPosition
      = RawTerm.occurrenceCountAt sourceTerm sourcePosition :=
  match sourceTerm with
  | .mkGen generator payload children => by
      by_cases generatorIsVar : generator = .gen_var
      · subst generatorIsVar
        show RawTerm.occurrenceCountAt
          (fold GenAlgebra.canonical someRenaming
            (.mkGen .gen_var payload children)) targetPosition
          = RawTerm.occurrenceCountAt (.mkGen .gen_var payload children) sourcePosition
        dsimp only [fold]
        rw [dif_pos rfl]
        show RawTerm.occurrenceCountAt
          (.mkGen .gen_var (someRenaming payload) .childNil) targetPosition
          = RawTerm.occurrenceCountAt (.mkGen .gen_var payload .childNil) sourcePosition
        dsimp only [RawTerm.occurrenceCountAt]
        rw [dif_pos rfl, dif_pos rfl]
        show (if RawVarSet.singleton (someRenaming payload) targetPosition = true then 1 else 0)
          = (if RawVarSet.singleton payload sourcePosition = true then 1 else 0)
        -- Show the two singleton membership booleans AGREE, then the `if`s coincide.  Casing on the
        -- BOOL value (`cases h : …`) is propext-clean, avoiding a `by_cases` on the equality (whose
        -- syntactic type `Generator.gen_var.payload …` fails DecidableEq search → Classical leak).
        have singletonsAgree :
            RawVarSet.singleton (someRenaming payload) targetPosition
              = RawVarSet.singleton payload sourcePosition := by
          cases hsource : RawVarSet.singleton payload sourcePosition with
          | true =>
              exact (RawVarSet.contains_singleton_iff (someRenaming payload) targetPosition).mpr
                ((hits payload).mpr
                  ((RawVarSet.contains_singleton_iff payload sourcePosition).mp hsource).symm).symm
          | false =>
              cases htarget : RawVarSet.singleton (someRenaming payload) targetPosition with
              | false => rfl
              | true =>
                  have sourceHits :
                      RawVarSet.singleton payload sourcePosition = true :=
                    (RawVarSet.contains_singleton_iff payload sourcePosition).mpr
                      ((hits payload).mp
                        ((RawVarSet.contains_singleton_iff
                          (someRenaming payload) targetPosition).mp htarget).symm).symm
                  exact Bool.noConfusion (hsource ▸ sourceHits)
        rw [singletonsAgree]
      · rw [RawTerm.rename_mkGen_of_ne_var someRenaming generatorIsVar payload children]
        dsimp only [RawTerm.occurrenceCountAt]
        rw [dif_neg generatorIsVar, dif_neg generatorIsVar]
        exact RawTermChildren.occurrenceCountAt_rename_image
          someRenaming children sourcePosition targetPosition hits

/-- Children-spine version of `RawTerm.occurrenceCountAt_rename_image`. -/
theorem RawTermChildren.occurrenceCountAt_rename_image {sourceScope targetScope : Nat}
    {binderShifts : List Nat}
    (someRenaming : RawRenaming sourceScope targetScope)
    (sourceChildren : RawTermChildren binderShifts sourceScope)
    (sourcePosition : Fin sourceScope) (targetPosition : Fin targetScope)
    (hits : ∀ candidatePosition : Fin sourceScope,
      someRenaming candidatePosition = targetPosition ↔ candidatePosition = sourcePosition) :
    RawTermChildren.occurrenceCountAt
        (RawTermChildren.rename someRenaming sourceChildren) targetPosition
      = RawTermChildren.occurrenceCountAt sourceChildren sourcePosition :=
  match binderShifts, sourceChildren with
  | [], .childNil => rfl
  | binderShift :: _restShifts, .childCons childHead childTail => by
      show RawTerm.occurrenceCountAt
          (fold GenAlgebra.canonical
            (iterateLiftRaw someRenaming binderShift) childHead)
          (RawVarSet.raiseParentPosition binderShift targetPosition) +
        RawTermChildren.occurrenceCountAt
          (foldChildren GenAlgebra.canonical someRenaming childTail)
          targetPosition
        = RawTerm.occurrenceCountAt childHead
            (RawVarSet.raiseParentPosition binderShift sourcePosition) +
          RawTermChildren.occurrenceCountAt childTail sourcePosition
      rw [← RawTerm.rename_eq_fold, ← RawTermChildren.rename_eq_foldChildren]
      rw [RawTerm.occurrenceCountAt_rename_image
            (iterateLiftRaw someRenaming binderShift) childHead
            (RawVarSet.raiseParentPosition binderShift sourcePosition)
            (RawVarSet.raiseParentPosition binderShift targetPosition)
            (iterateLiftRawHitsRaised hits binderShift),
          RawTermChildren.occurrenceCountAt_rename_image
            someRenaming childTail sourcePosition targetPosition hits]

end

/-- **★ The weakening shift primitive.**  `weaken t` (= `rename Fin.succ`) counts at the raised position
`Fin.succ r` exactly what `t` counts at `r`.  The de Bruijn shift the master substitution equation
needs; together with the shipped `occurrenceCountAt_weaken_zeroPosition` (count `0` at the freshest
position) it fully characterizes occurrences under weakening. -/
theorem RawTerm.occurrenceCountAt_weaken_succ {scope : Nat}
    (sourceTerm : RawTerm scope) (position : Fin scope) :
    RawTerm.occurrenceCountAt (RawTerm.weaken sourceTerm) (Fin.succ position)
      = RawTerm.occurrenceCountAt sourceTerm position := by
  rw [RawTerm.weaken_eq_rename]
  exact RawTerm.occurrenceCountAt_rename_image RawRenaming.weaken sourceTerm
    position (Fin.succ position)
    (fun candidatePosition => by
      constructor
      · intro weakenHit
        exact Fin.eq_of_val_eq (Nat.succ.inj (congrArg Fin.val weakenHit))
      · intro isSource
        exact Fin.eq_of_val_eq (congrArg (· + 1) (congrArg Fin.val isSource)))

/-- **★ The GHOST quantitative substitution lemma.**  Substituting into a WEAKENED (dimension-constant,
ghost-`.zero`-graded) body preserves every occurrence count: `subst0 (weaken body) arg` counts at every
position exactly what `body` counts there — the substituted `arg` contributes NOTHING, because the
binder is used zero times.  The closed-form quantitative content of the strongest binder grade, via the
shipped `weaken_subst_singleton`. -/
theorem RawTerm.occurrenceCountAt_subst0_weaken {scope : Nat}
    (body rawArg : RawTerm scope) (position : Fin scope) :
    RawTerm.occurrenceCountAt (RawTerm.subst0 (RawTerm.weaken body) rawArg) position
      = RawTerm.occurrenceCountAt body position := by
  dsimp only [RawTerm.subst0]
  rw [RawTerm.weaken_subst_singleton body rawArg]

/-- **The general ghost case.**  A body that STRENGTHENS (does not use the substituted binder) erases
`arg` under `subst0`: `subst0 body arg = extracted`, so its occurrence count at every position is the
strengthened body's, with zero contribution from `arg`.  Via the shipped `strengthen_commutes_subst0`. -/
theorem RawTerm.occurrenceCountAt_subst0_of_strengthens {scope : Nat}
    (body : RawTerm (scope + 1)) (extracted rawArg : RawTerm scope)
    (strengthens : RawTerm.strengthen body = some extracted)
    (position : Fin scope) :
    RawTerm.occurrenceCountAt (RawTerm.subst0 body rawArg) position
      = RawTerm.occurrenceCountAt extracted position := by
  rw [RawTerm.strengthen_commutes_subst0 body extracted rawArg strengthens]

/-- **★ Non-vacuous witness.**  `subst0 (weaken (var 0)) arg` still counts `var 0` exactly once — the
ghost substitution genuinely preserves a real occurrence (the count is not vacuously zero). -/
theorem RawTerm.occurrenceCountAt_subst0_weaken_self {scope : Nat}
    (rawArg : RawTerm (scope + 1)) :
    RawTerm.occurrenceCountAt
        (RawTerm.subst0 (RawTerm.weaken
          (.mkGen .gen_var (⟨0, Nat.succ_pos scope⟩ : Fin (scope + 1)) .childNil)) rawArg)
        ⟨0, Nat.succ_pos scope⟩
      = 1 := by
  rw [RawTerm.occurrenceCountAt_subst0_weaken]
  exact RawTerm.occurrenceCountAt_var_self ⟨0, Nat.succ_pos scope⟩

end FX1Poly.Core
