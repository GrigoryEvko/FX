import FX1Poly.Core.RawTermOccurrenceSubst

/-! # FX1Poly/Core/RawTermOccurrenceSubstLift — the occurrence-count master lemma under a
    HIT-PROFILE substitution (the graded-arm prerequisite for the native-union substitution lemma)

The native-union substitution lemma (NATIVE-37 part b) carries the graded binder-introduction arm: a
body typed under one binder, substituted by a LIFTED substitution `iterateLiftRaw substitution 1`, must
still pass the affine binder check `gradedBinderChecks usage body` — which is definitionally a bound on
`RawTerm.occurrenceCountAt body (var 0)`.  Under a LIFTED substitution the count at `var 0` is
PRESERVED: the lift maps `var 0` to `var 0` (one occurrence) and every other variable to a WEAKENED
substituent (zero occurrences of `var 0`, because weakening raises every index past `0`).  So the body's
freshest-binder usage is unchanged and the graded check transports verbatim.

This file ships the quantitative content of that fact, in the most reusable form:

  * **`RawTerm.occurrenceCountAt_subst_hitProfile`** (mutual with the children version) — the
    substitution analogue of `occurrenceCountAt_rename_image`: a substitution whose substituent-image
    occurrence profile at `targetPosition` is exactly the indicator of `sourcePosition` (one occurrence
    at the source variable's substituent, none at every other) transports the occurrence count from the
    source term at `sourcePosition` to the substituted term at `targetPosition`.  Mirrors the renaming
    EXACT-HIT lemma, with the genuinely-new ingredient that substituents are arbitrary terms (counted),
    not renamed variables.
  * **`RawTermSubst.lift_hitProfile_succ`** / **`iterateLiftRaw_hitProfile_raised`** — the binder
    transport: a hit profile lifts to the raised positions (`var 0` is the fresh bound variable, hitting
    neither raised source nor raised target; index `k+1` carries the weakened source substituent, whose
    count at the raised target is the un-raised count by `occurrenceCountAt_weaken_succ`).
  * **`RawTerm.occurrenceCountAt_subst_lift_zeroPosition`** — ★ the headline the graded arm consumes:
    `occurrenceCountAt (subst (iterateLiftRaw substitution 1) body) (var 0) = occurrenceCountAt body
    (var 0)`.  A lifted substitution preserves the freshest-binder occurrence count exactly.

## Zero-axiom

The hit-profile induction mirrors `occurrenceCountAt_rename_image` (structural over the term/children
spine; the var case routes the singleton through `contains_singleton_iff` with the count profile read
off via a `Bool`-value `cases`, never a `by_cases` on a payload equality).  The binder transport is the
shipped `occurrenceCountAt_weaken_succ` / `occurrenceCountAt_weaken_zeroPosition`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Audit-gated in
`FX1PolyAudit/AuditNativeUnionSubstitution.lean`. -/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-- A variable cell counts a DIFFERENT position zero times. -/
theorem occurrenceCountAt_var_of_ne {scope : Nat}
    {variablePosition queriedPosition : Fin scope}
    (different : ¬ (queriedPosition = variablePosition)) :
    RawTerm.occurrenceCountAt (.mkGen .gen_var variablePosition .childNil) queriedPosition = 0 := by
  dsimp only [RawTerm.occurrenceCountAt]
  rw [dif_pos rfl]
  have missesSingleton :
      ¬ (RawVarSet.singleton variablePosition queriedPosition = true) := by
    intro singletonHit
    exact different ((RawVarSet.contains_singleton_iff variablePosition queriedPosition).mp singletonHit)
  show (if RawVarSet.singleton variablePosition queriedPosition = true then 1 else 0) = 0
  rw [if_neg missesSingleton]

/-- `occ (var (k+1)) (succ source) = occ (var k) source`: both sides agree (each is `1` iff `k =
source`, else `0`).  Read off via the two var-count cases, propext-clean. -/
theorem occurrenceCountAt_var_succ_eq {sourceScope : Nat}
    (priorValue : Nat) (priorBound : priorValue < sourceScope)
    (candidateBound : priorValue + 1 < sourceScope + 1) (sourcePosition : Fin sourceScope) :
    RawTerm.occurrenceCountAt
        (.mkGen .gen_var (⟨priorValue, priorBound⟩ : Fin sourceScope) .childNil) sourcePosition
      = RawTerm.occurrenceCountAt
          (.mkGen .gen_var (⟨priorValue + 1, candidateBound⟩ : Fin (sourceScope + 1)) .childNil)
          (Fin.succ sourcePosition) := by
  by_cases priorIsSource : (sourcePosition = ⟨priorValue, priorBound⟩)
  · rw [priorIsSource, RawTerm.occurrenceCountAt_var_self]
    have succEq :
        (Fin.succ (⟨priorValue, priorBound⟩ : Fin sourceScope))
          = (⟨priorValue + 1, candidateBound⟩ : Fin (sourceScope + 1)) := Fin.eq_of_val_eq rfl
    rw [← succEq, RawTerm.occurrenceCountAt_var_self]
  · rw [occurrenceCountAt_var_of_ne priorIsSource,
      occurrenceCountAt_var_of_ne
        (by intro succEq
            exact priorIsSource (Fin.eq_of_val_eq (Nat.succ.inj (congrArg Fin.val succEq))))]

/-- A hit-count PROFILE for a substitution at `targetPosition` against `sourcePosition`: every
substituent image counts `targetPosition` exactly what the bare variable cell at the candidate position
counts `sourcePosition` (one occurrence when the candidate IS the source variable, none elsewhere).  The
quantitative substitution analogue of the renaming exact-hit hypothesis — phrased through the variable
cell's own count to sidestep the `Decidable` of the awkward `gen_var.payload` type. -/
def RawTermSubst.hitsExactlyAt {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (sourcePosition : Fin sourceScope) (targetPosition : Fin targetScope) : Prop :=
  ∀ candidatePosition : Fin sourceScope,
    RawTerm.occurrenceCountAt (substitution candidatePosition) targetPosition
      = RawTerm.occurrenceCountAt (.mkGen .gen_var candidatePosition .childNil) sourcePosition

/-- One binder lift transports a hit-count profile to the raised positions: `var 0` (the fresh bound
variable) hits neither the raised source nor the raised target, and index `k+1` carries the weakened
source substituent whose count at `Fin.succ targetPosition` is the un-raised count
(`occurrenceCountAt_weaken_succ`). -/
theorem RawTermSubst.lift_hitProfile_succ {sourceScope targetScope : Nat}
    {substitution : RawTermSubst sourceScope targetScope}
    {sourcePosition : Fin sourceScope} {targetPosition : Fin targetScope}
    (profile : RawTermSubst.hitsExactlyAt substitution sourcePosition targetPosition) :
    RawTermSubst.hitsExactlyAt (RawTermSubst.lift substitution)
      (Fin.succ sourcePosition) (Fin.succ targetPosition) := by
  intro candidatePosition
  obtain ⟨candidateValue, candidateBound⟩ := candidatePosition
  cases candidateValue with
  | zero =>
      -- The fresh bound variable: `lift substitution (var 0) = var 0`, count 0 at `Fin.succ target`;
      -- the source side `occ (var 0) (succ source)` is also 0 (`0 ≠ succ source.val`).
      show RawTerm.occurrenceCountAt
          (.mkGen .gen_var (⟨0, Nat.zero_lt_succ targetScope⟩ : Fin (targetScope + 1)) .childNil)
          (Fin.succ targetPosition)
        = RawTerm.occurrenceCountAt
            (.mkGen .gen_var (⟨0, candidateBound⟩ : Fin (sourceScope + 1)) .childNil)
            (Fin.succ sourcePosition)
      rw [occurrenceCountAt_var_of_ne (by intro hit; exact Nat.noConfusion (congrArg Fin.val hit)),
        occurrenceCountAt_var_of_ne (by intro hit; exact Nat.noConfusion (congrArg Fin.val hit))]
  | succ priorValue =>
      have priorBound : priorValue < sourceScope := Nat.lt_of_succ_lt_succ candidateBound
      -- `lift substitution (var (k+1)) = weaken (substitution (var k))`; its count at `succ target` is
      -- the un-raised count of `substitution (var k)` at `target` (`weaken_succ`), which the profile
      -- equates to `occ (var k) source`.  The source side `occ (var (k+1)) (succ source)` matches that.
      show RawTerm.occurrenceCountAt
          (RawTerm.weaken (substitution ⟨priorValue, priorBound⟩)) (Fin.succ targetPosition)
        = RawTerm.occurrenceCountAt
            (.mkGen .gen_var (⟨priorValue + 1, candidateBound⟩ : Fin (sourceScope + 1)) .childNil)
            (Fin.succ sourcePosition)
      rw [RawTerm.occurrenceCountAt_weaken_succ, profile ⟨priorValue, priorBound⟩]
      exact occurrenceCountAt_var_succ_eq priorValue priorBound candidateBound sourcePosition

/-- Iterated binder lifting transports the hit-count profile to the raised positions. -/
theorem iterateLiftRaw_hitProfile_raised {sourceScope targetScope : Nat}
    {substitution : RawTermSubst sourceScope targetScope}
    {sourcePosition : Fin sourceScope} {targetPosition : Fin targetScope}
    (profile : RawTermSubst.hitsExactlyAt substitution sourcePosition targetPosition) :
    ∀ binderShift : Nat,
      RawTermSubst.hitsExactlyAt (iterateLiftRaw substitution binderShift)
        (RawVarSet.raiseParentPosition binderShift sourcePosition)
        (RawVarSet.raiseParentPosition binderShift targetPosition)
  | 0 => by
      rw [RawVarSet.raiseParentPosition_zero, RawVarSet.raiseParentPosition_zero]
      exact profile
  | binderShift + 1 => by
      rw [RawVarSet.raiseParentPosition_succ, RawVarSet.raiseParentPosition_succ]
      exact RawTermSubst.lift_hitProfile_succ (iterateLiftRaw_hitProfile_raised profile binderShift)

mutual

/-- **Substitution under a hit-count profile transports the occurrence count.**  If every substituent
image counts `targetPosition` exactly the indicator of `sourcePosition`, the substituted term counts
`targetPosition` exactly what the source counts at `sourcePosition`.  The substitution analogue of
`occurrenceCountAt_rename_image` (the renamed exact-hit lemma) — but the substituents are arbitrary
terms (their occurrence counts read off the profile), not renamed variables. -/
theorem RawTerm.occurrenceCountAt_subst_hitProfile {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (sourceTerm : RawTerm sourceScope)
    (sourcePosition : Fin sourceScope) (targetPosition : Fin targetScope)
    (profile : RawTermSubst.hitsExactlyAt substitution sourcePosition targetPosition) :
    RawTerm.occurrenceCountAt (RawTerm.subst substitution sourceTerm) targetPosition
      = RawTerm.occurrenceCountAt sourceTerm sourcePosition :=
  match sourceTerm with
  | .mkGen generator payload children => by
      by_cases generatorIsVar : generator = .gen_var
      · subst generatorIsVar
        show RawTerm.occurrenceCountAt
          (fold GenAlgebra.canonical substitution
            (.mkGen .gen_var payload children)) targetPosition
          = RawTerm.occurrenceCountAt (.mkGen .gen_var payload children) sourcePosition
        dsimp only [fold]
        rw [dif_pos rfl]
        -- `subst substitution (var payload) = substitution payload`; the profile equates its count at
        -- `targetPosition` to `occ (var payload) sourcePosition` — exactly the source side.
        show RawTerm.occurrenceCountAt (substitution payload) targetPosition
          = RawTerm.occurrenceCountAt (.mkGen .gen_var payload .childNil) sourcePosition
        exact profile payload
      · rw [RawTerm.subst_mkGen_of_ne_var substitution generatorIsVar payload children]
        dsimp only [RawTerm.occurrenceCountAt]
        rw [dif_neg generatorIsVar, dif_neg generatorIsVar]
        exact RawTermChildren.occurrenceCountAt_subst_hitProfile
          substitution children sourcePosition targetPosition profile

/-- Children-spine version of `RawTerm.occurrenceCountAt_subst_hitProfile`. -/
theorem RawTermChildren.occurrenceCountAt_subst_hitProfile {sourceScope targetScope : Nat}
    {binderShifts : List Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (sourceChildren : RawTermChildren binderShifts sourceScope)
    (sourcePosition : Fin sourceScope) (targetPosition : Fin targetScope)
    (profile : RawTermSubst.hitsExactlyAt substitution sourcePosition targetPosition) :
    RawTermChildren.occurrenceCountAt
        (RawTermChildren.subst substitution sourceChildren) targetPosition
      = RawTermChildren.occurrenceCountAt sourceChildren sourcePosition :=
  match binderShifts, sourceChildren with
  | [], .childNil => rfl
  | binderShift :: _restShifts, .childCons childHead childTail => by
      show RawTerm.occurrenceCountAt
          (fold GenAlgebra.canonical
            (iterateLiftRaw substitution binderShift) childHead)
          (RawVarSet.raiseParentPosition binderShift targetPosition) +
        RawTermChildren.occurrenceCountAt
          (foldChildren GenAlgebra.canonical substitution childTail)
          targetPosition
        = RawTerm.occurrenceCountAt childHead
            (RawVarSet.raiseParentPosition binderShift sourcePosition) +
          RawTermChildren.occurrenceCountAt childTail sourcePosition
      rw [← RawTerm.subst_eq_fold, ← RawTermChildren.subst_eq_foldChildren]
      rw [RawTerm.occurrenceCountAt_subst_hitProfile
            (iterateLiftRaw substitution binderShift) childHead
            (RawVarSet.raiseParentPosition binderShift sourcePosition)
            (RawVarSet.raiseParentPosition binderShift targetPosition)
            (iterateLiftRaw_hitProfile_raised profile binderShift),
          RawTermChildren.occurrenceCountAt_subst_hitProfile
            substitution childTail sourcePosition targetPosition profile]

end

/-- The lifted substitution `iterateLiftRaw substitution 1` (≡ `RawTermSubst.lift substitution`) hits
the freshest position `var 0` exactly at `var 0`: position `0` maps to `var 0` (one occurrence of `var
0`) and every higher position maps to a weakened substituent (zero occurrences of `var 0`).  The hit
profile the graded-arm preservation reads off. -/
theorem RawTermSubst.lift_hitsExactlyAt_zero {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope) :
    RawTermSubst.hitsExactlyAt (RawTermSubst.lift substitution)
      ⟨0, Nat.succ_pos sourceScope⟩ ⟨0, Nat.succ_pos targetScope⟩ := by
  intro candidatePosition
  obtain ⟨candidateValue, candidateBound⟩ := candidatePosition
  cases candidateValue with
  | zero =>
      show RawTerm.occurrenceCountAt
          (.mkGen .gen_var (⟨0, Nat.zero_lt_succ targetScope⟩ : Fin (targetScope + 1)) .childNil)
          ⟨0, Nat.succ_pos targetScope⟩
        = RawTerm.occurrenceCountAt
            (.mkGen .gen_var (⟨0, candidateBound⟩ : Fin (sourceScope + 1)) .childNil)
            ⟨0, Nat.succ_pos sourceScope⟩
      rw [RawTerm.occurrenceCountAt_var_self, RawTerm.occurrenceCountAt_var_self]
  | succ priorValue =>
      have priorBound : priorValue < sourceScope := Nat.lt_of_succ_lt_succ candidateBound
      show RawTerm.occurrenceCountAt
          (RawTerm.weaken (substitution ⟨priorValue, priorBound⟩)) ⟨0, Nat.succ_pos targetScope⟩
        = RawTerm.occurrenceCountAt
            (.mkGen .gen_var (⟨priorValue + 1, candidateBound⟩ : Fin (sourceScope + 1)) .childNil)
            ⟨0, Nat.succ_pos sourceScope⟩
      rw [RawTerm.occurrenceCountAt_weaken_zeroPosition]
      rw [occurrenceCountAt_var_of_ne
        (by intro succEqZero; exact Nat.noConfusion (congrArg Fin.val succEqZero))]

/-- **★ A lifted substitution preserves the freshest-binder occurrence count.**
`occurrenceCountAt (subst (iterateLiftRaw substitution 1) body) (var 0) = occurrenceCountAt body (var
0)`.  The native-union substitution lemma's graded binder-introduction arm consumes this: the affine
binder check `gradedBinderChecks usage body` (a bound on the `var 0` count) transports verbatim through
the lifted substitution.  The lift never touches `var 0` and never introduces a new `var 0` (the higher
substituents are weakened), so the count is unchanged. -/
theorem RawTerm.occurrenceCountAt_subst_lift_zeroPosition {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (body : RawTerm (sourceScope + 1)) :
    RawTerm.occurrenceCountAt
        (RawTerm.subst (iterateLiftRaw substitution 1) body) ⟨0, Nat.succ_pos targetScope⟩
      = RawTerm.occurrenceCountAt body ⟨0, Nat.succ_pos sourceScope⟩ :=
  RawTerm.occurrenceCountAt_subst_hitProfile (iterateLiftRaw substitution 1) body
    ⟨0, Nat.succ_pos sourceScope⟩ ⟨0, Nat.succ_pos targetScope⟩
    (RawTermSubst.lift_hitsExactlyAt_zero substitution)

end FX1Poly.Core
