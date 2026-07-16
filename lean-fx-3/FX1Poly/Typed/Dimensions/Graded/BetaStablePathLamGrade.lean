import FX1Poly.Typed.Dimensions.Graded.GradedTableCoherence
import FX1Poly.Axis.Term.Subst.RawTermOccurrenceSubst
import FX1Poly.Axis.Term.Subst.RawTermOccurrenceSubstLift
import FX1Poly.Axis.Term.Subst.RawTermSubst0

/-! # FX1Poly/Typed/BetaStablePathLamGrade — the BETA-STABLE dimension-usage grade for `pathLam`

`pathLam`'s affineness is currently the side condition `gradedBinderChecks UsageGrade.one body`,
which unfolds to the RAW occurrence bound `RawTerm.occurrenceCountAt body 0 ≤ 1`.  That raw count is
BETA-FRAGILE: a typed `pathLam` whose body contains a redex `(lam y. pair y y) (g @ i)` (the
dimension `i` occurring once) beta-steps to `pair (g @ i) (g @ i)` — the dimension's raw occurrence
count jumps `1 → 2`, so a typed `pathLam` can step to a count-violating one and SUBJECT REDUCTION
fails.  The raw count sees only the CURRENT occurrences; it misses the duplication the redex WILL
cause.

## The fix: account the dimension's USAGE GRADE, not its raw count

The App rule scales the argument's grades by the function's binder grade `r` (`functionGrades + r *
argumentGrades`, §6.2).  FX's ordinary `lam` carries binder grade `UsageGrade.omega` (the parameter
is unrestricted), so in `(lam y. pair y y) (g @ i)` the dimension `i`'s grade is
`UsageGrade.mul UsageGrade.omega UsageGrade.one = UsageGrade.omega`, which is NOT `≤ UsageGrade.one`
— the REDEX is rejected by the grade premise BEFORE it can reduce.  The grade sees the future
duplication inside the redex because the App scaling `r * p` is exactly the substitution scaling.

## The SR-stability key (the graded substitution lemma)

For a redex `(lam y. M) N ↝ M[N/y]` the App rule grades a dimension at `dimGrade M + r * dimGrade N`
with `r` the lam's parameter grade `= y`'s usage in `M`; the substitution `M[N/y]` grades the same
dimension at `dimGrade M + (usage of y in M) * dimGrade N`.  These AGREE — App scaling `r * p` IS
substitution scaling — so the grade premise (dimension grade `≤ UsageGrade.one`) is INVARIANT under
`Step`.  At the COUNT level this is the master equation
`occurrenceCountAt (subst0 body arg) p = occurrenceCountAt body p.succ
  + occurrenceCountAt body 0 * occurrenceCountAt arg p`
(noted as the remaining prerequisite in `RawTermOccurrenceSubst.lean`); applying the SEMIRING
homomorphism `natToUsageGrade` (additive `natToUsageGrade_addHom` AND multiplicative
`natToUsageGrade_mulHom`, landed here) carries it to the grade-level identity.

## What this file ships (each piece zero-axiom)

  * **`natToUsageGrade_mulHom`** — ★ the count→grade abstraction is MULTIPLICATIVE too, so together
    with the shipped additive hom it is a full SEMIRING homomorphism `(Nat, +, *, 0, 1) →
    (UsageGrade, add, mul, zero, one)`.  The multiplicative half is what carries the substitution
    SCALING `g_y * g_N` to the grade level.
  * the named scaling facts `UsageGrade.omega_mul_one_eq_omega` / `one_mul_omega_eq_omega` /
    `omega_not_le_one` — the omega-scaling arithmetic the rejection of the duplicating redex uses.
  * **`natToUsageGrade_monotone`** — the count→grade abstraction is order-preserving, the bridge
    from a count bound to a grade bound.
  * **`RawTerm.dimensionUsageGrade`** — the dimension's usage grade `= natToUsageGrade ∘
    occurrenceCountAt` (the grade reading of one position's count); its beta good behavior is the
    substitution lemma, NOT in-place stability.
  * **`RawTerm.bodyBinderUsageGrade`** — the structural reading of the App rule's scalar `r`: a
    lambda body's usage of its OWN freshest binder (`natToUsageGrade (occurrenceCountAt body 0)`).
  * **`RawTerm.affineBinderGradePremise`** (+ `_iff_gradedBinderChecks`) — the grade reading of the
    SUPERSEDED `pathLamIntroRule.sideCondition`; it is NOT beta-stable, which is why it was replaced.
    The swap has LANDED — the live premise is the App-scaled grade (`AppScaledPathLamGrade`) with
    unconditional zero-axiom beta-stability (`AppScaledSubstMetatheory`).  Retained as the historical
    record of what the swap moved away from.
  * **`RawTerm.occurrenceCountAt_subst0`** — ★ THE COUNT MASTER EQUATION, now PROVEN (was the
    "remaining" prerequisite flagged in `RawTermOccurrenceSubst.lean`): `occ (subst0 body arg) p =
    occ body p.succ + occ body 0 * occ arg p`, via a WEIGHTED generalization
    (`occurrenceCountAt_subst_weightProfile`) of the shipped exact-hit profile that carries the
    duplication term.
  * **`dimensionUsageGrade_subst0`** — ★ THE GRADED SUBSTITUTION LEMMA (the SR-stability key),
    UNCONDITIONAL: the dimension grade of `subst0 body arg` equals `add (dimensionUsageGrade body
    p.succ) (mul (bodyBinderUsageGrade body) (dimensionUsageGrade arg p))` — App-scaling agrees with
    substitution-scaling at the grade level, so the dimension grade is a beta INVARIANT.
    (`dimensionUsageGrade_subst0_master` is the same statement parameterized by the count master.)
  * **`dimensionUsageGrade_subst0_omegaBlowup`** — ★ the non-vacuous demonstration: an unrestricted
    binder over a dimension-carrying argument forces the reduct's dimension grade to `omega`, catching
    the raw count's beta-fragility at the grade level.
  * **`dimensionUsageGrade_subst0_ghost`** — the ghost instance: a dimension-constant (`weaken`) body
    carries the dimension grade through `subst0` unchanged.

## Honest scope / limitation

The grade-level SR-stability KEY `dimensionUsageGrade_subst0` is UNCONDITIONAL — the count master
`occurrenceCountAt_subst0` (the general arg-multiplicity half) is proven here.  It shows the reduct's
dimension grade equals the App-rule grade of the redex `funcGrade + binderGrade * argGrade`, so under a
beta step the dimension grade is INVARIANT (the App scalar `r` agreeing with substitution-scaling is the
whole point).  The App scalar `r` is read structurally as `bodyBinderUsageGrade` — a lambda body's own
usage of its freshest binder — which coincides with a LITERAL lambda's declared binder grade and needs
NO typing information; for a NEUTRAL function it is the function's Pi-binder grade (the type layer), and
the substitution lemma is binder-grade-agnostic so it composes with either reading.

What is NOT yet built is the beta-stable PREMISE itself: it is the App-SCALED dimension grade — a
RECURSIVE accounting over the body that, at each application node, scales the argument's dimension grade
by that function's binder grade (so the crux body `(lam y. pair y y) (g @ i)` grades the dimension at
`omega * one = omega`, rejecting the redex).  `dimensionUsageGrade` here reads only ONE position's count
and is therefore NOT that recursive accounting; `affineBinderGradePremise` is exactly the current
(beta-fragile) binder-only premise, recorded in grade vocabulary.  The substitution lemma is the
redex-case PRESERVATION engine for the recursive accounting; defining that accounting (it needs the
per-application binder grade — structural for literal lambdas, typing-dependent for neutrals) and
proving its `Step` congruence preservation is the remaining work to swap
`pathLamIntroRule.sideCondition` (see the final-report plan).

## Zero-axiom

`natToUsageGrade_mulHom` is a nine-case enumeration (`rfl` / `Nat.zero_mul` / `Nat.one_mul` /
`Nat.mul_zero` / `Nat.mul_one`); the scaling facts are `rfl`; `natToUsageGrade_monotone` is a
finite case split via `Bool.noConfusion`; the master lemma is a `rw` of the additive + multiplicative
homs; the ghost instance cites `occurrenceCountAt_subst0_weaken`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Audit-gated in
`FX1PolyAudit/Typed/Dimensions/Graded/BetaStablePathLamGrade.lean`. -/

/-! ## The COUNT master equation (the structural SR-stability prerequisite)

The shipped `RawTermOccurrenceSubst.lean` proves the GHOST and EXACT-HIT halves of the occurrence
substitution metatheory and flags the general arg-multiplicity master
`occ (subst0 body arg) p = occ body p.succ + occ body 0 * occ arg p` as the remaining prerequisite.
We land it here by generalizing the shipped EXACT-HIT profile (`hitsExactlyAt`, where each substituent
counts the target as the bare indicator of a single source position) to a WEIGHTED profile that adds a
duplication term `(indicator of the binder) * weight`.  The induction mirrors
`occurrenceCountAt_subst_hitProfile` step-for-step; the genuinely new ingredient is the
right-distributivity rearrangement at the child-spine cons node. -/

namespace FX1Poly.Core

open FX1Poly.Axis.Syntax

/-- The four-way addition exchange `(a + b) + (c + d) = (a + c) + (b + d)` — the commutative-monoid
rearrangement the child-spine cons node needs, by explicit `add_assoc` / `add_left_comm` (axiom-free,
unlike `ac_rfl`). -/
theorem addExchangeFourWay (firstTerm secondTerm thirdTerm fourthTerm : Nat) :
    (firstTerm + secondTerm) + (thirdTerm + fourthTerm)
      = (firstTerm + thirdTerm) + (secondTerm + fourthTerm) := by
  rw [Nat.add_assoc, Nat.add_assoc, Nat.add_left_comm secondTerm thirdTerm fourthTerm]

/-- Right distributivity `(p + q) * weight = p * weight + q * weight`, proven zero-axiom by induction
on `weight` (`Nat.add_mul` itself leaks propext, so the structural induction is used instead). -/
theorem natRightDistribByWeight (firstFactor secondFactor weight : Nat) :
    (firstFactor + secondFactor) * weight = firstFactor * weight + secondFactor * weight := by
  induction weight with
  | zero => rfl
  | succ priorWeight inductiveHypothesis =>
      rw [Nat.mul_succ, Nat.mul_succ, Nat.mul_succ, inductiveHypothesis]
      exact addExchangeFourWay (firstFactor * priorWeight) (secondFactor * priorWeight)
        firstFactor secondFactor

/-- **A WEIGHTED hit profile** for a substitution at `targetPosition`: every substituent image counts
`targetPosition` as the indicator of the SHIFT source position PLUS the indicator of the BINDER
(special) source position scaled by a fixed `weight`.  The generalization of the shipped
`hitsExactlyAt` (which is the `weight = 0` case) that records the duplication a non-affine binder
causes — phrased through the variable cell's own count to sidestep the `gen_var.payload` `Decidable`. -/
def RawTermSubst.hitsWithWeight {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (shiftSource binderSource : Fin sourceScope) (targetPosition : Fin targetScope)
    (weight : Nat) : Prop :=
  ∀ candidatePosition : Fin sourceScope,
    RawTerm.occurrenceCountAt (substitution candidatePosition) targetPosition
      = RawTerm.occurrenceCountAt (.mkGen .gen_var candidatePosition .childNil) shiftSource
        + RawTerm.occurrenceCountAt (.mkGen .gen_var candidatePosition .childNil) binderSource
          * weight

/-- One binder lift transports a weighted hit profile to the raised positions, with the SAME weight:
`var 0` (the fresh bound variable) hits no raised source, and index `k+1` carries the weakened source
substituent whose count at `Fin.succ targetPosition` is the un-raised count
(`occurrenceCountAt_weaken_succ`). -/
theorem RawTermSubst.lift_hitsWithWeight_succ {sourceScope targetScope : Nat}
    {substitution : RawTermSubst sourceScope targetScope}
    {shiftSource binderSource : Fin sourceScope} {targetPosition : Fin targetScope} {weight : Nat}
    (profile : RawTermSubst.hitsWithWeight substitution shiftSource binderSource targetPosition weight) :
    RawTermSubst.hitsWithWeight (RawTermSubst.lift substitution)
      (Fin.succ shiftSource) (Fin.succ binderSource) (Fin.succ targetPosition) weight := by
  intro candidatePosition
  obtain ⟨candidateValue, candidateBound⟩ := candidatePosition
  cases candidateValue with
  | zero =>
      show RawTerm.occurrenceCountAt
          (.mkGen .gen_var (⟨0, Nat.zero_lt_succ targetScope⟩ : Fin (targetScope + 1)) .childNil)
          (Fin.succ targetPosition)
        = RawTerm.occurrenceCountAt
            (.mkGen .gen_var (⟨0, candidateBound⟩ : Fin (sourceScope + 1)) .childNil)
            (Fin.succ shiftSource)
          + RawTerm.occurrenceCountAt
              (.mkGen .gen_var (⟨0, candidateBound⟩ : Fin (sourceScope + 1)) .childNil)
              (Fin.succ binderSource) * weight
      rw [occurrenceCountAt_var_of_ne (by intro hit; exact Nat.noConfusion (congrArg Fin.val hit)),
        occurrenceCountAt_var_of_ne (by intro hit; exact Nat.noConfusion (congrArg Fin.val hit)),
        occurrenceCountAt_var_of_ne (by intro hit; exact Nat.noConfusion (congrArg Fin.val hit)),
        Nat.zero_mul, Nat.add_zero]
  | succ priorValue =>
      have priorBound : priorValue < sourceScope := Nat.lt_of_succ_lt_succ candidateBound
      show RawTerm.occurrenceCountAt
          (RawTerm.weaken (substitution ⟨priorValue, priorBound⟩)) (Fin.succ targetPosition)
        = RawTerm.occurrenceCountAt
            (.mkGen .gen_var (⟨priorValue + 1, candidateBound⟩ : Fin (sourceScope + 1)) .childNil)
            (Fin.succ shiftSource)
          + RawTerm.occurrenceCountAt
              (.mkGen .gen_var (⟨priorValue + 1, candidateBound⟩ : Fin (sourceScope + 1)) .childNil)
              (Fin.succ binderSource) * weight
      rw [RawTerm.occurrenceCountAt_weaken_succ, profile ⟨priorValue, priorBound⟩,
        ← occurrenceCountAt_var_succ_eq priorValue priorBound candidateBound shiftSource,
        ← occurrenceCountAt_var_succ_eq priorValue priorBound candidateBound binderSource]

/-- Iterated binder lifting transports the weighted hit profile to the raised positions. -/
theorem iterateLiftRaw_hitsWithWeight_raised {sourceScope targetScope : Nat}
    {substitution : RawTermSubst sourceScope targetScope}
    {shiftSource binderSource : Fin sourceScope} {targetPosition : Fin targetScope} {weight : Nat}
    (profile : RawTermSubst.hitsWithWeight substitution shiftSource binderSource targetPosition weight) :
    ∀ binderShift : Nat,
      RawTermSubst.hitsWithWeight (iterateLiftRaw substitution binderShift)
        (RawVarSet.raiseParentPosition binderShift shiftSource)
        (RawVarSet.raiseParentPosition binderShift binderSource)
        (RawVarSet.raiseParentPosition binderShift targetPosition) weight
  | 0 => by
      rw [RawVarSet.raiseParentPosition_zero, RawVarSet.raiseParentPosition_zero,
        RawVarSet.raiseParentPosition_zero]
      exact profile
  | binderShift + 1 => by
      rw [RawVarSet.raiseParentPosition_succ, RawVarSet.raiseParentPosition_succ,
        RawVarSet.raiseParentPosition_succ]
      exact RawTermSubst.lift_hitsWithWeight_succ
        (iterateLiftRaw_hitsWithWeight_raised profile binderShift)

mutual

/-- **★ Substitution under a WEIGHTED hit profile transports the occurrence count with the duplication
term.**  If every substituent counts `targetPosition` as the shift indicator plus the binder indicator
scaled by `weight`, then the substituted term counts `targetPosition` as `occ source shiftSource +
occ source binderSource * weight`.  The arg-multiplicity master generalizing the shipped
`occurrenceCountAt_subst_hitProfile`. -/
theorem RawTerm.occurrenceCountAt_subst_weightProfile {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (sourceTerm : RawTerm sourceScope)
    (shiftSource binderSource : Fin sourceScope) (targetPosition : Fin targetScope) (weight : Nat)
    (profile : RawTermSubst.hitsWithWeight substitution shiftSource binderSource targetPosition weight) :
    RawTerm.occurrenceCountAt (RawTerm.subst substitution sourceTerm) targetPosition
      = RawTerm.occurrenceCountAt sourceTerm shiftSource
        + RawTerm.occurrenceCountAt sourceTerm binderSource * weight :=
  match sourceTerm with
  | .mkGen generator payload children => by
      by_cases generatorIsVar : generator = .gen_var
      · subst generatorIsVar
        show RawTerm.occurrenceCountAt
          (fold GenAlgebra.canonical substitution
            (.mkGen .gen_var payload children)) targetPosition
          = RawTerm.occurrenceCountAt (.mkGen .gen_var payload children) shiftSource
            + RawTerm.occurrenceCountAt (.mkGen .gen_var payload children) binderSource * weight
        dsimp only [fold]
        rw [dif_pos rfl]
        exact profile payload
      · rw [RawTerm.subst_mkGen_of_ne_var substitution generatorIsVar payload children]
        dsimp only [RawTerm.occurrenceCountAt]
        rw [dif_neg generatorIsVar, dif_neg generatorIsVar, dif_neg generatorIsVar]
        exact RawTermChildren.occurrenceCountAt_subst_weightProfile
          substitution children shiftSource binderSource targetPosition weight profile

/-- Children-spine version of `RawTerm.occurrenceCountAt_subst_weightProfile`. -/
theorem RawTermChildren.occurrenceCountAt_subst_weightProfile {sourceScope targetScope : Nat}
    {binderShifts : List Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (sourceChildren : RawTermChildren binderShifts sourceScope)
    (shiftSource binderSource : Fin sourceScope) (targetPosition : Fin targetScope) (weight : Nat)
    (profile : RawTermSubst.hitsWithWeight substitution shiftSource binderSource targetPosition weight) :
    RawTermChildren.occurrenceCountAt
        (RawTermChildren.subst substitution sourceChildren) targetPosition
      = RawTermChildren.occurrenceCountAt sourceChildren shiftSource
        + RawTermChildren.occurrenceCountAt sourceChildren binderSource * weight :=
  match binderShifts, sourceChildren with
  | [], .childNil => by
      show (0 : Nat) = 0 + 0 * weight
      rw [Nat.zero_mul, Nat.add_zero]
  | binderShift :: _restShifts, .childCons childHead childTail => by
      show RawTerm.occurrenceCountAt
          (fold GenAlgebra.canonical
            (iterateLiftRaw substitution binderShift) childHead)
          (RawVarSet.raiseParentPosition binderShift targetPosition) +
        RawTermChildren.occurrenceCountAt
          (foldChildren GenAlgebra.canonical substitution childTail)
          targetPosition
        = (RawTerm.occurrenceCountAt childHead
              (RawVarSet.raiseParentPosition binderShift shiftSource) +
            RawTermChildren.occurrenceCountAt childTail shiftSource)
          + (RawTerm.occurrenceCountAt childHead
                (RawVarSet.raiseParentPosition binderShift binderSource) +
              RawTermChildren.occurrenceCountAt childTail binderSource) * weight
      rw [← RawTerm.subst_eq_fold, ← RawTermChildren.subst_eq_foldChildren]
      rw [RawTerm.occurrenceCountAt_subst_weightProfile
            (iterateLiftRaw substitution binderShift) childHead
            (RawVarSet.raiseParentPosition binderShift shiftSource)
            (RawVarSet.raiseParentPosition binderShift binderSource)
            (RawVarSet.raiseParentPosition binderShift targetPosition) weight
            (iterateLiftRaw_hitsWithWeight_raised profile binderShift),
          RawTermChildren.occurrenceCountAt_subst_weightProfile
            substitution childTail shiftSource binderSource targetPosition weight profile,
          natRightDistribByWeight, addExchangeFourWay]

end

/-- The single-position substitution `RawTermSubst.singleton arg` satisfies the weighted hit profile at
target `position`: the shift source is `Fin.succ position` (every higher variable shifts down by one),
the binder source is `var 0`, and the weight is `arg`'s own occurrence count at `position`. -/
theorem RawTermSubst.singleton_hitsWithWeight {scope : Nat}
    (rawArg : RawTerm scope) (position : Fin scope) :
    RawTermSubst.hitsWithWeight (RawTermSubst.singleton rawArg)
      (Fin.succ position) ⟨0, Nat.succ_pos scope⟩ position
      (RawTerm.occurrenceCountAt rawArg position) := by
  intro candidatePosition
  obtain ⟨candidateValue, candidateBound⟩ := candidatePosition
  cases candidateValue with
  | zero =>
      show RawTerm.occurrenceCountAt rawArg position
        = RawTerm.occurrenceCountAt
            (.mkGen .gen_var (⟨0, candidateBound⟩ : Fin (scope + 1)) .childNil) (Fin.succ position)
          + RawTerm.occurrenceCountAt
              (.mkGen .gen_var (⟨0, candidateBound⟩ : Fin (scope + 1)) .childNil)
              ⟨0, Nat.succ_pos scope⟩ * RawTerm.occurrenceCountAt rawArg position
      have shiftMiss :
          RawTerm.occurrenceCountAt
            (.mkGen .gen_var (⟨0, candidateBound⟩ : Fin (scope + 1)) .childNil)
            (Fin.succ position) = 0 :=
        occurrenceCountAt_var_of_ne (by intro hit; exact Nat.noConfusion (congrArg Fin.val hit))
      have binderHit :
          RawTerm.occurrenceCountAt
            (.mkGen .gen_var (⟨0, candidateBound⟩ : Fin (scope + 1)) .childNil)
            (⟨0, Nat.succ_pos scope⟩ : Fin (scope + 1)) = 1 :=
        RawTerm.occurrenceCountAt_var_self ⟨0, candidateBound⟩
      rw [shiftMiss, binderHit, Nat.one_mul, Nat.zero_add]
  | succ priorValue =>
      have priorBound : priorValue < scope := Nat.lt_of_succ_lt_succ candidateBound
      show RawTerm.occurrenceCountAt
          (.mkGen .gen_var (⟨priorValue, priorBound⟩ : Fin scope) .childNil) position
        = RawTerm.occurrenceCountAt
            (.mkGen .gen_var (⟨priorValue + 1, candidateBound⟩ : Fin (scope + 1)) .childNil)
            (Fin.succ position)
          + RawTerm.occurrenceCountAt
              (.mkGen .gen_var (⟨priorValue + 1, candidateBound⟩ : Fin (scope + 1)) .childNil)
              ⟨0, Nat.succ_pos scope⟩
            * RawTerm.occurrenceCountAt rawArg position
      have binderMiss :
          RawTerm.occurrenceCountAt
            (.mkGen .gen_var (⟨priorValue + 1, candidateBound⟩ : Fin (scope + 1)) .childNil)
            (⟨0, Nat.succ_pos scope⟩ : Fin (scope + 1)) = 0 :=
        occurrenceCountAt_var_of_ne
          (by intro succEqZero; exact Nat.noConfusion (congrArg Fin.val succEqZero))
      rw [binderMiss, Nat.zero_mul, Nat.add_zero]
      exact occurrenceCountAt_var_succ_eq priorValue priorBound candidateBound position

/-- **★ THE COUNT MASTER EQUATION** (the arg-multiplicity half flagged in `RawTermOccurrenceSubst.lean`).
`occ (subst0 body arg) p = occ body p.succ + occ body 0 * occ arg p`.  Beta substituting the binder by
`arg` shifts every other variable down (the `occ body p.succ` term) and duplicates `arg` once per
binder use (`occ body 0` copies, each contributing `occ arg p`).  The structural SR-stability key the
graded substitution lemma lifts to usage grades. -/
theorem RawTerm.occurrenceCountAt_subst0 {scope : Nat}
    (body : RawTerm (scope + 1)) (rawArg : RawTerm scope) (position : Fin scope) :
    RawTerm.occurrenceCountAt (RawTerm.subst0 body rawArg) position
      = RawTerm.occurrenceCountAt body (Fin.succ position)
        + RawTerm.occurrenceCountAt body ⟨0, Nat.succ_pos scope⟩
          * RawTerm.occurrenceCountAt rawArg position :=
  RawTerm.occurrenceCountAt_subst_weightProfile (RawTermSubst.singleton rawArg) body
    (Fin.succ position) ⟨0, Nat.succ_pos scope⟩ position
    (RawTerm.occurrenceCountAt rawArg position)
    (RawTermSubst.singleton_hitsWithWeight rawArg position)

end FX1Poly.Core

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Modal

/-! ## The semiring-homomorphism completion: the multiplicative half -/

/-- **★ The count→grade abstraction is a MULTIPLICATIVE homomorphism** `natToUsageGrade (a * b) =
mul (natToUsageGrade a) (natToUsageGrade b)`.  Together with the shipped additive hom
`natToUsageGrade_addHom` this makes `natToUsageGrade` a full SEMIRING homomorphism `(Nat, +, *, 0, 1)
→ (UsageGrade, add, mul, zero, one)`.  The multiplicative half is exactly what carries the
substitution SCALING `(usage of y) * (dimension count of the argument)` to the usage-grade level —
the arithmetic core of beta-stability.  Nine-case enumeration; the load-bearing diagonal is
`(a+2) * (b+2) ↦ omega = mul omega omega`. -/
theorem natToUsageGrade_mulHom : ∀ (firstCount secondCount : Nat),
    natToUsageGrade (firstCount * secondCount)
      = UsageGrade.mul (natToUsageGrade firstCount) (natToUsageGrade secondCount)
  | 0, 0 => rfl
  | 0, 1 => rfl
  | 0, _ + 2 => by rw [Nat.zero_mul]; exact (UsageGrade.zero_mul _).symm
  | 1, 0 => rfl
  | 1, 1 => rfl
  | 1, _ + 2 => by rw [Nat.one_mul]; exact (UsageGrade.one_mul _).symm
  | _ + 2, 0 => by rw [Nat.mul_zero]; exact (UsageGrade.mul_zero _).symm
  | _ + 2, 1 => by rw [Nat.mul_one]; exact (UsageGrade.mul_one _).symm
  | _ + 2, _ + 2 => rfl

/-! ## The omega-scaling arithmetic (the duplicating-redex rejection) -/

/-- The omega-binder scales a once-occurring dimension to `omega`: `mul omega one = omega`.  The
arithmetic that makes the ordinary `lam`'s unrestricted parameter reject a dimension-carrying
argument inside a `pathLam` body. -/
theorem UsageGrade.omega_mul_one_eq_omega :
    UsageGrade.mul UsageGrade.omega UsageGrade.one = UsageGrade.omega := rfl

/-- The symmetric scaling fact `mul one omega = omega`. -/
theorem UsageGrade.one_mul_omega_eq_omega :
    UsageGrade.mul UsageGrade.one UsageGrade.omega = UsageGrade.omega := rfl

/-- `omega` is NOT below the affine grade `one`: the omega-scaled dimension fails the affine premise
`≤ one`.  The pin that the duplicating redex is rejected by the grade. -/
theorem UsageGrade.omega_not_le_one :
    UsageGrade.le UsageGrade.omega UsageGrade.one = false := rfl

/-! ## Order preservation: the count-bound → grade-bound bridge -/

/-- **The count→grade abstraction is ORDER-PRESERVING**: a count below another maps to a grade below
the other's image.  The bridge from a syntactic count bound to a usage-grade bound — finite case
split on the count shapes, the impossible orders refuted by `Bool.noConfusion`. -/
theorem natToUsageGrade_monotone : ∀ (firstCount secondCount : Nat),
    firstCount ≤ secondCount →
      UsageGrade.le (natToUsageGrade firstCount) (natToUsageGrade secondCount) = true
  | 0, secondCount, _ => by
      cases secondShape : natToUsageGrade secondCount <;> rfl
  | 1, 0, oneLeZero => absurd oneLeZero (Nat.not_succ_le_zero 0)
  | 1, 1, _ => rfl
  | 1, _ + 2, _ => rfl
  | _ + 2, 0, succLeZero => absurd succLeZero (Nat.not_succ_le_zero _)
  | _ + 2, 1, succSuccLeOne =>
      absurd (Nat.le_of_succ_le_succ succSuccLeOne) (Nat.not_succ_le_zero _)
  | _ + 2, _ + 2, _ => rfl

/-! ## The dimension usage grade + the App-rule binder scalar -/

/-- **The dimension's usage grade** — the semiring image `natToUsageGrade` of the syntactic occurrence
count at a dimension position.  This is the GRADE READING of a single position's count; on its own (at
the binder of a `pathLam`) it equals the current beta-FRAGILE premise.  Its beta good behavior is NOT
that this reading is stable in place, but that under `subst0` it transforms by App-SCALING
(`dimensionUsageGrade_subst0` below) — the App-rule scalar `r * p` agreeing with substitution-scaling,
which is the genuine SR-stability key. -/
def RawTerm.dimensionUsageGrade {scope : Nat} (body : RawTerm scope)
    (dimension : Fin scope) : UsageGrade :=
  natToUsageGrade (RawTerm.occurrenceCountAt body dimension)

/-- **The App rule's scalar, read structurally** — a lambda body's usage grade for its OWN freshest
binder (position `0`).  For a redex `(lam y. body) arg` this is the parameter grade `r` the App rule
scales the argument by; reading it off the body's `var 0` occurrence count is the structural reading
that needs no typing information (it coincides with a literal lambda's binder grade). -/
def RawTerm.bodyBinderUsageGrade {scope : Nat} (body : RawTerm (scope + 1)) : UsageGrade :=
  natToUsageGrade (RawTerm.occurrenceCountAt body ⟨0, Nat.succ_pos scope⟩)

/-- **The affine binder-grade premise (the grade reading of the SUPERSEDED premise)** for `pathLam`: the
dimension's usage grade at the freshest binder is below the affine grade `one`.  This is NOT beta-stable
— it equals the raw bound `occurrenceCountAt body 0 ≤ 1`, reading only the binder's RAW count and missing
the App-scaling that a duplicating redex inside the body would cause.

★ **HISTORICAL.**  The swap this vocabulary was written to describe has LANDED: `pathLamIntroRule` now
carries `RawTerm.appScaledDimensionGrade body 0 <= one` (the App-SCALED grade, which scales each
application's argument by `RawTerm.functionBinderGrade` of its head — §6.2's `p1 + r * p2`), and its
beta-stability is proven unconditionally and zero-axiom
(`appScaledRootBeta_le_unconditional`, `appScaledRootPathBeta_le_ofAffine_unconditional`).  This
definition is retained as the grade reading of the OLD premise — it documents what was replaced and why,
and is what the swap-equivalence lemmas below are stated against.  It is not a live side condition. -/
def RawTerm.affineBinderGradePremise {scope : Nat} (body : RawTerm (scope + 1)) : Prop :=
  UsageGrade.le (RawTerm.dimensionUsageGrade body ⟨0, Nat.succ_pos scope⟩) UsageGrade.one = true

/-- The affine binder-grade premise is EQUIVALENT to the current `gradedBinderChecks` affine check (the
grade reading of the SAME bound, by the shipped keystone `gradedBinderChecks_iff_gradeSubsumption`).
This pins that `dimensionUsageGrade body 0 ≤ one` IS the current `pathLamIntroRule.sideCondition` — so
the beta-stable upgrade is a change from this binder-only reading to the App-scaled one, not a change of
the affine grade. -/
theorem affineBinderGradePremise_iff_gradedBinderChecks {scope : Nat} (body : RawTerm (scope + 1)) :
    RawTerm.affineBinderGradePremise body ↔ gradedBinderChecks UsageGrade.one body :=
  (gradedBinderChecks_iff_gradeSubsumption UsageGrade.one body).symm

/-! ## ★ The graded substitution lemma — the SR-stability key (unconditional, via the count master) -/

/-- **★ THE GRADED SUBSTITUTION LEMMA (the SR-stability key).**  CONDITIONAL on the count master
equation `occurrenceCountAt (subst0 body arg) p = occurrenceCountAt body p.succ + occurrenceCountAt
body 0 * occurrenceCountAt arg p`, the dimension grade of `subst0 body arg` equals
`add (dimensionUsageGrade body p.succ) (mul (bodyBinderUsageGrade body) (dimensionUsageGrade arg p))`.
This is the App rule's scaling `functionGrades + r * argumentGrades` realized by substitution:
App-scaling agrees with substitution-scaling at the usage-grade level, so the affine premise
(dimension grade `≤ one`) is preserved by a beta step.  The semiring structure does all the work —
`natToUsageGrade` carries the count master through both `add` (`addHom`) and `mul` (`mulHom`). -/
theorem dimensionUsageGrade_subst0_master {scope : Nat}
    (body : RawTerm (scope + 1)) (rawArg : RawTerm scope) (dimension : Fin scope)
    (countMaster :
      RawTerm.occurrenceCountAt (RawTerm.subst0 body rawArg) dimension
        = RawTerm.occurrenceCountAt body (Fin.succ dimension)
          + RawTerm.occurrenceCountAt body ⟨0, Nat.succ_pos scope⟩
            * RawTerm.occurrenceCountAt rawArg dimension) :
    RawTerm.dimensionUsageGrade (RawTerm.subst0 body rawArg) dimension
      = UsageGrade.add
          (RawTerm.dimensionUsageGrade body (Fin.succ dimension))
          (UsageGrade.mul (RawTerm.bodyBinderUsageGrade body)
            (RawTerm.dimensionUsageGrade rawArg dimension)) := by
  dsimp only [RawTerm.dimensionUsageGrade, RawTerm.bodyBinderUsageGrade]
  rw [countMaster, natToUsageGrade_addHom, natToUsageGrade_mulHom]

/-- **★ THE GRADED SUBSTITUTION LEMMA, UNCONDITIONAL.**  Discharging `dimensionUsageGrade_subst0_master`
with the now-proven count master `RawTerm.occurrenceCountAt_subst0`: the dimension grade of the beta
reduct `subst0 body arg` is EXACTLY the App-rule grading of the dimension in the redex
`(lam body) arg` — `add (functionGrades) (mul (binderGrade) (argumentGrades))`.  This is the
SR-stability key fully proven at the structural + grade level: App-scaling and substitution-scaling
agree, so the dimension grade is a beta INVARIANT and the affine premise (`≤ one`) is preserved. -/
theorem dimensionUsageGrade_subst0 {scope : Nat}
    (body : RawTerm (scope + 1)) (rawArg : RawTerm scope) (dimension : Fin scope) :
    RawTerm.dimensionUsageGrade (RawTerm.subst0 body rawArg) dimension
      = UsageGrade.add
          (RawTerm.dimensionUsageGrade body (Fin.succ dimension))
          (UsageGrade.mul (RawTerm.bodyBinderUsageGrade body)
            (RawTerm.dimensionUsageGrade rawArg dimension)) :=
  dimensionUsageGrade_subst0_master body rawArg dimension
    (RawTerm.occurrenceCountAt_subst0 body rawArg dimension)

/-- **★ The omega-blowup the beta-stable grade CATCHES (non-vacuous).**  When the lambda body uses its
binder unrestrictedly (`bodyBinderUsageGrade body = omega`, the ordinary `lam`), the argument carries
the dimension (`dimensionUsageGrade arg p = one`), and the function part is dimension-free
(`dimensionUsageGrade body p.succ = zero`), the reduct's dimension grade is `omega` — NOT affine.
By `dimensionUsageGrade_subst0` the redex's App-graded reading is the SAME `omega`, so the grade
rejects the redex BEFORE it can step: exactly the beta-fragility of the raw count, now caught at the
grade level.  Witnesses the mechanism end-to-end (`add zero (mul omega one) = omega`). -/
theorem dimensionUsageGrade_subst0_omegaBlowup {scope : Nat}
    (body : RawTerm (scope + 1)) (rawArg : RawTerm scope) (dimension : Fin scope)
    (functionDimensionFree :
      RawTerm.dimensionUsageGrade body (Fin.succ dimension) = UsageGrade.zero)
    (binderUnrestricted : RawTerm.bodyBinderUsageGrade body = UsageGrade.omega)
    (argumentCarriesDimension :
      RawTerm.dimensionUsageGrade rawArg dimension = UsageGrade.one) :
    RawTerm.dimensionUsageGrade (RawTerm.subst0 body rawArg) dimension = UsageGrade.omega := by
  rw [dimensionUsageGrade_subst0, functionDimensionFree, binderUnrestricted,
    argumentCarriesDimension]
  rfl

/-! ## The UNCONDITIONAL ghost instance -/

/-- **The UNCONDITIONAL ghost instance of the graded substitution lemma.**  When the body is
dimension-constant (`RawTerm.weaken sourceBody` — binder grade `zero`, it does not use the substituted
binder), `subst0` carries the dimension grade through unchanged: the argument contributes NOTHING.
Discharged by the shipped quantitative-ghost lemma `occurrenceCountAt_subst0_weaken` — the strongest
binder grade, requiring no count master. -/
theorem dimensionUsageGrade_subst0_ghost {scope : Nat}
    (sourceBody rawArg : RawTerm scope) (dimension : Fin scope) :
    RawTerm.dimensionUsageGrade (RawTerm.subst0 (RawTerm.weaken sourceBody) rawArg) dimension
      = RawTerm.dimensionUsageGrade sourceBody dimension := by
  dsimp only [RawTerm.dimensionUsageGrade]
  rw [RawTerm.occurrenceCountAt_subst0_weaken]

end FX1Poly.Typed
