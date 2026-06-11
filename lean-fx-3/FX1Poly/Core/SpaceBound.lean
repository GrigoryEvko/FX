import FX1Poly.Core.CostBound
import FX1Poly.Core.RawSize

/-! # FX1Poly/Core/SpaceBound
    — the kernel SPACE bound: every intermediate of the canonical evaluation is size-bounded (COST-3 brick 6)

The Dim-15 (Space) counterpart of the cost semantics: space at the kernel
rewriting layer is INTERMEDIATE TERM SIZE — how large the term gets while
the canonical normalizer runs.

  * `RawTerm.OnCanonicalPath` — the canonical evaluation path: the terms
    the shipped normalizer actually visits (`reduceOnce` iterates).
    `toStepStar` shows every visited term is genuinely reachable.
  * ★ `RawTerm.spaceBound` — the computable space bound: by `Acc.rec`
    (constant `Nat` motive), the SUM of the sizes along the canonical
    path.  Sum, not max: `Nat.le_max_*` leaks `propext`, and the sum
    dominates the max — the propext-free SUM-bound discipline at the
    price of slack (same trade as `costBound`).
  * ★ `RawTerm.spaceBound_isSound` — EVERY term the canonical evaluation
    visits has size at most `spaceBound`; in particular the input
    (`size_le_spaceBound`) and THE normal form
    (`normalize_size_le_spaceBound`, via `normalize_onCanonicalPath`).
  * Non-vacuity: `spaceBound unit = 1` by kernel evaluation; the
    identity-β fixture's canonical path reaches `unit` and BOTH
    endpoints are bounded.

## Honest scope boundary

This bounds the CANONICAL strategy's intermediates (the path the shipped
normalizer takes) — not every strategy's.  A worst-case-over-all-
strategies space bound would fold sizes over the brick-2/3 reduct
enumeration exactly as `costBound` does; the canonical-path version is
what the Dim-15 packaging ("the space the evaluator actually uses")
needs.

Zero-axiom; gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Core

open Foundation

/-! ## The canonical evaluation path -/

/-- **The canonical evaluation path**: `OnCanonicalPath term intermediate`
holds when the shipped normalizer, iterating `reduceOnce` from `term`,
visits `intermediate`. -/
inductive RawTerm.OnCanonicalPath {scope : Nat} :
    RawTerm scope → RawTerm scope → Prop where
  /-- The start is visited. -/
  | here (term : RawTerm scope) : RawTerm.OnCanonicalPath term term
  /-- A fired step extends the path. -/
  | there {term reduct intermediate : RawTerm scope}
      (fireStep : RawTerm.reduceOnce term = some reduct)
      (restPath : RawTerm.OnCanonicalPath reduct intermediate) :
      RawTerm.OnCanonicalPath term intermediate

/-- Every canonically-visited term is genuinely reachable. -/
theorem RawTerm.OnCanonicalPath.toStepStar {scope : Nat}
    {term intermediate : RawTerm scope}
    (path : RawTerm.OnCanonicalPath term intermediate) :
    StepStar term intermediate := by
  induction path with
  | here visitedTerm => exact StepStar.refl visitedTerm
  | there fireStep _restPath restToStepStar =>
      exact StepStar.trans (RawTerm.reduceOnce_sound fireStep) restToStepStar

/-! ## ★ The computable space bound -/

/-- ★ **The computable kernel space bound**: the SUM of the term sizes
along the canonical evaluation path (`Acc.rec`, constant `Nat` motive).
The sum dominates the maximum intermediate size — the propext-free
SUM-bound discipline. -/
def RawTerm.spaceBound {scope : Nat} (term : RawTerm scope)
    (accessible : Acc (@StepStar.StepSuccessor scope) term) : Nat :=
  Acc.rec (motive := fun _currentTerm _acc => Nat)
    (fun currentTerm _accStep spaceRec =>
      match hReduce : RawTerm.reduceOnce currentTerm with
      | none => RawTerm.size currentTerm
      | some reduct =>
          RawTerm.size currentTerm
            + spaceRec reduct (RawTerm.reduceOnce_sound hReduce))
    accessible

/-- One-step unfolding of `spaceBound` at an `Acc.intro` witness (rfl). -/
theorem RawTerm.spaceBound_unfold {scope : Nat} (term : RawTerm scope)
    (accStep : ∀ later, StepStar.StepSuccessor later term →
      Acc StepStar.StepSuccessor later) :
    RawTerm.spaceBound term (.intro term accStep) =
      (match hReduce : RawTerm.reduceOnce term with
        | none => RawTerm.size term
        | some reduct =>
            RawTerm.size term
              + RawTerm.spaceBound reduct
                  (accStep reduct (RawTerm.reduceOnce_sound hReduce))) := rfl

/-- ★ **Space soundness**: EVERY term the canonical evaluation visits has
size at most `spaceBound`.  By `Acc`-induction: the visited start is one
summand; a deeper visit lands in the recursive summand (the firing
equations are reconciled by `Option.some` injectivity). -/
theorem RawTerm.spaceBound_isSound {scope : Nat} {term : RawTerm scope}
    (accessible : Acc (@StepStar.StepSuccessor scope) term) :
    ∀ {intermediate : RawTerm scope},
      RawTerm.OnCanonicalPath term intermediate →
      RawTerm.size intermediate ≤ RawTerm.spaceBound term accessible := by
  induction accessible with
  | intro currentTerm accStep ih =>
      intro intermediate path
      rw [RawTerm.spaceBound_unfold currentTerm accStep]
      split
      · next haltEq =>
          cases path with
          | here _ => exact Nat.le_refl _
          | there fireStep _restPath =>
              exact nomatch fireStep.symm.trans haltEq
      · next firedReduct firedEq =>
          cases path with
          | here _ => exact Nat.le_add_right _ _
          | there fireStep restPath =>
              injection fireStep.symm.trans firedEq with reductEq
              rw [reductEq] at restPath
              exact Nat.le_trans
                (ih firedReduct (RawTerm.reduceOnce_sound firedEq) restPath)
                (Nat.le_add_left _ _)

/-- The input itself is space-bounded (it is on its own canonical path). -/
theorem RawTerm.size_le_spaceBound {scope : Nat} (term : RawTerm scope)
    (accessible : Acc (@StepStar.StepSuccessor scope) term) :
    RawTerm.size term ≤ RawTerm.spaceBound term accessible :=
  RawTerm.spaceBound_isSound accessible (.here term)

/-- The normalizer's output is on the canonical path (it is the path's
endpoint, by the same `Acc`-induction that defines the normalizer). -/
theorem RawTerm.normalize_onCanonicalPath {scope : Nat} (term : RawTerm scope)
    (accessible : Acc (@StepStar.StepSuccessor scope) term) :
    RawTerm.OnCanonicalPath term (RawTerm.normalize term accessible) := by
  induction accessible with
  | intro currentTerm accStep ih =>
      rw [RawTerm.normalize_unfold currentTerm accStep]
      split
      · exact RawTerm.OnCanonicalPath.here currentTerm
      · next reduct hReduce =>
          exact RawTerm.OnCanonicalPath.there hReduce
            (ih reduct (RawTerm.reduceOnce_sound hReduce))

/-- THE normal form is space-bounded: evaluation never needs more space
than `spaceBound`, including for its final result. -/
theorem RawTerm.normalize_size_le_spaceBound {scope : Nat} (term : RawTerm scope)
    (accessible : Acc (@StepStar.StepSuccessor scope) term) :
    RawTerm.size (RawTerm.normalize term accessible)
      ≤ RawTerm.spaceBound term accessible :=
  RawTerm.spaceBound_isSound accessible
    (RawTerm.normalize_onCanonicalPath term accessible)

/-! ## Non-vacuity — the space bound computes and is engaged -/

/-- **The bound computes**: the normal form `unit` has space bound exactly
its own size (one node) — kernel evaluation through the concrete
`Acc.intro` witness. -/
theorem RawTerm.spaceBound_unit_isOne :
    RawTerm.spaceBound unitNormalFormFixture unitNormalFormFixture_accessible = 1 := rfl

/-- The identity-β fixture's canonical evaluation visits `unit` (the
root redex fires by kernel computation, then halts). -/
theorem identityBetaFixture_canonicalPathReachesUnit :
    RawTerm.OnCanonicalPath identityBetaFixture unitNormalFormFixture :=
  RawTerm.OnCanonicalPath.there
    (rfl : RawTerm.reduceOnce identityBetaFixture = some unitNormalFormFixture)
    (RawTerm.OnCanonicalPath.here unitNormalFormFixture)

/-- **The bound is honest on a genuine redex**: both endpoints of the
identity-β fixture's canonical evaluation — the redex itself and the
value `unit` it computes to — are size-bounded by its space bound. -/
theorem identityBetaFixture_spaceBound_boundsBothEndpoints :
    RawTerm.size identityBetaFixture
        ≤ RawTerm.spaceBound identityBetaFixture identityBetaFixture_accessible
      ∧ RawTerm.size unitNormalFormFixture
        ≤ RawTerm.spaceBound identityBetaFixture identityBetaFixture_accessible :=
  ⟨RawTerm.size_le_spaceBound identityBetaFixture identityBetaFixture_accessible,
   RawTerm.spaceBound_isSound identityBetaFixture_accessible
     identityBetaFixture_canonicalPathReachesUnit⟩

end FX1Poly.Core
