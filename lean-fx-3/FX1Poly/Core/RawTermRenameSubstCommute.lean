import FX1Poly.Core.RawTermRenameComposeFusion
import FX1Poly.Core.RawTermSubstPointwise

/-! # Foundation/PolyCell/Core/RawTermRenameSubstCommute — rename-then-subst commute

This file ships the **first cross-direction commute lemma**:

  RawTerm.subst sigma (RawTerm.rename rho term)
    = RawTerm.subst (rho.thenSubst sigma) term

— "renaming-then-substituting equals substituting via the
pre-composed (renaming-then-lookup) substitution".

Position in the cross-direction fusion ladder:

  rename_pointwise            (#181c1, shipped)
  rename's lift_compose etc.  (#181c2, shipped)
  payload_cast_compose keystone + rename_compose  (#181c3, shipped)
  rename_subst_commute        (THIS COMMIT)
  subst_rename_commute        (next)
  subst's lift_compose etc.   (after)
  subst_compose               (the headline)
  Action RawTermSubst instance  (closes V2-L2.7)

## Why this is the SIMPLER cross-direction lemma

v1's `RawTerm.rename_subst_commute` uses an auxiliary
`RawTermSubst.lift_renaming_pull` whose proof at both Fin cases is
`rfl` — purely definitional.

The OTHER direction `subst_rename_commute` needs an auxiliary
`RawTermSubst.lift_then_rename_lift` that uses `rename_compose`
PLUS another helper `RawRenaming.weaken_lift_commute`.  More
infrastructure.

So shipping `rename_subst_commute` FIRST is the natural pacing:
* The binder-level pull (`lift_thenSubst_pull`) closes by `rfl`.
* The iterated pull (`iterateLiftRaw_thenSubst_pointwise`) is a
  Nat induction with the standard 2-rewrite succ-case.
* The mutual term theorem uses the now-established 4-arm template
  (var arm `rfl`, non-var arm double-unfold + cast keystone +
  children IH, cons arm head bridge + tail IH).

`subst_rename_commute` ships next, after this commit's
infrastructure is in hand.

## The bridge substitution

  RawRenaming.thenSubst rho sigma pos = sigma (rho pos)

A `RawTermSubst src tgt` constructed from a renaming
`rho : RawRenaming src mid` and a substitution
`sigma : RawTermSubst mid tgt`.  Conceptually:
"first rename, then substitute".

Named under `FX1Poly.Core.RawRenaming.thenSubst`
(v2 namespace; v1's `FX1Poly.Foundation.RawRenaming` is not modified).

## Zero-axiom verification

All declarations propext-free, following the recipe established
across #181a-c3:
* `RawRenaming.thenSubst` — `@[reducible]` definition.
* `RawRenaming.lift_thenSubst_pull` — Fin pattern match, both
  branches `rfl` (lift on both sigma and rho reduces to thenSubst-lift
  uniformly).
* `iterateLiftRaw_RawRenaming_thenSubst_pointwise` — Nat induction
  with `lift_pointwise` (subst-side, from #181a) and
  `lift_thenSubst_pull` chain.
* Mutual `RawTerm.rename_subst_commute` /
  `RawTermChildren.rename_subst_commute` — `dsimp only [fold]`
  (not `unfold` — Quot.sound trap), `simp only [dif_neg hVar]`,
  `congr 1` + cast keystone (#181c3) + mutual IH + iterated bridge
  at children spine.

Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`.

## v1 comparison

v1's `RawTerm.rename_subst_commute` (Foundation/RawSubst/
SubstLemmas.lean lines 212-310) is a 74-arm structural induction.
v2's version is a 4-arm mutual induction.  Cascade-tax ratio
preserved at ~18x.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-! ## Section 1 — The pre-composition bridge

`thenSubst` is the substitution that arises when factoring a
rename-then-subst pair through a single substitution. -/

/-- Pre-compose a renaming with a substitution: at position `pos`,
look up `sigma` at `rho pos` (the renamed position).

Used by `rename_subst_commute` to factor `(term.rename rho).subst
sigma` through a single substitution.

`@[reducible]` so the `lift_thenSubst_pull` proof can close by `rfl`. -/
@[reducible] def RawRenaming.thenSubst
    {sourceScope middleScope targetScope : Nat}
    (rawRenaming : FX1Poly.Foundation.RawRenaming sourceScope middleScope)
    (someSubstitution : RawTermSubst middleScope targetScope) :
    RawTermSubst sourceScope targetScope :=
  fun position => someSubstitution (rawRenaming position)

/-! ## Section 2 — Binder-level pull: lift sigma after lift rho = lift thenSubst

The substitution `(rho.lift).thenSubst (sigma.lift)`, which
substitutes via `sigma.lift` at the rho-lift-renamed position, agrees
pointwise with the lifted version of `(rho.thenSubst sigma)`.

This is the binder-level fact that makes the cons case of
`rename_subst_commute` work. -/

/-- Binder-level pull: lifting the bridge commutes with composing
the lifts.

At position ⟨0, _⟩: both sides reduce to `mkGen .gen_var ⟨0, _⟩
.childNil` (the fresh var).
At position ⟨k+1, _⟩: both sides reduce to
`RawTerm.weaken (sigma (rho ⟨k, _⟩))`.

Both close by `rfl` — `RawRenaming.lift`, `RawTermSubst.lift`,
and `RawRenaming.thenSubst` are all `@[reducible]` so the Lean
kernel reduces uniformly under both Fin arms. -/
theorem RawRenaming.lift_thenSubst_pull
    {sourceScope middleScope targetScope : Nat}
    (rawRenaming : FX1Poly.Foundation.RawRenaming sourceScope middleScope)
    (someSubstitution : RawTermSubst middleScope targetScope) :
    RawTermSubst.PointwiseEq
        (fun position => someSubstitution.lift (rawRenaming.lift position))
        (RawRenaming.thenSubst rawRenaming someSubstitution).lift := by
  intro position
  match position with
  | ⟨0, _⟩ => rfl
  | ⟨_priorPositionValue + 1, _⟩ => rfl

/-! ## Section 3 — Iterated lift of the bridge

Nat induction lifting `lift_thenSubst_pull` through arbitrary binder
depths.  Needed at each `childCons` spine descent in
`rename_subst_commute`. -/

/-- Iterated lift commutes with the renaming-then-substitution
bridge (pointwise).

  iterateLiftRaw (rho.thenSubst sigma) depth ≅
    fun pos => (iterateLiftRaw sigma depth) ((iterateLiftRaw rho depth) pos)

Inducts on `binderDepth`:
* `zero`: both reduce to `rho.thenSubst sigma` definitionally.
* `succ priorDepth`: chains
  - `lift_pointwise priorIH` (#181a, lifts the IH through one binder)
  - `lift_thenSubst_pull` (this file, pulls the lift inside)
  via two rewrites. -/
theorem iterateLiftRaw_RawRenaming_thenSubst_pointwise
    {sourceScope middleScope targetScope : Nat}
    (rawRenaming : FX1Poly.Foundation.RawRenaming sourceScope middleScope)
    (someSubstitution : RawTermSubst middleScope targetScope)
    (binderDepth : Nat) :
    RawTermSubst.PointwiseEq
        (iterateLiftRaw
            (RawRenaming.thenSubst rawRenaming someSubstitution) binderDepth)
        (fun position =>
            (iterateLiftRaw someSubstitution binderDepth)
              ((iterateLiftRaw rawRenaming binderDepth) position)) := by
  induction binderDepth with
  | zero =>
      -- Both sides equal `rho.thenSubst sigma` (since iter _ 0 = _).
      exact RawTermSubst.PointwiseEq.refl _
  | succ _priorDepth priorIH =>
      -- iter (k+1) = lift (iter k) on each iterate.
      intro position
      show RawTermSubst.lift
              (iterateLiftRaw
                  (RawRenaming.thenSubst rawRenaming someSubstitution) _priorDepth)
              position =
            RawTermSubst.lift
                (iterateLiftRaw someSubstitution _priorDepth)
              (RawRenaming.lift
                (iterateLiftRaw rawRenaming _priorDepth) position)
      -- Chain:
      --   lift (iter (rho.thenSubst sigma) k)
      --     ≅ lift ((iter rho k).thenSubst (iter sigma k))   -- by lift_pointwise priorIH
      --     ≅ (iter sigma k).lift on (iter rho k).lift _     -- by lift_thenSubst_pull (symm)
      rw [RawTermSubst.lift_pointwise priorIH position]
      exact (RawRenaming.lift_thenSubst_pull
              (iterateLiftRaw rawRenaming _priorDepth)
              (iterateLiftRaw someSubstitution _priorDepth) position).symm

/-! ## Section 4 — The term-level commute (mutual)

In v1: 74-arm structural induction.
In v2: 4-arm mutual induction reusing fold's dispatch + the cast
keystone + the iterated bridge above. -/

mutual

/-- Rename-then-subst commutes through a pre-composed substitution.

This is the v2 replacement for v1's 74-arm
`RawTerm.rename_subst_commute`. -/
theorem RawTerm.rename_subst_commute
    {sourceScope middleScope targetScope : Nat}
    (rawRenaming : FX1Poly.Foundation.RawRenaming sourceScope middleScope)
    (someSubstitution : RawTermSubst middleScope targetScope)
    (sourceTerm : RawTerm sourceScope) :
    RawTerm.subst someSubstitution
        (RawTerm.rename rawRenaming sourceTerm) =
      RawTerm.subst
        (RawRenaming.thenSubst rawRenaming someSubstitution) sourceTerm := by
  match sourceTerm with
  | .mkGen someGenerator somePayload someChildren =>
    by_cases hVar : someGenerator = .gen_var
    case pos =>
      subst hVar
      -- Variable arm: LHS = subst sigma (mkGen .gen_var (rho p) .childNil)
      --                   = sigma (rho p)
      -- RHS = subst (rho.thenSubst sigma) (mkGen .gen_var p .childNil)
      --     = (rho.thenSubst sigma) p = sigma (rho p).  Both rfl.
      match someChildren with
      | .childNil => rfl
    case neg =>
      -- Non-variable arm: double-unfold + congr + cast keystone +
      -- children IH.
      show RawTerm.subst someSubstitution
              (RawTerm.rename rawRenaming
                  (.mkGen someGenerator somePayload someChildren)) =
            RawTerm.subst
              (RawRenaming.thenSubst rawRenaming someSubstitution)
              (.mkGen someGenerator somePayload someChildren)
      -- Pass 1: unfold outer subst + inner rename's fold + algebra.
      dsimp only [RawTerm.subst, RawTerm.rename, fold,
                  GenAlgebra.canonical]
      simp only [dif_neg hVar]
      -- Pass 2: unfold the outer fold over the fresh mkGen from inner.
      dsimp only [fold, GenAlgebra.canonical]
      simp only [dif_neg hVar]
      -- Both sides flat: mkGen g (cast) (foldChildren ...) form.
      congr 1
      · -- Cast composition keystone (chained rename's eq_src_mid then
        -- subst's eq_mid_tgt = single eq_src_tgt).
        exact Generator.payload_cast_compose hVar
                sourceScope middleScope targetScope somePayload
      · -- Children fusion via mutual IH.
        exact RawTermChildren.rename_subst_commute
                rawRenaming someSubstitution someChildren

/-- Rename-then-subst commute on children spines.

In the cons case, the head is under `headShift` binders.  The
mutual head IH at the lifted scopes gives:

  subst (iter sigma shift) (rename (iter rho shift) head)
    = subst ((iter rho shift).thenSubst (iter sigma shift)) head

The bridge via `iterateLiftRaw_RawRenaming_thenSubst_pointwise`
(symmetric direction + subst_pointwise from #181a) converts this to
`subst (iter (rho.thenSubst sigma) shift) head`. -/
theorem RawTermChildren.rename_subst_commute
    {sourceScope middleScope targetScope : Nat}
    (rawRenaming : FX1Poly.Foundation.RawRenaming sourceScope middleScope)
    (someSubstitution : RawTermSubst middleScope targetScope)
    {binderShifts : List Nat}
    (someChildren : RawTermChildren binderShifts sourceScope) :
    RawTermChildren.subst someSubstitution
        (RawTermChildren.rename rawRenaming someChildren) =
      RawTermChildren.subst
        (RawRenaming.thenSubst rawRenaming someSubstitution) someChildren := by
  match binderShifts, someChildren with
  | [], .childNil =>
      rfl
  | headShift :: _, .childCons childHead childTail =>
      show RawTermChildren.childCons
              (RawTerm.subst (iterateLiftRaw someSubstitution headShift)
                  (RawTerm.rename (iterateLiftRaw rawRenaming headShift)
                      childHead))
              (RawTermChildren.subst someSubstitution
                  (RawTermChildren.rename rawRenaming childTail)) =
            RawTermChildren.childCons
              (RawTerm.subst
                  (iterateLiftRaw
                      (RawRenaming.thenSubst rawRenaming someSubstitution) headShift)
                  childHead)
              (RawTermChildren.subst
                  (RawRenaming.thenSubst rawRenaming someSubstitution) childTail)
      have headCommute := RawTerm.rename_subst_commute
                            (iterateLiftRaw rawRenaming headShift)
                            (iterateLiftRaw someSubstitution headShift)
                            childHead
      -- headCommute :
      --   subst (iter sigma shift) (rename (iter rho shift) head) =
      --   subst ((iter rho shift).thenSubst (iter sigma shift)) head
      have iterBridgeForward :=
        iterateLiftRaw_RawRenaming_thenSubst_pointwise
          rawRenaming someSubstitution headShift
      -- iterBridgeForward :
      --   iter (rho.thenSubst sigma) shift ≅
      --   (iter sigma shift).comp (iter rho shift)
      -- We need symmetric: (iter rho shift).thenSubst (iter sigma shift)
      -- = (iter sigma shift).comp (iter rho shift) is just defn.
      have headBridge :
          RawTerm.subst
              (RawRenaming.thenSubst
                  (iterateLiftRaw rawRenaming headShift)
                  (iterateLiftRaw someSubstitution headShift))
              childHead =
            RawTerm.subst
              (iterateLiftRaw
                  (RawRenaming.thenSubst rawRenaming someSubstitution) headShift)
              childHead :=
        RawTerm.subst_pointwise
          (fun position => (iterBridgeForward position).symm)
          childHead
      have tailCommute :=
        RawTermChildren.rename_subst_commute
          rawRenaming someSubstitution childTail
      rw [headCommute, headBridge, tailCommute]

end -- mutual

/-! ## Section 5 — Smoke tests -/

/-- Smoke: rename_subst_commute on `.gen_unit` (no variables — both
sides reduce to a fresh `gen_unit`). -/
theorem RawTerm.rename_subst_commute_unit_smoke
    {sourceScope middleScope targetScope : Nat}
    (rawRenaming : FX1Poly.Foundation.RawRenaming sourceScope middleScope)
    (someSubstitution : RawTermSubst middleScope targetScope) :
    RawTerm.subst someSubstitution
        (RawTerm.rename rawRenaming
            (.mkGen .gen_unit () .childNil : RawTerm sourceScope)) =
      RawTerm.subst
        (RawRenaming.thenSubst rawRenaming someSubstitution)
        (.mkGen .gen_unit () .childNil : RawTerm sourceScope) :=
  RawTerm.rename_subst_commute rawRenaming someSubstitution _

/-- Smoke: rename_subst_commute on `.gen_var` at position 0 —
exercises the variable arm. -/
theorem RawTerm.rename_subst_commute_var_smoke
    {sourceScope middleScope targetScope : Nat}
    (rawRenaming :
        FX1Poly.Foundation.RawRenaming (sourceScope + 1) (middleScope + 1))
    (someSubstitution :
        RawTermSubst (middleScope + 1) (targetScope + 1)) :
    RawTerm.subst someSubstitution
        (RawTerm.rename rawRenaming
            (.mkGen .gen_var
                    (⟨0, Nat.zero_lt_succ sourceScope⟩ : Fin (sourceScope + 1))
                    .childNil)) =
      RawTerm.subst
        (RawRenaming.thenSubst rawRenaming someSubstitution)
        (.mkGen .gen_var
                (⟨0, Nat.zero_lt_succ sourceScope⟩ : Fin (sourceScope + 1))
                .childNil) :=
  RawTerm.rename_subst_commute rawRenaming someSubstitution _

end FX1Poly.Core
