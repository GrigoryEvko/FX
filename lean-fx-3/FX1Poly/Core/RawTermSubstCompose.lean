import FX1Poly.Core.RawTermSubstRenameCommute

/-! # Foundation/PolyCell/Core/RawTermSubstCompose — substitution composition law

The **third Action law** at the term layer:

  (term.subst sigma1).subst sigma2 = term.subst (sigma1.compose sigma2)

— the polynomial monad's **multiplication law**.

## The three Action laws

  1. apply_ext      / subst_pointwise
  2. identity_apply / subst_identity
  3. compose_assoc  / subst_compose   (this file)

## Architectural payoff: the polynomial monad fundamental theorem

`subst_compose` is the multiplication law of the polynomial monad
view of substitution:

  μ_X ∘ μ_X = μ_X ∘ T_μ_X     (in monad notation)
  (term.subst sigma1).subst sigma2 = term.subst (sigma1.compose sigma2)
                                                          ^^^^^^^
                                              composition INSIDE the monad

The Allais ICFP'18 framework says this follows from a SINGLE
structural induction over the term + the binder pull identity:
the 4-arm mutual induction suffices, with the binder pull
(lift_compose_pointwise) doing the substantive cross-direction
work.

## The binder pull: lift_compose_pointwise

The most subtle step: at the lifted scope, the composed substitution
`(compose sigma1 sigma2).lift` agrees pointwise with `compose
sigma1.lift sigma2.lift`.

At ⟨0, _⟩: both reduce to the fresh `gen_var 0` — `rfl`.

At ⟨k+1, h⟩: the proof uses BOTH cross-direction commutes:
* `subst_rename_commute` on the LHS to flatten
  `rename weaken (subst sigma2 X)` into `subst (postRename sigma2 weaken) X`.
* `rename_subst_commute` on the RHS to flatten
  `subst sigma2.lift (rename weaken X)` into `subst (thenSubst weaken sigma2.lift) X`.
* `subst_pointwise` to close from pointwise eq of
  `postRename sigma2 weaken` vs `thenSubst weaken sigma2.lift`.

The latter pointwise eq is `rfl` per Fin position: both produce
`rename weaken (sigma2 ⟨n, _⟩)` — one by the definition of
`postRename`, the other by the definition of `thenSubst` plus
`lift`'s successor branch.

## The mutual `subst_compose` theorem

A 4-arm mutual induction:
* var arm = `rfl` (both reduce to `subst sigma2 (sigma1 pos)`).
* non-var arm = double-unfold + congr + payload_cast_compose +
  children IH.
* childNil = `rfl`.
* childCons = head IH at lifted scopes, bridge via
  iterateLiftRaw_compose_pointwise (.symm) + subst_pointwise,
  tail IH.

## Zero-axiom verification

All declarations propext-free:
* `RawTermSubst.compose` — `@[reducible]` def.
* `RawTermSubst.lift_compose_pointwise` — Fin pattern match;
  `⟨0,_⟩` rfl, `⟨k+1,_⟩` uses BOTH cross-direction commutes.
* `iterateLiftRaw_RawTermSubst_compose_pointwise` — Nat induction.
* Mutual `subst_compose` — standard 4-arm template.

Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`.

Adding a new term former costs ZERO new lines here, since the
Generator dispatch is amortized into fold.

The `Action RawTermSubst` instance cites the three laws:
compose_assoc from this file, plus identity_apply and apply_ext.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-! ## Section 1 — The substitution composition

The polynomial monad's multiplication operation, at the
substitution layer. -/

/-- Compose two substitutions: at position `pos`, look up `sigma1`
at `pos` (yielding a term in the middle scope), then substitute via
`sigma2` (yielding a term in the target scope).

`@[reducible]` so binder-level proofs can close after dsimp.

Conceptually: the polynomial-monad multiplication
`mu_RawTerm : T(T X) -> T X` at the data level. -/
@[reducible] def RawTermSubst.compose
    {sourceScope middleScope targetScope : Nat}
    (firstSubstitution : RawTermSubst sourceScope middleScope)
    (secondSubstitution : RawTermSubst middleScope targetScope) :
    RawTermSubst sourceScope targetScope :=
  fun position =>
    RawTerm.subst secondSubstitution (firstSubstitution position)

/-! ## Section 2 — The binder pull (the cross-direction step)

The most subtle step in the polynomial monad multiplication: lifting
a composed substitution under a binder agrees pointwise with
composing the lifts.

This binder pull uses BOTH cross-direction commutes
(subst_rename_commute and rename_subst_commute) plus
subst_pointwise. -/

/-- Lift commutes with substitution composition (pointwise).

  lift (compose sigma1 sigma2) ≅ compose sigma1.lift sigma2.lift

At ⟨0, _⟩: both sides reduce to `mkGen .gen_var ⟨0, _⟩ .childNil`.
At ⟨k+1, _⟩: uses BOTH cross-direction commutes plus
subst_pointwise.

The proof at ⟨k+1, _⟩:
* Unfold lift, compose, weaken on both sides.
* LHS becomes `rename weaken (subst sigma2 (sigma1 ⟨k, _⟩))`.
  Apply `subst_rename_commute`: → `subst (postRename sigma2 weaken)
  (sigma1 ⟨k, _⟩)`.
* RHS becomes `subst sigma2.lift (rename weaken (sigma1 ⟨k, _⟩))`.
  Apply `rename_subst_commute`: → `subst (thenSubst weaken sigma2.lift)
  (sigma1 ⟨k, _⟩)`.
* By `subst_pointwise`, suffices to show pointwise eq of
  `postRename sigma2 weaken` vs `thenSubst weaken sigma2.lift`.
  Both produce `rename weaken (sigma2 ⟨val, _⟩)` per Fin position
  (the former by `postRename`'s defn, the latter by `thenSubst` +
  `lift`'s successor branch).  Closes by `cases p; rfl`. -/
theorem RawTermSubst.lift_compose_pointwise
    {sourceScope middleScope targetScope : Nat}
    (firstSubstitution : RawTermSubst sourceScope middleScope)
    (secondSubstitution : RawTermSubst middleScope targetScope) :
    RawTermSubst.PointwiseEq
        (RawTermSubst.compose firstSubstitution secondSubstitution).lift
        (RawTermSubst.compose
            firstSubstitution.lift secondSubstitution.lift) := by
  intro position
  match position with
  | ⟨0, _⟩ => rfl
  | ⟨priorPositionValue + 1, hBound⟩ =>
      -- Unfold lift, compose, and weaken on both sides.
      dsimp only [RawTermSubst.lift, RawTermSubst.compose,
                  RawTerm.weaken]
      -- LHS: rename weaken (subst sigma2 (sigma1 ⟨k, _⟩))
      -- RHS: subst sigma2.lift (rename weaken (sigma1 ⟨k, _⟩))
      -- Apply the cross-direction commutes to flatten both into
      -- single substs.
      rw [RawTerm.subst_rename_commute secondSubstitution
            FX1Poly.Foundation.RawRenaming.weaken
            (firstSubstitution
                ⟨priorPositionValue, Nat.lt_of_succ_lt_succ hBound⟩),
          RawTerm.rename_subst_commute FX1Poly.Foundation.RawRenaming.weaken
            secondSubstitution.lift
            (firstSubstitution
                ⟨priorPositionValue, Nat.lt_of_succ_lt_succ hBound⟩)]
      -- Goal: subst (postRename sigma2 weaken) (sigma1 ⟨k, _⟩) =
      --       subst (thenSubst weaken sigma2.lift) (sigma1 ⟨k, _⟩)
      apply RawTerm.subst_pointwise
      intro pointwisePosition
      match pointwisePosition with
      | ⟨_, _⟩ => rfl

/-! ## Section 3 — Iterated lift of compose

Nat induction extending `lift_compose_pointwise` through arbitrary
binder depths.  Needed at each `childCons` spine descent in
`subst_compose`. -/

/-- Iterated lift commutes with substitution composition (pointwise).

  iter (compose sigma1 sigma2) depth ≅
    compose (iter sigma1 depth) (iter sigma2 depth)

Standard Nat induction; succ case chains lift_pointwise
with lift_compose_pointwise (this file). -/
theorem iterateLiftRaw_RawTermSubst_compose_pointwise
    {sourceScope middleScope targetScope : Nat}
    (firstSubstitution : RawTermSubst sourceScope middleScope)
    (secondSubstitution : RawTermSubst middleScope targetScope)
    (binderDepth : Nat) :
    RawTermSubst.PointwiseEq
        (iterateLiftRaw
            (RawTermSubst.compose firstSubstitution secondSubstitution)
            binderDepth)
        (RawTermSubst.compose
            (iterateLiftRaw firstSubstitution binderDepth)
            (iterateLiftRaw secondSubstitution binderDepth)) := by
  induction binderDepth with
  | zero =>
      exact RawTermSubst.PointwiseEq.refl _
  | succ _priorDepth priorIH =>
      intro position
      show RawTermSubst.lift
              (iterateLiftRaw
                  (RawTermSubst.compose firstSubstitution secondSubstitution)
                  _priorDepth)
              position =
            RawTermSubst.compose
              (RawTermSubst.lift
                  (iterateLiftRaw firstSubstitution _priorDepth))
              (RawTermSubst.lift
                  (iterateLiftRaw secondSubstitution _priorDepth))
              position
      rw [RawTermSubst.lift_pointwise priorIH position]
      exact RawTermSubst.lift_compose_pointwise
              (iterateLiftRaw firstSubstitution _priorDepth)
              (iterateLiftRaw secondSubstitution _priorDepth)
              position

/-! ## Section 4 — The mutual theorem

A 4-arm mutual induction using the standard template +
lift_compose_pointwise binder pull.

This is the polynomial monad's multiplication law at the term
layer. -/

mutual

/-- Substitution composition: applying two substitutions
sequentially equals applying the composed substitution once.

The polynomial monad multiplication law at the term layer.

  (term.subst sigma1).subst sigma2 = term.subst (sigma1.compose sigma2)
-/
theorem RawTerm.subst_compose
    {sourceScope middleScope targetScope : Nat}
    (firstSubstitution : RawTermSubst sourceScope middleScope)
    (secondSubstitution : RawTermSubst middleScope targetScope)
    (sourceTerm : RawTerm sourceScope) :
    RawTerm.subst secondSubstitution
        (RawTerm.subst firstSubstitution sourceTerm) =
      RawTerm.subst
        (RawTermSubst.compose firstSubstitution secondSubstitution)
        sourceTerm := by
  match sourceTerm with
  | .mkGen someGenerator somePayload someChildren =>
    by_cases hVar : someGenerator = .gen_var
    case pos =>
      -- Variable arm: LHS = subst sigma2 (subst sigma1 (mkGen .gen_var p .childNil))
      --                   = subst sigma2 (sigma1 p)
      -- RHS = subst (compose sigma1 sigma2) (mkGen .gen_var p .childNil)
      --     = (compose sigma1 sigma2) p = subst sigma2 (sigma1 p).
      -- Both equal `subst sigma2 (sigma1 p)` definitionally.
      subst hVar
      match someChildren with
      | .childNil => rfl
    case neg =>
      -- Non-variable arm: now-standard 4-arm template.
      show RawTerm.subst secondSubstitution
              (RawTerm.subst firstSubstitution
                  (.mkGen someGenerator somePayload someChildren)) =
            RawTerm.subst
              (RawTermSubst.compose firstSubstitution secondSubstitution)
              (.mkGen someGenerator somePayload someChildren)
      -- Pass 1: unfold both subst calls one layer.
      dsimp only [RawTerm.subst, fold, GenAlgebra.canonical]
      simp only [dif_neg hVar]
      -- Pass 2: unfold the outer subst over the fresh mkGen from inner.
      dsimp only [fold, GenAlgebra.canonical]
      simp only [dif_neg hVar]
      -- Both sides flat; congr 1 peels off mkGen.
      congr 1
      · -- Cast composition keystone.
        exact Generator.payload_cast_compose hVar
                sourceScope middleScope targetScope somePayload
      · -- Children fusion via mutual IH.
        exact RawTermChildren.subst_compose
                firstSubstitution secondSubstitution someChildren

/-- Substitution composition on children spines.

In the cons case, the head is under `headShift` binders.  The
mutual head IH at the lifted scopes + bridge via
`iterateLiftRaw_RawTermSubst_compose_pointwise` (.symm) +
subst_pointwise closes. -/
theorem RawTermChildren.subst_compose
    {sourceScope middleScope targetScope : Nat}
    (firstSubstitution : RawTermSubst sourceScope middleScope)
    (secondSubstitution : RawTermSubst middleScope targetScope)
    {binderShifts : List Nat}
    (someChildren : RawTermChildren binderShifts sourceScope) :
    RawTermChildren.subst secondSubstitution
        (RawTermChildren.subst firstSubstitution someChildren) =
      RawTermChildren.subst
        (RawTermSubst.compose firstSubstitution secondSubstitution)
        someChildren := by
  match binderShifts, someChildren with
  | [], .childNil =>
      rfl
  | headShift :: _, .childCons childHead childTail =>
      show RawTermChildren.childCons
              (RawTerm.subst (iterateLiftRaw secondSubstitution headShift)
                  (RawTerm.subst (iterateLiftRaw firstSubstitution headShift)
                      childHead))
              (RawTermChildren.subst secondSubstitution
                  (RawTermChildren.subst firstSubstitution childTail)) =
            RawTermChildren.childCons
              (RawTerm.subst
                  (iterateLiftRaw
                      (RawTermSubst.compose firstSubstitution
                          secondSubstitution)
                      headShift)
                  childHead)
              (RawTermChildren.subst
                  (RawTermSubst.compose firstSubstitution
                      secondSubstitution)
                  childTail)
      have headFusion := RawTerm.subst_compose
                            (iterateLiftRaw firstSubstitution headShift)
                            (iterateLiftRaw secondSubstitution headShift)
                            childHead
      have iterBridgeForward :=
        iterateLiftRaw_RawTermSubst_compose_pointwise
          firstSubstitution secondSubstitution headShift
      have headBridge :
          RawTerm.subst
              (RawTermSubst.compose
                  (iterateLiftRaw firstSubstitution headShift)
                  (iterateLiftRaw secondSubstitution headShift))
              childHead =
            RawTerm.subst
              (iterateLiftRaw
                  (RawTermSubst.compose firstSubstitution
                      secondSubstitution)
                  headShift)
              childHead :=
        RawTerm.subst_pointwise
          (fun position => (iterBridgeForward position).symm)
          childHead
      have tailFusion :=
        RawTermChildren.subst_compose
          firstSubstitution secondSubstitution childTail
      rw [headFusion, headBridge, tailFusion]

end -- mutual

/-! ## Section 5 — Smoke tests -/

/-- Smoke: subst_compose on `.gen_unit` — both sides reduce to a
fresh `gen_unit` (no variables, no substitution application). -/
theorem RawTerm.subst_compose_unit_smoke
    {sourceScope middleScope targetScope : Nat}
    (firstSubstitution : RawTermSubst sourceScope middleScope)
    (secondSubstitution : RawTermSubst middleScope targetScope) :
    RawTerm.subst secondSubstitution
        (RawTerm.subst firstSubstitution
            (.mkGen .gen_unit () .childNil : RawTerm sourceScope)) =
      RawTerm.subst
        (RawTermSubst.compose firstSubstitution secondSubstitution)
        (.mkGen .gen_unit () .childNil : RawTerm sourceScope) :=
  RawTerm.subst_compose firstSubstitution secondSubstitution _

/-- Smoke: subst_compose on `.gen_var` at position 0 — exercises
the variable arm.  Both LHS and RHS reduce to
`subst sigma2 (sigma1 ⟨0, _⟩)`. -/
theorem RawTerm.subst_compose_var_smoke
    {sourceScope middleScope targetScope : Nat}
    (firstSubstitution :
        RawTermSubst (sourceScope + 1) (middleScope + 1))
    (secondSubstitution :
        RawTermSubst (middleScope + 1) (targetScope + 1)) :
    RawTerm.subst secondSubstitution
        (RawTerm.subst firstSubstitution
            (.mkGen .gen_var
                    (⟨0, Nat.zero_lt_succ sourceScope⟩ : Fin (sourceScope + 1))
                    .childNil)) =
      RawTerm.subst
        (RawTermSubst.compose firstSubstitution secondSubstitution)
        (.mkGen .gen_var
                (⟨0, Nat.zero_lt_succ sourceScope⟩ : Fin (sourceScope + 1))
                .childNil) :=
  RawTerm.subst_compose firstSubstitution secondSubstitution _

end FX1Poly.Core
