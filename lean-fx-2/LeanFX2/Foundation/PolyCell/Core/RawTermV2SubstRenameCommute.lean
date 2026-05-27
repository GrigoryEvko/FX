import LeanFX2.Foundation.PolyCell.Core.RawTermV2RenameSubstCommute

/-! # Foundation/PolyCell/Core/RawTermV2SubstRenameCommute — subst-then-rename commute

This file ships the **second cross-direction commute lemma**:

  RawTermV2.rename rho (RawTermV2.subst sigma term)
    = RawTermV2.subst (RawTermSubstV2.postRename sigma rho) term

— "substituting-then-renaming equals substituting via the
post-composed (substitute-then-rename-each-substituent)
substitution".

Position in the cross-direction fusion ladder:

  rename_pointwise            (#181c1, shipped)
  rename's lift_compose etc.  (#181c2, shipped)
  payload_cast_compose keystone + rename_compose  (#181c3, shipped)
  rename_subst_commute        (#181c4, shipped)
  subst_rename_commute        (THIS COMMIT)
  subst's lift_compose etc.   (next)
  subst_compose               (the headline — third Action law)
  Action RawTermSubstV2 instance  (closes V2-L2.7)

## Why this direction is structurally more complex

The OTHER direction `rename_subst_commute` (shipped #181c4) had a
binder pull lemma `lift_thenSubst_pull` whose proof closed by
`rfl` at both Fin cases — purely definitional.

This direction's binder pull lemma `lift_then_rename_lift_pull`
needs NON-TRIVIAL work at the `⟨k+1, h⟩` case:

  (sigma.lift ⟨k+1, h⟩).rename rho.lift
    = (weaken (sigma ⟨k, _⟩)).rename rho.lift
    = (sigma ⟨k, _⟩).rename (compose weaken rho.lift)    -- by rename_compose
    = (sigma ⟨k, _⟩).rename (compose rho weaken)         -- by rename_pointwise + weaken_lift_commute
    = (rename rho (sigma ⟨k, _⟩)).rename weaken          -- by rename_compose (reverse)
    = weaken (rename rho (sigma ⟨k, _⟩))
    = weaken ((postRename sigma rho) ⟨k, _⟩)
    = (postRename sigma rho).lift ⟨k+1, h⟩

So this binder pull uses:
* `RawTermV2.rename_compose` (#181c3 — shipped, just landed)
* `RawTermV2.rename_pointwise` (#181c1)
* `RawRenaming.weaken_lift_commute` (THIS FILE — trivial `fun _ => rfl`)

Hence we depend on the keystone + the rename ladder shipped earlier.

## The post-composition bridge

  RawTermSubstV2.postRename sigma rho pos = RawTermV2.rename rho (sigma pos)

A `RawTermSubstV2 src tgt` constructed from a substitution
`sigma : RawTermSubstV2 src mid` and a renaming
`rho : RawRenaming mid tgt`.  Conceptually: "substitute first,
then rename each substituent".

## Zero-axiom verification

All declarations propext-free, following the recipe established
across #181a-c4:
* `RawRenaming.weaken_lift_commute` — `fun _ => rfl`.
* `RawTermSubstV2.postRename` — `@[reducible]` def.
* `RawTermSubstV2.lift_then_rename_lift_pull` — Fin pattern match;
  `⟨0,_⟩` rfl, `⟨k+1,_⟩` uses dsimp + rename_compose (twice) +
  rename_pointwise + weaken_lift_commute.
* `iterateLiftRaw_RawTermSubstV2_postRename_pointwise` — Nat
  induction with lift_pointwise + lift_then_rename_lift_pull chain.
* Mutual `RawTermV2.subst_rename_commute` /
  `RawTermChildrenV2.subst_rename_commute` — `dsimp only [foldV2]`,
  `simp only [dif_neg hVar]`, `congr 1` + payload_cast_compose
  keystone + mutual IH + iterated bridge.

Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`.

## v1 comparison

v1's `RawTerm.subst_rename_commute` (Foundation/RawSubst/
SubstLemmas.lean lines 432-525) is a 74-arm structural induction.
v2's version is a 4-arm mutual induction.  Cascade-tax ratio
preserved at ~18x.
-/

namespace LeanFX2.Foundation.PolyCell.Core

open LeanFX2

/-! ## Section 1 — Weaken / Lift commute (binder-level rename)

The cleanest possible binder commute lemma: lifting a renaming
through one binder, then applying it to a weakened position, equals
weakening the result of applying the renaming.  Both sides reduce
definitionally to `Fin.succ (rho pos)`. -/

/-- Weaken composed with lift equals lift composed with weaken
(pointwise).

  rho.lift (weaken pos) = weaken (rho pos)

Closes by `fun _ => rfl` because:
* `weaken pos = Fin.succ pos`
* `rho.lift (Fin.succ pos) = Fin.succ (rho pos)` by lift's successor
  branch
* `weaken (rho pos) = Fin.succ (rho pos)` by weaken's defn -/
theorem RawRenaming.weaken_lift_commute
    {sourceScope targetScope : Nat}
    (rawRenaming : LeanFX2.RawRenaming sourceScope targetScope) :
    ∀ position : Fin sourceScope,
      rawRenaming.lift (LeanFX2.RawRenaming.weaken position) =
        LeanFX2.RawRenaming.weaken (rawRenaming position) :=
  fun _ => rfl

/-! ## Section 2 — The post-composition bridge

`postRename` is the substitution that arises when factoring a
subst-then-rename pair through a single substitution. -/

/-- Post-compose a substitution with a renaming: at position `pos`,
substitute via `sigma`, then rename the result via `rho`.

Used by `subst_rename_commute` to factor `(term.subst sigma).rename
rho` through a single substitution.

`@[reducible]` so binder-level proofs can close after dsimp. -/
@[reducible] def RawTermSubstV2.postRename
    {sourceScope middleScope targetScope : Nat}
    (someSubstitution : RawTermSubstV2 sourceScope middleScope)
    (rawRenaming : LeanFX2.RawRenaming middleScope targetScope) :
    RawTermSubstV2 sourceScope targetScope :=
  fun position =>
    RawTermV2.rename rawRenaming (someSubstitution position)

/-! ## Section 3 — Binder-level pull: lift-then-rename-lift

The substitution that first lifts sigma, then renames each
substituent via the LIFTED rho, agrees pointwise with the lifted
version of `postRename sigma rho`. -/

/-- Binder-level pull for subst-then-rename: lifting commutes with
the post-rename bridge.

* Position ⟨0, _⟩: both sides reduce to `mkGen .gen_var ⟨0, _⟩
  .childNil` (the fresh variable).  Closes by `rfl`.
* Position ⟨k+1, _⟩: uses `RawTermV2.rename_compose` (#181c3) twice
  and `weaken_lift_commute` (this file) plus `rename_pointwise`
  (#181c1) to convert
    (weaken (sigma ⟨k, _⟩)).rename rho.lift
  to
    weaken (rename rho (sigma ⟨k, _⟩)). -/
theorem RawTermSubstV2.lift_then_rename_lift_pull
    {sourceScope middleScope targetScope : Nat}
    (someSubstitution : RawTermSubstV2 sourceScope middleScope)
    (rawRenaming : LeanFX2.RawRenaming middleScope targetScope) :
    RawTermSubstV2.PointwiseEq
        (fun position =>
            RawTermV2.rename rawRenaming.lift (someSubstitution.lift position))
        (RawTermSubstV2.postRename someSubstitution rawRenaming).lift := by
  intro position
  match position with
  | ⟨0, _⟩ => rfl
  | ⟨priorPositionValue + 1, hBound⟩ =>
      -- Unfold lift and postRename to expose the underlying weaken /
      -- rename calls.
      dsimp only [RawTermSubstV2.lift, RawTermSubstV2.postRename,
                  RawTermV2.weaken]
      -- Goal now:
      --   rename rho.lift (rename weaken (sigma ⟨k, _⟩))
      --   = rename weaken (rename rho (sigma ⟨k, _⟩))
      -- Apply rename_compose on each side to fuse the two renames
      -- into single renames over composed renamings.
      rw [RawTermV2.rename_compose LeanFX2.RawRenaming.weaken
            rawRenaming.lift
            (someSubstitution ⟨priorPositionValue, Nat.lt_of_succ_lt_succ hBound⟩),
          RawTermV2.rename_compose rawRenaming
            LeanFX2.RawRenaming.weaken
            (someSubstitution ⟨priorPositionValue, Nat.lt_of_succ_lt_succ hBound⟩)]
      -- Goal:
      --   rename (compose weaken rho.lift) X
      --   = rename (compose rho weaken) X
      -- where X = sigma ⟨k, _⟩.
      -- By rename_pointwise, suffices to show pointwise eq of the
      -- two composed renamings; that's weaken_lift_commute.
      apply RawTermV2.rename_pointwise
      intro pointwisePosition
      exact RawRenaming.weaken_lift_commute rawRenaming pointwisePosition

/-! ## Section 4 — Iterated lift of the post-rename bridge

Nat induction lifting `lift_then_rename_lift_pull` through arbitrary
binder depths.  Needed at each `childCons` spine descent in
`subst_rename_commute`. -/

/-- Iterated lift commutes with the subst-then-rename bridge
(pointwise).

  iter (postRename sigma rho) depth ≅
    postRename (iter sigma depth) (iter rho depth)

Inducts on `binderDepth`:
* `zero`: both reduce to `postRename sigma rho` (since iter _ 0 = _).
* `succ priorDepth`: chains
  - `lift_pointwise priorIH` (#181a, lifts the IH through one binder)
  - `lift_then_rename_lift_pull` (this file, pulls the lift inside)
  via the standard 2-step pattern. -/
theorem iterateLiftRaw_RawTermSubstV2_postRename_pointwise
    {sourceScope middleScope targetScope : Nat}
    (someSubstitution : RawTermSubstV2 sourceScope middleScope)
    (rawRenaming : LeanFX2.RawRenaming middleScope targetScope)
    (binderDepth : Nat) :
    RawTermSubstV2.PointwiseEq
        (iterateLiftRaw
            (RawTermSubstV2.postRename someSubstitution rawRenaming)
            binderDepth)
        (RawTermSubstV2.postRename
            (iterateLiftRaw someSubstitution binderDepth)
            (iterateLiftRaw rawRenaming binderDepth)) := by
  induction binderDepth with
  | zero =>
      exact RawTermSubstV2.PointwiseEq.refl _
  | succ _priorDepth priorIH =>
      intro position
      show RawTermSubstV2.lift
              (iterateLiftRaw
                  (RawTermSubstV2.postRename someSubstitution rawRenaming)
                  _priorDepth)
              position =
            RawTermSubstV2.postRename
              (RawTermSubstV2.lift
                  (iterateLiftRaw someSubstitution _priorDepth))
              (RawRenaming.lift
                  (iterateLiftRaw rawRenaming _priorDepth))
              position
      rw [RawTermSubstV2.lift_pointwise priorIH position]
      exact (RawTermSubstV2.lift_then_rename_lift_pull
              (iterateLiftRaw someSubstitution _priorDepth)
              (iterateLiftRaw rawRenaming _priorDepth)
              position).symm

/-! ## Section 5 — The term-level commute (mutual)

In v1: 74-arm structural induction.
In v2: 4-arm mutual induction reusing foldV2 + payload_cast_compose
keystone + the iterated bridge above. -/

mutual

/-- Subst-then-rename commutes through a post-composed substitution.

This is the v2 replacement for v1's 74-arm
`RawTerm.subst_rename_commute`. -/
theorem RawTermV2.subst_rename_commute
    {sourceScope middleScope targetScope : Nat}
    (someSubstitution : RawTermSubstV2 sourceScope middleScope)
    (rawRenaming : LeanFX2.RawRenaming middleScope targetScope)
    (sourceTerm : RawTermV2 sourceScope) :
    RawTermV2.rename rawRenaming
        (RawTermV2.subst someSubstitution sourceTerm) =
      RawTermV2.subst
        (RawTermSubstV2.postRename someSubstitution rawRenaming)
        sourceTerm := by
  match sourceTerm with
  | .mkGen someGenerator somePayload someChildren =>
    by_cases hVar : someGenerator = .gen_var
    case pos =>
      -- Variable arm: LHS = rename rho (subst sigma (mkGen .gen_var p .childNil))
      --                   = rename rho (sigma p)
      -- RHS = subst (postRename sigma rho) (mkGen .gen_var p .childNil)
      --     = (postRename sigma rho) p = rename rho (sigma p).
      -- Both equal `rename rho (sigma p)` definitionally.
      subst hVar
      match someChildren with
      | .childNil => rfl
    case neg =>
      -- Non-variable arm: same template as #181c3 / #181c4.
      show RawTermV2.rename rawRenaming
              (RawTermV2.subst someSubstitution
                  (.mkGen someGenerator somePayload someChildren)) =
            RawTermV2.subst
              (RawTermSubstV2.postRename someSubstitution rawRenaming)
              (.mkGen someGenerator somePayload someChildren)
      -- Pass 1: unfold outer rename + inner subst's foldV2 + algebra.
      dsimp only [RawTermV2.rename, RawTermV2.subst, foldV2,
                  GenAlgebraV2.canonical]
      simp only [dif_neg hVar]
      -- Pass 2: unfold the outer foldV2 over the fresh mkGen.
      dsimp only [foldV2, GenAlgebraV2.canonical]
      simp only [dif_neg hVar]
      -- Both sides flat; congr 1 peels off mkGen.
      congr 1
      · -- Cast composition keystone (chained subst's eq_src_mid then
        -- rename's eq_mid_tgt = single eq_src_tgt).
        exact Generator.payload_cast_compose hVar
                sourceScope middleScope targetScope somePayload
      · -- Children fusion via mutual IH.
        exact RawTermChildrenV2.subst_rename_commute
                someSubstitution rawRenaming someChildren

/-- Subst-then-rename commute on children spines.

In the cons case, the head is under `headShift` binders.  The
mutual head IH at the lifted scopes gives:

  rename (iter rho shift) (subst (iter sigma shift) head)
    = subst (postRename (iter sigma shift) (iter rho shift)) head

The bridge via `iterateLiftRaw_RawTermSubstV2_postRename_pointwise`
(symmetric direction + subst_pointwise from #181a) converts this to
`subst (iter (postRename sigma rho) shift) head`. -/
theorem RawTermChildrenV2.subst_rename_commute
    {sourceScope middleScope targetScope : Nat}
    (someSubstitution : RawTermSubstV2 sourceScope middleScope)
    (rawRenaming : LeanFX2.RawRenaming middleScope targetScope)
    {binderShifts : List Nat}
    (someChildren : RawTermChildrenV2 binderShifts sourceScope) :
    RawTermChildrenV2.rename rawRenaming
        (RawTermChildrenV2.subst someSubstitution someChildren) =
      RawTermChildrenV2.subst
        (RawTermSubstV2.postRename someSubstitution rawRenaming)
        someChildren := by
  match binderShifts, someChildren with
  | [], .childNil =>
      rfl
  | headShift :: _, .childCons childHead childTail =>
      show RawTermChildrenV2.childCons
              (RawTermV2.rename (iterateLiftRaw rawRenaming headShift)
                  (RawTermV2.subst (iterateLiftRaw someSubstitution headShift)
                      childHead))
              (RawTermChildrenV2.rename rawRenaming
                  (RawTermChildrenV2.subst someSubstitution childTail)) =
            RawTermChildrenV2.childCons
              (RawTermV2.subst
                  (iterateLiftRaw
                      (RawTermSubstV2.postRename someSubstitution rawRenaming)
                      headShift)
                  childHead)
              (RawTermChildrenV2.subst
                  (RawTermSubstV2.postRename someSubstitution rawRenaming)
                  childTail)
      have headCommute := RawTermV2.subst_rename_commute
                            (iterateLiftRaw someSubstitution headShift)
                            (iterateLiftRaw rawRenaming headShift)
                            childHead
      have iterBridgeForward :=
        iterateLiftRaw_RawTermSubstV2_postRename_pointwise
          someSubstitution rawRenaming headShift
      have headBridge :
          RawTermV2.subst
              (RawTermSubstV2.postRename
                  (iterateLiftRaw someSubstitution headShift)
                  (iterateLiftRaw rawRenaming headShift))
              childHead =
            RawTermV2.subst
              (iterateLiftRaw
                  (RawTermSubstV2.postRename someSubstitution rawRenaming)
                  headShift)
              childHead :=
        RawTermV2.subst_pointwise
          (fun position => (iterBridgeForward position).symm)
          childHead
      have tailCommute :=
        RawTermChildrenV2.subst_rename_commute
          someSubstitution rawRenaming childTail
      rw [headCommute, headBridge, tailCommute]

end -- mutual

/-! ## Section 6 — Smoke tests -/

/-- Smoke: subst_rename_commute on `.gen_unit`. -/
theorem RawTermV2.subst_rename_commute_unit_smoke
    {sourceScope middleScope targetScope : Nat}
    (someSubstitution : RawTermSubstV2 sourceScope middleScope)
    (rawRenaming : LeanFX2.RawRenaming middleScope targetScope) :
    RawTermV2.rename rawRenaming
        (RawTermV2.subst someSubstitution
            (.mkGen .gen_unit () .childNil : RawTermV2 sourceScope)) =
      RawTermV2.subst
        (RawTermSubstV2.postRename someSubstitution rawRenaming)
        (.mkGen .gen_unit () .childNil : RawTermV2 sourceScope) :=
  RawTermV2.subst_rename_commute someSubstitution rawRenaming _

/-- Smoke: subst_rename_commute on `.gen_var` at position 0. -/
theorem RawTermV2.subst_rename_commute_var_smoke
    {sourceScope middleScope targetScope : Nat}
    (someSubstitution :
        RawTermSubstV2 (sourceScope + 1) (middleScope + 1))
    (rawRenaming :
        LeanFX2.RawRenaming (middleScope + 1) (targetScope + 1)) :
    RawTermV2.rename rawRenaming
        (RawTermV2.subst someSubstitution
            (.mkGen .gen_var
                    (⟨0, Nat.zero_lt_succ sourceScope⟩ : Fin (sourceScope + 1))
                    .childNil)) =
      RawTermV2.subst
        (RawTermSubstV2.postRename someSubstitution rawRenaming)
        (.mkGen .gen_var
                (⟨0, Nat.zero_lt_succ sourceScope⟩ : Fin (sourceScope + 1))
                .childNil) :=
  RawTermV2.subst_rename_commute someSubstitution rawRenaming _

end LeanFX2.Foundation.PolyCell.Core
