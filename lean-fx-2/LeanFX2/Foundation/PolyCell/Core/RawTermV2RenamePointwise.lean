import LeanFX2.Foundation.PolyCell.Core.RawTermV2Rename

/-! # Foundation/PolyCell/Core/RawTermV2RenamePointwise — rename-side Allais extensionality

This file ships the **rename-side analog** of #181a's
`subst_pointwise`: pointwise-equal renamings produce equal rename
results on any term.

## Why this is the first piece of the cross-direction fusion ladder

The headline `subst_compose` (the polynomial monad's associativity)
requires a cross-direction commute lemma between rename and subst:

  weaken (term.subst sigma) = (weaken term).subst sigma.lift

which itself is an instance of `subst_rename_commute` /
`rename_subst_commute`.  And those, in turn, rely on rename-side
pointwise reasoning.

The dependency tower:

  rename_pointwise            (THIS FILE)            <─ Allais ext for ρ
  rename_compose              (next)                 <─ ρ-ρ fusion
  subst_rename_commute        (after)                <─ ρ then σ
  rename_subst_commute        (after)                <─ σ then ρ
  lift_compose_pointwise      (using all of above)
  subst_compose               (the headline)
  Action RawTermSubstV2 instance  (closes V2-L2.7)

Each layer is a 4-arm mutual induction in v2 (vs v1's 74-arm).

## Structural parallel to #181a

The file mirrors `RawTermV2SubstPointwise.lean` exactly:
* `RawRenaming.PointwiseEq` predicate (parallel to
  `RawTermSubstV2.PointwiseEq`).
* `RawRenaming.lift_pointwise` (parallel to
  `RawTermSubstV2.lift_pointwise`).
* `iterateLiftRaw_RawRenaming_pointwise` (parallel to
  `iterateLiftRaw_RawTermSubstV2_pointwise`).
* Mutual `RawTermV2.rename_pointwise` /
  `RawTermChildrenV2.rename_pointwise` (parallel to
  `subst_pointwise` mutual block).

The differences are:
* `RawRenaming` has `ActionTarget := Fin`, not `RawTermV2`.
  `varToRawTermV2 rho pos = .mkGen .gen_var (rho pos) .childNil`
  (the renamed Fin wrapped back as a `gen_var` term).
* `RawRenaming.lift ⟨k+1, _⟩ = Fin.succ (rho ⟨k, _⟩)` (Fin shift).
  The substitution's `lift ⟨k+1, _⟩ = weaken (sigma ⟨k, _⟩)` is a
  RawTermV2.

## Zero-axiom verification

Same recipe as #181a (the propext-clean recipe is now established):
* `dsimp only [..., foldV2]` rather than `unfold` — `unfold` on
  mutual recursion pulls Quot.sound (per
  `feedback_lean_unfold_mutual_quot_sound`).
* `simp only [dif_neg hVar]` — propext-clean.
* `by_cases hVar : g = .gen_var` via `DecidableEq Generator`.
* Full pattern enumeration (no wildcards).

Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`.

## v1 comparison

v1's `RawTerm.rename_pointwise` (Foundation/RawSubst/RenameLemmas.lean
or similar — exists in the 74-arm style).  v2's version is a 4-arm
mutual induction.  Same cascade-tax ratio (~18x reduction) as #181a.
-/

namespace LeanFX2.Foundation.PolyCell.Core

open LeanFX2

/-! ## Section 1 — Pointwise equality on RawRenamings -/

/-- Pointwise equality of renamings.

Two renamings agree pointwise when they produce the same target Fin
for every source position.  Avoids funext: the laws are stated
relative to this Prop rather than function equality.

Named under `LeanFX2.Foundation.PolyCell.Core.RawRenaming.PointwiseEq`
(NOT v1's `LeanFX2.RawRenaming` namespace) to keep v1 / v2 namespace
separation clean.  The full path disambiguates from any potential
future v1 lemma with the same leaf name. -/
def RawRenaming.PointwiseEq {sourceScope targetScope : Nat}
    (firstRenaming secondRenaming :
        LeanFX2.RawRenaming sourceScope targetScope) : Prop :=
  ∀ position : Fin sourceScope,
    firstRenaming position = secondRenaming position

/-- Pointwise equality is reflexive. -/
theorem RawRenaming.PointwiseEq.refl {sourceScope targetScope : Nat}
    (someRenaming : LeanFX2.RawRenaming sourceScope targetScope) :
    RawRenaming.PointwiseEq someRenaming someRenaming :=
  fun _ => Eq.refl _

/-! ## Section 2 — Binder lifts respect pointwise equality -/

/-- Lifting respects pointwise equality on renamings.

* Variable 0 in the lifted scope: both lifts produce `⟨0, _⟩` by
  `RawRenaming.lift`'s defn.  Closes by `rfl`.
* Variable k+1 in the lifted scope: both lifts produce
  `Fin.succ (rho_i ⟨k, _⟩)`.  Congruence of `Fin.succ` over the
  pointwise hypothesis at position k closes via `rw`. -/
theorem RawRenaming.lift_pointwise {sourceScope targetScope : Nat}
    {firstRenaming secondRenaming :
        LeanFX2.RawRenaming sourceScope targetScope}
    (renamingEq :
        RawRenaming.PointwiseEq firstRenaming secondRenaming) :
    RawRenaming.PointwiseEq
        firstRenaming.lift
        secondRenaming.lift := by
  intro position
  match position with
  | ⟨0, _⟩ => rfl
  | ⟨priorPositionValue + 1, hBound⟩ =>
      show Fin.succ
              (firstRenaming
                  ⟨priorPositionValue, Nat.lt_of_succ_lt_succ hBound⟩) =
            Fin.succ
              (secondRenaming
                  ⟨priorPositionValue, Nat.lt_of_succ_lt_succ hBound⟩)
      rw [renamingEq ⟨priorPositionValue, Nat.lt_of_succ_lt_succ hBound⟩]

/-- Iterated lift respects pointwise equality on renamings.

Induction on `binderDepth`.  The succ case threads via
`RawRenaming.lift_pointwise` over the IH (mirroring #181a's
`iterateLiftRaw_RawTermSubstV2_pointwise` exactly). -/
theorem iterateLiftRaw_RawRenaming_pointwise {sourceScope targetScope : Nat}
    {firstRenaming secondRenaming :
        LeanFX2.RawRenaming sourceScope targetScope}
    (renamingEq :
        RawRenaming.PointwiseEq firstRenaming secondRenaming)
    (binderDepth : Nat) :
    RawRenaming.PointwiseEq
        (iterateLiftRaw firstRenaming binderDepth)
        (iterateLiftRaw secondRenaming binderDepth) := by
  induction binderDepth with
  | zero => exact renamingEq
  | succ _priorDepth priorIH =>
      show RawRenaming.PointwiseEq
              (LiftsRaw.liftForRaw (iterateLiftRaw firstRenaming _priorDepth))
              (LiftsRaw.liftForRaw (iterateLiftRaw secondRenaming _priorDepth))
      exact RawRenaming.lift_pointwise priorIH

/-! ## Section 3 — The Allais rename-side extensionality theorem

In v1: 74-arm structural induction (one arm per RawTerm ctor).
In v2: 4-arm mutual induction.

Same proof technique as #181a's `subst_pointwise`, with the
following differences in the variable arm:

  Substitution side (#181a):
    `varToRawTermV2 sigma pos = sigma pos` (a RawTermV2).

  Renaming side (THIS FILE):
    `varToRawTermV2 rho pos = .mkGen .gen_var (rho pos) .childNil`
    (a RawTermV2 wrapping the renamed Fin).

The non-variable arm is identical in shape — both dispatch via
`dsimp only [foldV2] + simp only [dif_neg hVar] + congr 1 +
children IH`. -/

mutual

/-- Allais extensionality for `RawTermV2.rename`: pointwise-equal
renamings produce equal rename results.

This is the v2 replacement for v1's 74-arm `RawTerm.rename_pointwise`.
Adding a new Generator does NOT require adding a new arm here — the
proof closes uniformly through the non-var sub-case via the children
spine recursion. -/
theorem RawTermV2.rename_pointwise {sourceScope targetScope : Nat}
    {firstRenaming secondRenaming :
        LeanFX2.RawRenaming sourceScope targetScope}
    (renamingEq :
        RawRenaming.PointwiseEq firstRenaming secondRenaming)
    (sourceTerm : RawTermV2 sourceScope) :
    RawTermV2.rename firstRenaming sourceTerm =
      RawTermV2.rename secondRenaming sourceTerm := by
  match sourceTerm with
  | .mkGen someGenerator somePayload someChildren =>
    by_cases hVar : someGenerator = .gen_var
    case pos =>
      -- Variable arm: rename reduces via foldV2 var-arm to
      -- `varToRawTermV2 rho_i payload`.  For RawRenaming's
      -- ActsOnRawTermV2Var instance:
      --   varToRawTermV2 rho pos = .mkGen .gen_var (rho pos) .childNil
      -- So LHS and RHS reduce to `.mkGen .gen_var (rho_i pos) .childNil`.
      -- We need (rho_1 pos) = (rho_2 pos) via renamingEq.
      subst hVar
      show ActsOnRawTermV2Var.varToRawTermV2 firstRenaming somePayload =
            ActsOnRawTermV2Var.varToRawTermV2 secondRenaming somePayload
      show (.mkGen .gen_var (firstRenaming somePayload) .childNil
              : RawTermV2 targetScope) =
            .mkGen .gen_var (secondRenaming somePayload) .childNil
      rw [renamingEq somePayload]
    case neg =>
      -- Non-variable arm: foldV2 dispatches to algebra arm.
      -- Reduces to canonical.algebra g (cast p) (foldChildren rho_i ch).
      -- canonical.algebra g p c = .mkGen g p c.  Cast is rfl-identity
      -- only when src = tgt; for rename src ≠ tgt in general, but the
      -- payload type is scope-invariant for non-var generators so the
      -- cast is well-defined and uniform on both sides.
      -- The algebra and the cast payload are rho-independent; only
      -- the folded children differ.  The children IH closes the goal.
      show RawTermV2.rename firstRenaming
              (.mkGen someGenerator somePayload someChildren) =
            RawTermV2.rename secondRenaming
              (.mkGen someGenerator somePayload someChildren)
      dsimp only [RawTermV2.rename, foldV2]
      simp only [dif_neg hVar]
      congr 1
      exact RawTermChildrenV2.rename_pointwise renamingEq someChildren

/-- Allais extensionality for `RawTermChildrenV2.rename` on the
children spine: pointwise-equal renamings produce equal rename
results.

In the cons case, the head sits under `headShift`-many binders, so
the renaming lifts to `iterateLiftRaw rho headShift` for the head's
recursive call.  Threading pointwise-eq through this lift uses
`iterateLiftRaw_RawRenaming_pointwise` (a Nat induction on
binderDepth).  The tail recurses with the original renaming. -/
theorem RawTermChildrenV2.rename_pointwise
    {sourceScope targetScope : Nat}
    {firstRenaming secondRenaming :
        LeanFX2.RawRenaming sourceScope targetScope}
    (renamingEq :
        RawRenaming.PointwiseEq firstRenaming secondRenaming)
    {binderShifts : List Nat}
    (someChildren : RawTermChildrenV2 binderShifts sourceScope) :
    RawTermChildrenV2.rename firstRenaming someChildren =
      RawTermChildrenV2.rename secondRenaming someChildren := by
  match binderShifts, someChildren with
  | [], .childNil =>
      rfl
  | headShift :: _, .childCons childHead childTail =>
      show RawTermChildrenV2.childCons
              (RawTermV2.rename
                  (iterateLiftRaw firstRenaming headShift) childHead)
              (RawTermChildrenV2.rename firstRenaming childTail) =
            RawTermChildrenV2.childCons
              (RawTermV2.rename
                  (iterateLiftRaw secondRenaming headShift) childHead)
              (RawTermChildrenV2.rename secondRenaming childTail)
      have headEqualityWitness :=
        RawTermV2.rename_pointwise
          (iterateLiftRaw_RawRenaming_pointwise renamingEq headShift)
          childHead
      have tailEqualityWitness :=
        RawTermChildrenV2.rename_pointwise renamingEq childTail
      rw [headEqualityWitness, tailEqualityWitness]

end -- mutual

/-! ## Section 4 — Smoke tests

Verify the headline `RawTermV2.rename_pointwise` invokes cleanly on
representative terms. -/

/-- Smoke: rename_pointwise on `.gen_unit` is `rfl` (no variables, no
renaming-eq usage in the var arm). -/
theorem RawTermV2.rename_pointwise_unit_smoke
    {sourceScope targetScope : Nat}
    {firstRenaming secondRenaming :
        LeanFX2.RawRenaming sourceScope targetScope}
    (renamingEq :
        RawRenaming.PointwiseEq firstRenaming secondRenaming) :
    RawTermV2.rename firstRenaming
        (.mkGen .gen_unit () .childNil : RawTermV2 sourceScope) =
      RawTermV2.rename secondRenaming
        (.mkGen .gen_unit () .childNil : RawTermV2 sourceScope) :=
  RawTermV2.rename_pointwise renamingEq _

/-- Smoke: rename_pointwise on `.gen_var ⟨0, _⟩` uses the pointwise
hypothesis at position 0.  Exercises the variable arm. -/
theorem RawTermV2.rename_pointwise_var_smoke
    {sourceScope targetScope : Nat}
    {firstRenaming secondRenaming :
        LeanFX2.RawRenaming (sourceScope + 1) (targetScope + 1)}
    (renamingEq :
        RawRenaming.PointwiseEq firstRenaming secondRenaming) :
    RawTermV2.rename firstRenaming
        (.mkGen .gen_var
                (⟨0, Nat.zero_lt_succ sourceScope⟩ : Fin (sourceScope + 1))
                .childNil) =
      RawTermV2.rename secondRenaming
        (.mkGen .gen_var
                (⟨0, Nat.zero_lt_succ sourceScope⟩ : Fin (sourceScope + 1))
                .childNil) :=
  RawTermV2.rename_pointwise renamingEq _

end LeanFX2.Foundation.PolyCell.Core
