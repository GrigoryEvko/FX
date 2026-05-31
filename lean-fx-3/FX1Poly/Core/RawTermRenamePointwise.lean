import FX1Poly.Core.RawTermRename

/-! # Foundation/PolyCell/Core/RawTermRenamePointwise — rename-side Allais extensionality

The **rename-side analog** of `subst_pointwise`: pointwise-equal
renamings produce equal rename results on any term.

## Place in the cross-direction fusion ladder

The headline `subst_compose` (the polynomial monad's associativity)
requires a cross-direction commute lemma between rename and subst:

  weaken (term.subst sigma) = (weaken term).subst sigma.lift

which itself is an instance of `subst_rename_commute` /
`rename_subst_commute`.  And those, in turn, rely on rename-side
pointwise reasoning.

The dependency tower:

  rename_pointwise            (THIS FILE)            <─ Allais ext for rho
  rename_compose                                     <─ rho-rho fusion
  subst_rename_commute                               <─ rho then sigma
  rename_subst_commute                               <─ sigma then rho
  lift_compose_pointwise      (using all of above)
  subst_compose               (the headline)
  Action RawTermSubst instance

Each layer is a 4-arm mutual induction.

## Structural parallel to `subst_pointwise`

The file mirrors `RawTermSubstPointwise.lean` exactly:
* `RawRenaming.PointwiseEq` predicate (parallel to
  `RawTermSubst.PointwiseEq`).
* `RawRenaming.lift_pointwise` (parallel to
  `RawTermSubst.lift_pointwise`).
* `iterateLiftRaw_RawRenaming_pointwise` (parallel to
  `iterateLiftRaw_RawTermSubst_pointwise`).
* Mutual `RawTerm.rename_pointwise` /
  `RawTermChildren.rename_pointwise` (parallel to
  `subst_pointwise` mutual block).

The differences are:
* `RawRenaming` has `ActionTarget := Fin`, not `RawTerm`.
  `varToRawTerm rho pos = .mkGen .gen_var (rho pos) .childNil`
  (the renamed Fin wrapped back as a `gen_var` term).
* `RawRenaming.lift ⟨k+1, _⟩ = Fin.succ (rho ⟨k, _⟩)` (Fin shift).
  The substitution's `lift ⟨k+1, _⟩ = weaken (sigma ⟨k, _⟩)` is a
  RawTerm.

## Zero-axiom verification

The propext-clean recipe:
* `dsimp only [..., fold]` rather than `unfold` — `unfold` on
  mutual recursion pulls Quot.sound (per
  `feedback_lean_unfold_mutual_quot_sound`).
* `simp only [dif_neg hVar]` — propext-clean.
* `by_cases hVar : g = .gen_var` via `DecidableEq Generator`.
* Full pattern enumeration (no wildcards).

Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`.

The mutual `RawTerm.rename_pointwise` /
`RawTermChildren.rename_pointwise` is a 4-arm mutual induction.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-! ## Section 1 — Pointwise equality on RawRenamings -/

/-- Pointwise equality of renamings.

Two renamings agree pointwise when they produce the same target Fin
for every source position.  Avoids funext: the laws are stated
relative to this Prop rather than function equality.

Named under `FX1Poly.Core.RawRenaming.PointwiseEq` (NOT the
`FX1Poly.Foundation.RawRenaming` namespace) to keep the namespaces
separate.  The full path disambiguates from any lemma with the same
leaf name in the Foundation namespace. -/
def RawRenaming.PointwiseEq {sourceScope targetScope : Nat}
    (firstRenaming secondRenaming :
        FX1Poly.Foundation.RawRenaming sourceScope targetScope) : Prop :=
  ∀ position : Fin sourceScope,
    firstRenaming position = secondRenaming position

/-- Pointwise equality is reflexive. -/
theorem RawRenaming.PointwiseEq.refl {sourceScope targetScope : Nat}
    (someRenaming : FX1Poly.Foundation.RawRenaming sourceScope targetScope) :
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
        FX1Poly.Foundation.RawRenaming sourceScope targetScope}
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
`iterateLiftRaw_RawTermSubst_pointwise` exactly). -/
theorem iterateLiftRaw_RawRenaming_pointwise {sourceScope targetScope : Nat}
    {firstRenaming secondRenaming :
        FX1Poly.Foundation.RawRenaming sourceScope targetScope}
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

A 4-arm mutual induction.

Same proof technique as `subst_pointwise`, with the following
differences in the variable arm:

  Substitution side:
    `varToRawTerm sigma pos = sigma pos` (a RawTerm).

  Renaming side (THIS FILE):
    `varToRawTerm rho pos = .mkGen .gen_var (rho pos) .childNil`
    (a RawTerm wrapping the renamed Fin).

The non-variable arm is identical in shape — both dispatch via
`dsimp only [fold] + simp only [dif_neg hVar] + congr 1 +
children IH`. -/

mutual

/-- Allais extensionality for `RawTerm.rename`: pointwise-equal
renamings produce equal rename results.

Adding a new Generator does NOT require adding a new arm here — the
proof closes uniformly through the non-var sub-case via the children
spine recursion. -/
theorem RawTerm.rename_pointwise {sourceScope targetScope : Nat}
    {firstRenaming secondRenaming :
        FX1Poly.Foundation.RawRenaming sourceScope targetScope}
    (renamingEq :
        RawRenaming.PointwiseEq firstRenaming secondRenaming)
    (sourceTerm : RawTerm sourceScope) :
    RawTerm.rename firstRenaming sourceTerm =
      RawTerm.rename secondRenaming sourceTerm := by
  match sourceTerm with
  | .mkGen someGenerator somePayload someChildren =>
    by_cases hVar : someGenerator = .gen_var
    case pos =>
      -- Variable arm: rename reduces via fold var-arm to
      -- `varToRawTerm rho_i payload`.  For RawRenaming's
      -- ActsOnRawTermVar instance:
      --   varToRawTerm rho pos = .mkGen .gen_var (rho pos) .childNil
      -- So LHS and RHS reduce to `.mkGen .gen_var (rho_i pos) .childNil`.
      -- We need (rho_1 pos) = (rho_2 pos) via renamingEq.
      subst hVar
      show ActsOnRawTermVar.varToRawTerm firstRenaming somePayload =
            ActsOnRawTermVar.varToRawTerm secondRenaming somePayload
      show (.mkGen .gen_var (firstRenaming somePayload) .childNil
              : RawTerm targetScope) =
            .mkGen .gen_var (secondRenaming somePayload) .childNil
      rw [renamingEq somePayload]
    case neg =>
      -- Non-variable arm: fold dispatches to algebra arm.
      -- Reduces to canonical.algebra g (cast p) (foldChildren rho_i ch).
      -- canonical.algebra g p c = .mkGen g p c.  Cast is rfl-identity
      -- only when src = tgt; for rename src ≠ tgt in general, but the
      -- payload type is scope-invariant for non-var generators so the
      -- cast is well-defined and uniform on both sides.
      -- The algebra and the cast payload are rho-independent; only
      -- the folded children differ.  The children IH closes the goal.
      show RawTerm.rename firstRenaming
              (.mkGen someGenerator somePayload someChildren) =
            RawTerm.rename secondRenaming
              (.mkGen someGenerator somePayload someChildren)
      dsimp only [RawTerm.rename, fold]
      simp only [dif_neg hVar]
      congr 1
      exact RawTermChildren.rename_pointwise renamingEq someChildren

/-- Allais extensionality for `RawTermChildren.rename` on the
children spine: pointwise-equal renamings produce equal rename
results.

In the cons case, the head sits under `headShift`-many binders, so
the renaming lifts to `iterateLiftRaw rho headShift` for the head's
recursive call.  Threading pointwise-eq through this lift uses
`iterateLiftRaw_RawRenaming_pointwise` (a Nat induction on
binderDepth).  The tail recurses with the original renaming. -/
theorem RawTermChildren.rename_pointwise
    {sourceScope targetScope : Nat}
    {firstRenaming secondRenaming :
        FX1Poly.Foundation.RawRenaming sourceScope targetScope}
    (renamingEq :
        RawRenaming.PointwiseEq firstRenaming secondRenaming)
    {binderShifts : List Nat}
    (someChildren : RawTermChildren binderShifts sourceScope) :
    RawTermChildren.rename firstRenaming someChildren =
      RawTermChildren.rename secondRenaming someChildren := by
  match binderShifts, someChildren with
  | [], .childNil =>
      rfl
  | headShift :: _, .childCons childHead childTail =>
      show RawTermChildren.childCons
              (RawTerm.rename
                  (iterateLiftRaw firstRenaming headShift) childHead)
              (RawTermChildren.rename firstRenaming childTail) =
            RawTermChildren.childCons
              (RawTerm.rename
                  (iterateLiftRaw secondRenaming headShift) childHead)
              (RawTermChildren.rename secondRenaming childTail)
      have headEqualityWitness :=
        RawTerm.rename_pointwise
          (iterateLiftRaw_RawRenaming_pointwise renamingEq headShift)
          childHead
      have tailEqualityWitness :=
        RawTermChildren.rename_pointwise renamingEq childTail
      rw [headEqualityWitness, tailEqualityWitness]

end -- mutual

/-! ## Section 4 — Smoke tests

Verify the headline `RawTerm.rename_pointwise` invokes cleanly on
representative terms. -/

/-- Smoke: rename_pointwise on `.gen_unit` is `rfl` (no variables, no
renaming-eq usage in the var arm). -/
theorem RawTerm.rename_pointwise_unit_smoke
    {sourceScope targetScope : Nat}
    {firstRenaming secondRenaming :
        FX1Poly.Foundation.RawRenaming sourceScope targetScope}
    (renamingEq :
        RawRenaming.PointwiseEq firstRenaming secondRenaming) :
    RawTerm.rename firstRenaming
        (.mkGen .gen_unit () .childNil : RawTerm sourceScope) =
      RawTerm.rename secondRenaming
        (.mkGen .gen_unit () .childNil : RawTerm sourceScope) :=
  RawTerm.rename_pointwise renamingEq _

/-- Smoke: rename_pointwise on `.gen_var ⟨0, _⟩` uses the pointwise
hypothesis at position 0.  Exercises the variable arm. -/
theorem RawTerm.rename_pointwise_var_smoke
    {sourceScope targetScope : Nat}
    {firstRenaming secondRenaming :
        FX1Poly.Foundation.RawRenaming (sourceScope + 1) (targetScope + 1)}
    (renamingEq :
        RawRenaming.PointwiseEq firstRenaming secondRenaming) :
    RawTerm.rename firstRenaming
        (.mkGen .gen_var
                (⟨0, Nat.zero_lt_succ sourceScope⟩ : Fin (sourceScope + 1))
                .childNil) =
      RawTerm.rename secondRenaming
        (.mkGen .gen_var
                (⟨0, Nat.zero_lt_succ sourceScope⟩ : Fin (sourceScope + 1))
                .childNil) :=
  RawTerm.rename_pointwise renamingEq _

end FX1Poly.Core
