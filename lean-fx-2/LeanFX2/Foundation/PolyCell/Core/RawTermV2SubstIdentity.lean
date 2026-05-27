import LeanFX2.Foundation.PolyCell.Core.RawTermV2SubstPointwise

/-! # Foundation/PolyCell/Core/RawTermV2SubstIdentity — `subst identity = identity`

This file ships the **second of three Action laws** V2-L2.7 needs:
**substituting by the identity substitution returns the term unchanged**.

In monad language: `subst` respects the polynomial monad's η law
(unit-on-the-right).  In Allais ICFP'18 terms: identity-of-the-action
is identity-on-the-term, witnessing the fundamental theorem's
boundary case.

## The three Action laws V2-L2.7 needs

  1. apply_ext      / subst_pointwise   (#181a, RawTermV2SubstPointwise.lean)
  2. identity_apply / subst_identity    (THIS FILE)
  3. compose_assoc  / subst_compose     (next iteration)

Together they close the `Action RawTermSubstV2` instance zero-axiom.

## Why this bridges through `subst_pointwise`

The natural proof shape:

  | mkGen non-var =>
      -- LHS reduces via foldV2's non-var arm to:
      --   algebra g (cast p) (foldChildrenV2 identity children)
      -- We want this to equal `.mkGen g p children`.
      -- The children sub-goal is `foldChildren identity children = children`.

  | childCons head tail =>
      -- Recursion descends under the head's binder shift, lifting
      -- the substitution: foldChildren uses
      --   `iterateLiftRaw identity headShift`
      -- in the head's recursive call.
      --
      -- WE WANT: `subst (iterateLiftRaw identity headShift) head = head`
      -- WE HAVE: `subst identity head = head`         (the term IH)
      --
      -- These differ because `iterateLiftRaw identity n ≠ identity`
      -- as functions (the match-form of `lift` makes the iterated
      -- version definitionally different from `identity`).  They ARE
      -- pointwise-equal — which is exactly what `subst_pointwise`
      -- (#181a) handles.

The chain:
* `lift_identity_pointwise` proves `lift identity ≅ identity` (pointwise).
* `iterateLiftRaw_identity_pointwise` proves
  `iterateLiftRaw identity n ≅ identity` (pointwise) by Nat induction.
* `subst_pointwise` (from #181a) converts the pointwise equality of
  substitutions to an equation of subst results.
* The chain `subst (iterLift identity n) head = subst identity head =
  head` closes via two `rw`s.

This is exactly why we shipped `subst_pointwise` FIRST — it's the
load-bearing infrastructure for `subst_identity` AND for the upcoming
`subst_compose`.

## v1 comparison

v1's `RawTerm.subst_identity` (Foundation/RawSubst/SubstIdentityAndBeta.lean
lines 58-127) is a **74-arm structural induction** — one arm per
RawTerm constructor.  Each arm is `dsimp only [RawTerm.subst] + rw [...]`.

v2's version is a **4-arm mutual induction**:
* `.mkGen` var sub-case (rfl after `subst hVar`)
* `.mkGen` non-var sub-case (`dsimp + simp [dif_neg] + congr 1 +
  children IH`)
* `.childNil` (rfl)
* `.childCons head tail` (subst_pointwise bridge + head IH + tail IH)

The 194-generator cascade is amortized into foldV2.

## Zero-axiom verification

All declarations propext-free:
* `RawTermSubstV2.lift_identity_pointwise` — Fin pattern match on
  0 / k+1; both cases close by `rfl` because lift of identity
  reduces to identity at each position.
* `iterateLiftRaw_identity_pointwise` — Nat induction; succ case
  uses `lift_pointwise priorIH` (from #181a) + `lift_identity_pointwise`.
* `RawTermV2.subst_identity_apply` /
  `RawTermChildrenV2.subst_identity_apply` — mutual structural
  induction with `dsimp only [foldV2]` (not `unfold` — see
  `feedback_lean_unfold_mutual_quot_sound`).

Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace LeanFX2.Foundation.PolyCell.Core

open LeanFX2

/-! ## Section 1 — Identity lifts to identity (pointwise)

Two prerequisite lemmas the mutual proof of `subst_identity_apply`
consumes through the children-spine recursion. -/

/-- Single-binder lift of identity is identity (pointwise).

At the lifted scope `scope + 1`:
* Variable 0 in the lifted scope: `lift identity ⟨0, _⟩ = mkGen .gen_var
  ⟨0, _⟩ .childNil = identity ⟨0, _⟩` by `rfl`.
* Variable k+1: `lift identity ⟨k+1, _⟩ = weaken (identity ⟨k, _⟩) =
  weaken (mkGen .gen_var ⟨k, _⟩ .childNil)`.  Weakening a `.gen_var`
  term via the var arm of foldV2 produces `mkGen .gen_var ⟨k+1, _⟩
  .childNil`, which is `identity ⟨k+1, _⟩` (with Fin bounds equated
  by proof irrelevance).  Closes by `rfl`. -/
theorem RawTermSubstV2.lift_identity_pointwise {scope : Nat} :
    RawTermSubstV2.PointwiseEq
        (RawTermSubstV2.lift (RawTermSubstV2.identity (scope := scope)))
        (RawTermSubstV2.identity (scope := scope + 1)) := by
  intro position
  match position with
  | ⟨0, _⟩ => rfl
  | ⟨_priorPositionValue + 1, _⟩ => rfl

/-- Iterated lift of identity is identity (pointwise).

Induction on `binderDepth`:
* `zero`: `iterateLiftRaw identity 0 = identity` (by `iterateLiftRaw`'s
  defn).  Pointwise-eq is reflexivity.
* `succ priorDepth`: chain through
  `lift (iterateLiftRaw identity priorDepth) ≅ lift identity ≅ identity`.
  First step via `lift_pointwise priorIH`; second step via
  `lift_identity_pointwise`. -/
theorem iterateLiftRaw_identity_pointwise {scope : Nat}
    (binderDepth : Nat) :
    RawTermSubstV2.PointwiseEq
        (iterateLiftRaw
            (RawTermSubstV2.identity (scope := scope)) binderDepth)
        (RawTermSubstV2.identity (scope := scope + binderDepth)) := by
  induction binderDepth with
  | zero => exact RawTermSubstV2.PointwiseEq.refl _
  | succ _priorDepth priorIH =>
      intro position
      -- iterateLiftRaw identity (priorDepth + 1) =
      --   lift (iterateLiftRaw identity priorDepth) by unfolding.
      -- Chain through lift identity to identity at the higher scope.
      show RawTermSubstV2.lift
              (iterateLiftRaw (RawTermSubstV2.identity (scope := scope))
                  _priorDepth) position
          = RawTermSubstV2.identity position
      rw [RawTermSubstV2.lift_pointwise priorIH position,
          RawTermSubstV2.lift_identity_pointwise position]

/-! ## Section 2 — The Allais identity_apply theorem (mutual induction)

The headline theorem: substituting by the identity substitution
returns the term unchanged.  This is the polynomial monad's
right-unit law at the term layer.

In v1: 74-arm structural induction.
In v2: 4-arm mutual induction.  The Generator cascade is dead. -/

mutual

/-- Allais identity_apply for terms: substituting by `RawTermSubstV2.identity`
returns the term unchanged.

This is the v2 replacement for v1's 74-arm `RawTerm.subst_identity`
(Foundation/RawSubst/SubstIdentityAndBeta.lean lines 58-127). -/
theorem RawTermV2.subst_identity_apply {scope : Nat}
    (sourceTerm : RawTermV2 scope) :
    RawTermV2.subst RawTermSubstV2.identity sourceTerm = sourceTerm := by
  match sourceTerm with
  | .mkGen someGenerator somePayload someChildren =>
    by_cases hVar : someGenerator = .gen_var
    case pos =>
      -- Variable arm: foldV2 dispatches to var arm.  The result is
      -- `varToRawTermV2 identity payload = identity payload =
      -- .mkGen .gen_var payload .childNil`.  Need someChildren =
      -- .childNil necessarily (only inhabitant of
      -- RawTermChildrenV2 .gen_var.binderShifts scope = ... [] scope).
      subst hVar
      match someChildren with
      | .childNil => rfl
    case neg =>
      -- Non-variable arm: foldV2 dispatches to algebra arm.
      -- Reduces to canonical.algebra g (cast p) (foldChildren id ch).
      -- canonical.algebra g p c = .mkGen g p c.
      -- Cast is rfl-identity since src = tgt = scope.
      -- So LHS = .mkGen g p (foldChildren id ch); congr 1 +
      -- children IH closes.
      --
      -- CRITICAL: `dsimp only [foldV2]` not `unfold foldV2` — `unfold`
      -- on a mutual recursive def pulls Quot.sound (see
      -- feedback_lean_unfold_mutual_quot_sound, confirmed during #181a).
      dsimp only [RawTermV2.subst, foldV2]
      simp only [dif_neg hVar]
      congr 1
      exact RawTermChildrenV2.subst_identity_apply someChildren

/-- Allais identity_apply for children spines: substituting by
`RawTermSubstV2.identity` returns the children unchanged.

In the cons case, the head sits under `headShift`-many binders, so
foldChildren uses `iterateLiftRaw identity headShift` for the head's
recursive substitution.  The chain:

  subst (iterateLiftRaw identity headShift) head
    = subst identity head            -- via subst_pointwise +
                                     -- iterateLiftRaw_identity_pointwise
    = head                           -- by the term IH
-/
theorem RawTermChildrenV2.subst_identity_apply {scope : Nat}
    {binderShifts : List Nat}
    (someChildren : RawTermChildrenV2 binderShifts scope) :
    RawTermChildrenV2.subst RawTermSubstV2.identity someChildren =
      someChildren := by
  match binderShifts, someChildren with
  | [], .childNil => rfl
  | headShift :: _, .childCons childHead childTail =>
      -- foldChildren identity (childCons h t) reduces to
      --   .childCons (foldV2 (iterateLiftRaw identity headShift) h)
      --              (foldChildren identity t)
      -- Need to bridge the head's lifted-identity through pointwise.
      show RawTermChildrenV2.childCons
              (RawTermV2.subst
                  (iterateLiftRaw RawTermSubstV2.identity headShift)
                  childHead)
              (RawTermChildrenV2.subst RawTermSubstV2.identity
                  childTail) =
            RawTermChildrenV2.childCons childHead childTail
      have iterLiftEqualsIdentity :=
        iterateLiftRaw_identity_pointwise (scope := scope) headShift
      have headSubstEqualsIdentity :
          RawTermV2.subst
              (iterateLiftRaw RawTermSubstV2.identity headShift)
              childHead =
            RawTermV2.subst RawTermSubstV2.identity childHead :=
        RawTermV2.subst_pointwise iterLiftEqualsIdentity childHead
      have headRecoverIH :=
        RawTermV2.subst_identity_apply childHead
      have tailRecoverIH :=
        RawTermChildrenV2.subst_identity_apply childTail
      rw [headSubstEqualsIdentity, headRecoverIH, tailRecoverIH]

end -- mutual

/-! ## Section 3 — Smoke tests

Verify the headline theorem invokes cleanly on representative terms.

The unit smoke test was already shipped at #180 as
`subst_identity_unit_smoke` (which closes by `rfl` directly because
unit has no variables).  The smokes below USE the general theorem
rather than `rfl`, exercising the mutual induction's dispatch on
non-trivial generators. -/

/-- Smoke: subst_identity_apply on `.gen_unit` returns the unit term
unchanged.  Exercises the non-variable arm (despite the unit having
no variables — the dispatch still routes through the non-var arm). -/
theorem RawTermV2.subst_identity_apply_unit_smoke {scope : Nat} :
    RawTermV2.subst (RawTermSubstV2.identity (scope := scope))
        (.mkGen .gen_unit () .childNil) =
      (.mkGen .gen_unit () .childNil : RawTermV2 scope) :=
  RawTermV2.subst_identity_apply _

/-- Smoke: subst_identity_apply on `.gen_var ⟨0, _⟩` returns the
variable term unchanged.  Exercises the variable arm. -/
theorem RawTermV2.subst_identity_apply_var_smoke {scope : Nat} :
    RawTermV2.subst (RawTermSubstV2.identity (scope := scope + 1))
        (.mkGen .gen_var
                (⟨0, Nat.zero_lt_succ scope⟩ : Fin (scope + 1))
                .childNil) =
      .mkGen .gen_var
              (⟨0, Nat.zero_lt_succ scope⟩ : Fin (scope + 1))
              .childNil :=
  RawTermV2.subst_identity_apply _

end LeanFX2.Foundation.PolyCell.Core
