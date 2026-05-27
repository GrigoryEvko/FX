import LeanFX2.Foundation.PolyCell.Core.RawTermV2RenameCompose

/-! # Foundation/PolyCell/Core/RawTermV2RenameComposeFusion — term-level renaming fusion

This file ships the **third cross-direction fusion piece**:

  RawTermV2.rename rho2 (RawTermV2.rename rho1 term)
    = RawTermV2.rename (RawRenaming.compose rho1 rho2) term

— the polynomial monad's associativity at the renaming layer.

Position in the cross-direction fusion ladder:

  rename_pointwise            (#181c1, shipped)
  lift_compose_pointwise (rename) (#181c2, shipped)
  iterateLiftRaw_compose_*  (rename) (#181c2, shipped)
  Generator.payload_cast_compose  (THIS COMMIT — keystone helper)
  rename_compose              (THIS COMMIT — term-level fusion)
  subst_rename_commute        (after)
  rename_subst_commute        (after)
  lift_compose_pointwise (subst)
  iterateLiftRaw_compose_* (subst)
  subst_compose               (the headline)
  Action RawTermSubstV2 instance  (closes V2-L2.7)

## The keystone helper: chained casts compose to single casts

The LHS of `rename_compose` applies `rename` TWICE, generating
TWO casts: `payload_scope_invariant_of_not_var hVar src mid` then
`payload_scope_invariant_of_not_var hVar mid tgt`.

The RHS applies `rename` ONCE with the composed renaming, generating
ONE cast: `payload_scope_invariant_of_not_var hVar src tgt`.

For non-var generators, `Generator.payload someGenerator scope` is
**scope-invariant** (a fact `payload_scope_invariant_of_not_var`
already captures).  So the underlying value is the SAME on both
sides — but propositionally, we need:

  eq_mid_tgt ▸ (eq_src_mid ▸ payload) = eq_src_tgt ▸ payload

This is `Generator.payload_cast_compose` (shipped here).  It's a
193-arm `all_goals rfl` after the var case is dispatched as
`absurd rfl hNotVar` — the same pattern as
`Generator.payload_scope_invariant_of_not_var`.

For each specific non-var generator, the payload type is a concrete
type (Unit, Nat, etc.) independent of scope, so both casts reduce
to the identity AND chain to the identity — all `rfl`.

## The main fusion theorem

`RawTermV2.rename_compose` is a mutual structural induction with the
standard pattern:
* `.mkGen .gen_var pos .childNil` (var arm) — closes by `rfl` (LHS
  and RHS both reduce to `mkGen .gen_var (rho2 (rho1 pos)) .childNil`).
* `.mkGen g p c` with `g ≠ .gen_var` (non-var arm) — three subgoals
  after `dsimp + simp_only [dif_neg hVar] + congr`:
  1. The generator is the same on both sides (auto-closes via rfl).
  2. Cast composition: closed by `Generator.payload_cast_compose`.
  3. Children fusion: closed by mutual children IH + bridge.

The children mutual sub-theorem:
* `.childNil` — `rfl`.
* `.childCons head tail` — head IH applied with LIFTED renamings,
  bridge via `iterateLiftRaw_RawRenaming_compose_pointwise` (from
  #181c2) to convert `compose (lift r1) (lift r2)` → `lift (compose r1 r2)`.

## Why double-unfolding is needed

The LHS `rename rho2 (rename rho1 (mkGen ...))` involves TWO renames.
After `dsimp only [RawTermV2.rename, foldV2]`, both occurrences unfold
but the inner result is `mkGen g (eq_src_mid ▸ p) (foldChildren rho1 c)`
— a NEW `mkGen` that the outer rename hasn't yet processed.

A second pass of `dsimp + simp_only [dif_neg hVar]` (with the outer
rename's foldV2 dispatch) is needed.  Specifically:
1. `dsimp only [RawTermV2.rename, foldV2]` — unfolds outer rename
   one step and inner rename fully (because the inner has the
   matchable `mkGen` directly).
2. `simp only [dif_neg hVar]` — collapses the inner's `if hVar : g =
   .gen_var` to else branch.
3. `dsimp only [RawTermV2.rename, foldV2, GenAlgebraV2.canonical]` —
   forces the outer's `match` to see the `mkGen` produced by the
   inner, unfolds the outer's foldV2.
4. `simp only [dif_neg hVar]` again — collapses the outer's dispatch.
5. Now both sides are flat `mkGen g (cast) (foldChildren-...) ` form;
   `congr 1` peels off into cast + children subgoals.

In practice, packing this into one `dsimp + simp_only + dsimp +
simp_only` sequence works.  If issues arise, can be split into a
helper unfolding lemma `RawTermV2.rename_nonvar`.

## Zero-axiom verification

All declarations propext-free:
* `Generator.payload_cast_compose` — `cases generator + absurd + all_goals rfl`,
  same pattern as `payload_scope_invariant_of_not_var`.
* Mutual `RawTermV2.rename_compose` / `RawTermChildrenV2.rename_compose` —
  `dsimp only [foldV2]` (NOT `unfold` — Quot.sound trap), `simp only
  [dif_neg]`, `congr` + cast helper + mutual IH.

Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`.

## v1 comparison

v1's `RawTerm.rename_compose` is a 74-arm structural induction
(Foundation/RawSubst/RenameLemmas.lean or equivalent).  Each arm is
`dsimp + rw`, similar to v1's other commute lemmas.

v2's version is a 4-arm mutual induction:
* `.mkGen` var sub-case
* `.mkGen` non-var sub-case
* `.childNil`
* `.childCons`

Cascade-tax ratio: ~18x reduction.  The Generator dispatch is
amortized into foldV2 plus the cast composition helper.
-/

namespace LeanFX2.Foundation.PolyCell.Core

open LeanFX2

/-! ## Section 1 — The cast composition keystone

For non-var generators, the payload type doesn't depend on scope.
This means: two successive scope-invariance casts (src→mid then
mid→tgt) yield the same value as a single cast (src→tgt).

This is the keystone that unblocks ALL term-level cross-direction
fusion (rename_compose here, subst_rename_commute,
rename_subst_commute, lift_compose for subst). -/

/-- Cast composition for non-var payloads: chained casts equal a
single cast.

For each non-var Generator, `Generator.payload someGenerator scope`
reduces to a fixed type independent of `scope`.  Therefore both
sides of the equation reduce to the original `payload`, closing
by `rfl` per non-var arm.

The proof has the same shape as
`Generator.payload_scope_invariant_of_not_var`: `cases generator`,
discharge `gen_var` via `absurd`, then `all_goals rfl` for the 193
non-var generators. -/
theorem Generator.payload_cast_compose
    {generator : Generator} (hNotVar : generator ≠ .gen_var)
    (sourceScope middleScope targetScope : Nat)
    (somePayload : generator.payload sourceScope) :
    (Generator.payload_scope_invariant_of_not_var hNotVar middleScope targetScope) ▸
      ((Generator.payload_scope_invariant_of_not_var hNotVar sourceScope middleScope) ▸
          somePayload)
    = (Generator.payload_scope_invariant_of_not_var hNotVar sourceScope targetScope) ▸
        somePayload := by
  cases generator
  case gen_var => exact absurd rfl hNotVar
  all_goals rfl

/-! ## Section 2 — The term-level renaming fusion

In v1: 74-arm structural induction.
In v2: 4-arm mutual induction reusing foldV2's dispatch + the cast
keystone above. -/

mutual

/-- Renaming-renaming fusion: applying two renamings sequentially
equals applying their composition.

This is the rename-side analog of `subst_compose` (and a stepping
stone toward it).  v2 replacement for v1's 74-arm
`RawTerm.rename_compose`. -/
theorem RawTermV2.rename_compose
    {sourceScope middleScope targetScope : Nat}
    (firstRenaming : LeanFX2.RawRenaming sourceScope middleScope)
    (secondRenaming : LeanFX2.RawRenaming middleScope targetScope)
    (sourceTerm : RawTermV2 sourceScope) :
    RawTermV2.rename secondRenaming
        (RawTermV2.rename firstRenaming sourceTerm) =
      RawTermV2.rename
        (LeanFX2.RawRenaming.compose firstRenaming secondRenaming)
        sourceTerm := by
  match sourceTerm with
  | .mkGen someGenerator somePayload someChildren =>
    by_cases hVar : someGenerator = .gen_var
    case pos =>
      subst hVar
      -- Variable arm: both LHS and RHS reduce to
      -- `mkGen .gen_var (rho2 (rho1 somePayload)) .childNil`.
      -- (compose rho1 rho2 pos = rho2 (rho1 pos))
      match someChildren with
      | .childNil => rfl
    case neg =>
      -- Non-variable arm.  Both LHS and RHS dispatch to the algebra
      -- branch.  After unfolding, the difference is in the cast on
      -- the payload (LHS chains two; RHS uses one) and in the
      -- children fold (LHS folds twice; RHS folds once with compose).
      show RawTermV2.rename secondRenaming
              (RawTermV2.rename firstRenaming
                  (.mkGen someGenerator somePayload someChildren)) =
            RawTermV2.rename
              (LeanFX2.RawRenaming.compose firstRenaming secondRenaming)
              (.mkGen someGenerator somePayload someChildren)
      -- Step 1: unfold both renames + collapse their `if hVar`
      -- dispatches.  TWO passes of dsimp+simp_only are needed
      -- because dsimp doesn't auto-iterate through the OUTER foldV2
      -- after the inner produces a fresh mkGen.
      --
      -- Pass 1: outer rename unfolds; inner rename's foldV2 unfolds
      -- (its match reduces because sourceTerm IS `.mkGen ...`).  The
      -- outer foldV2 sees the inner's algebra-applied result later.
      dsimp only [RawTermV2.rename, foldV2, GenAlgebraV2.canonical]
      simp only [dif_neg hVar]
      -- After pass 1, the LHS still has `foldV2 _ secondRenaming
      -- (mkGen ... innerResult)` — the outer foldV2 isn't yet
      -- unfolded.  Pass 2 forces the outer foldV2 to see the
      -- mkGen and dispatch.
      dsimp only [foldV2, GenAlgebraV2.canonical]
      simp only [dif_neg hVar]
      -- Now both sides are flat:
      --   LHS: mkGen g (eq2 ▸ eq1 ▸ p) (foldChildren rho2 (foldChildren rho1 c))
      --   RHS: mkGen g (eq3 ▸ p) (foldChildren (compose rho1 rho2) c)
      -- congr 1 peels off mkGen, generating subgoals.
      congr 1
      · -- Cast composition subgoal.
        exact Generator.payload_cast_compose hVar
                sourceScope middleScope targetScope somePayload
      · -- Children fusion subgoal (mutual IH).
        exact RawTermChildrenV2.rename_compose
                firstRenaming secondRenaming someChildren

/-- Renaming-renaming fusion on children spines.

In the cons case, the head sits under `headShift`-many binders, so
the renamings lift to `iterateLiftRaw rho_i headShift`.  The head IH
gives:

  rename (iter rho2 shift) (rename (iter rho1 shift) head)
    = rename (compose (iter rho1 shift) (iter rho2 shift)) head

To match the RHS shape, we bridge via
`iterateLiftRaw_RawRenaming_compose_pointwise` (from #181c2):

  iter (compose rho1 rho2) shift ≅ compose (iter rho1 shift) (iter rho2 shift)

The symmetric direction lets us rewrite back into `iter compose` form,
matching the RHS.  `RawTermV2.rename_pointwise` (from #181c1) does the
conversion at the head's scope. -/
theorem RawTermChildrenV2.rename_compose
    {sourceScope middleScope targetScope : Nat}
    (firstRenaming : LeanFX2.RawRenaming sourceScope middleScope)
    (secondRenaming : LeanFX2.RawRenaming middleScope targetScope)
    {binderShifts : List Nat}
    (someChildren : RawTermChildrenV2 binderShifts sourceScope) :
    RawTermChildrenV2.rename secondRenaming
        (RawTermChildrenV2.rename firstRenaming someChildren) =
      RawTermChildrenV2.rename
        (LeanFX2.RawRenaming.compose firstRenaming secondRenaming)
        someChildren := by
  match binderShifts, someChildren with
  | [], .childNil =>
      rfl
  | headShift :: _, .childCons childHead childTail =>
      show RawTermChildrenV2.childCons
              (RawTermV2.rename (iterateLiftRaw secondRenaming headShift)
                  (RawTermV2.rename (iterateLiftRaw firstRenaming headShift)
                      childHead))
              (RawTermChildrenV2.rename secondRenaming
                  (RawTermChildrenV2.rename firstRenaming childTail)) =
            RawTermChildrenV2.childCons
              (RawTermV2.rename
                  (iterateLiftRaw
                      (LeanFX2.RawRenaming.compose firstRenaming secondRenaming)
                      headShift)
                  childHead)
              (RawTermChildrenV2.rename
                  (LeanFX2.RawRenaming.compose firstRenaming secondRenaming)
                  childTail)
      -- Head: apply rename_compose at the LIFTED scope.
      have headFusionRaw := RawTermV2.rename_compose
                              (iterateLiftRaw firstRenaming headShift)
                              (iterateLiftRaw secondRenaming headShift)
                              childHead
      -- headFusionRaw :
      --   rename (iter rho2 shift) (rename (iter rho1 shift) head)
      --   = rename (compose (iter rho1 shift) (iter rho2 shift)) head
      -- We want the RHS-side renaming to be
      -- `iter (compose rho1 rho2) shift`, not
      -- `compose (iter rho1 shift) (iter rho2 shift)`.  Bridge via
      -- the iterateLiftRaw compose pointwise lemma in reverse.
      have iterLiftBridgeForward :=
        iterateLiftRaw_RawRenaming_compose_pointwise
          firstRenaming secondRenaming headShift
      -- iterLiftBridgeForward :
      --   iter (compose rho1 rho2) shift pos
      --   = compose (iter rho1 shift) (iter rho2 shift) pos
      -- We need the symmetric direction at the head scope, then
      -- apply rename_pointwise on it.
      have headRenameBridge :
          RawTermV2.rename
              (LeanFX2.RawRenaming.compose
                  (iterateLiftRaw firstRenaming headShift)
                  (iterateLiftRaw secondRenaming headShift))
              childHead =
            RawTermV2.rename
              (iterateLiftRaw
                  (LeanFX2.RawRenaming.compose firstRenaming secondRenaming)
                  headShift)
              childHead :=
        RawTermV2.rename_pointwise
          (fun position => (iterLiftBridgeForward position).symm)
          childHead
      -- Tail: direct mutual IH.
      have tailFusion :=
        RawTermChildrenV2.rename_compose
          firstRenaming secondRenaming childTail
      -- Chain: head IH, head bridge, tail IH.
      rw [headFusionRaw, headRenameBridge, tailFusion]

end -- mutual

/-! ## Section 3 — Smoke tests

Verify the headline `RawTermV2.rename_compose` invokes cleanly on
representative terms. -/

/-- Smoke: rename_compose on `.gen_unit` closes by direct application
(the term has no variables, so the result is the same `gen_unit`
regardless of renamings). -/
theorem RawTermV2.rename_compose_unit_smoke
    {sourceScope middleScope targetScope : Nat}
    (firstRenaming : LeanFX2.RawRenaming sourceScope middleScope)
    (secondRenaming : LeanFX2.RawRenaming middleScope targetScope) :
    RawTermV2.rename secondRenaming
        (RawTermV2.rename firstRenaming
            (.mkGen .gen_unit () .childNil : RawTermV2 sourceScope)) =
      RawTermV2.rename
        (LeanFX2.RawRenaming.compose firstRenaming secondRenaming)
        (.mkGen .gen_unit () .childNil : RawTermV2 sourceScope) :=
  RawTermV2.rename_compose firstRenaming secondRenaming _

/-- Smoke: rename_compose on `.gen_var` at position 0 — exercises
the variable arm of the mutual induction. -/
theorem RawTermV2.rename_compose_var_smoke
    {sourceScope middleScope targetScope : Nat}
    (firstRenaming :
        LeanFX2.RawRenaming (sourceScope + 1) (middleScope + 1))
    (secondRenaming :
        LeanFX2.RawRenaming (middleScope + 1) (targetScope + 1)) :
    RawTermV2.rename secondRenaming
        (RawTermV2.rename firstRenaming
            (.mkGen .gen_var
                    (⟨0, Nat.zero_lt_succ sourceScope⟩ : Fin (sourceScope + 1))
                    .childNil)) =
      RawTermV2.rename
        (LeanFX2.RawRenaming.compose firstRenaming secondRenaming)
        (.mkGen .gen_var
                (⟨0, Nat.zero_lt_succ sourceScope⟩ : Fin (sourceScope + 1))
                .childNil) :=
  RawTermV2.rename_compose firstRenaming secondRenaming _

end LeanFX2.Foundation.PolyCell.Core
