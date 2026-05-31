import FX1Poly.Core.RawTermRenameCompose

/-! # Foundation/PolyCell/Core/RawTermRenameComposeFusion — term-level renaming fusion

The **term-level renaming fusion**:

  RawTerm.rename rho2 (RawTerm.rename rho1 term)
    = RawTerm.rename (RawRenaming.compose rho1 rho2) term

— the polynomial monad's associativity at the renaming layer.

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

This is `Generator.payload_cast_compose`.  It's a 193-arm
`all_goals rfl` after the var case is dispatched as
`absurd rfl hNotVar` — the same pattern as
`Generator.payload_scope_invariant_of_not_var`.

For each specific non-var generator, the payload type is a concrete
type (Unit, Nat, etc.) independent of scope, so both casts reduce
to the identity AND chain to the identity — all `rfl`.

## The main fusion theorem

`RawTerm.rename_compose` is a mutual structural induction with the
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
  bridge via `iterateLiftRaw_RawRenaming_compose_pointwise`
  to convert `compose (lift r1) (lift r2)` → `lift (compose r1 r2)`.

## Why double-unfolding is needed

The LHS `rename rho2 (rename rho1 (mkGen ...))` involves TWO renames.
After `dsimp only [RawTerm.rename, fold]`, both occurrences unfold
but the inner result is `mkGen g (eq_src_mid ▸ p) (foldChildren rho1 c)`
— a NEW `mkGen` that the outer rename hasn't yet processed.

A second pass of `dsimp + simp_only [dif_neg hVar]` (with the outer
rename's fold dispatch) is needed.  Specifically:
1. `dsimp only [RawTerm.rename, fold]` — unfolds outer rename
   one step and inner rename fully (because the inner has the
   matchable `mkGen` directly).
2. `simp only [dif_neg hVar]` — collapses the inner's `if hVar : g =
   .gen_var` to else branch.
3. `dsimp only [RawTerm.rename, fold, GenAlgebra.canonical]` —
   forces the outer's `match` to see the `mkGen` produced by the
   inner, unfolds the outer's fold.
4. `simp only [dif_neg hVar]` again — collapses the outer's dispatch.
5. Now both sides are flat `mkGen g (cast) (foldChildren-...) ` form;
   `congr 1` peels off into cast + children subgoals.

In practice, packing this into one `dsimp + simp_only + dsimp +
simp_only` sequence works.  If issues arise, can be split into a
helper unfolding lemma `RawTerm.rename_nonvar`.

## Zero-axiom verification

All declarations propext-free:
* `Generator.payload_cast_compose` — `cases generator + absurd + all_goals rfl`,
  same pattern as `payload_scope_invariant_of_not_var`.
* Mutual `RawTerm.rename_compose` / `RawTermChildren.rename_compose` —
  `dsimp only [fold]` (NOT `unfold` — Quot.sound trap), `simp only
  [dif_neg]`, `congr` + cast helper + mutual IH.

Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`.

## Structure

`RawTerm.rename_compose` is a 4-arm mutual induction:
* `.mkGen` var sub-case
* `.mkGen` non-var sub-case
* `.childNil`
* `.childCons`

The Generator dispatch is amortized into fold plus the cast
composition helper.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

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

A 4-arm mutual induction reusing fold's dispatch + the cast
keystone above. -/

mutual

/-- Renaming-renaming fusion: applying two renamings sequentially
equals applying their composition.

This is the rename-side analog of `subst_compose` (and a stepping
stone toward it). -/
theorem RawTerm.rename_compose
    {sourceScope middleScope targetScope : Nat}
    (firstRenaming : FX1Poly.Foundation.RawRenaming sourceScope middleScope)
    (secondRenaming : FX1Poly.Foundation.RawRenaming middleScope targetScope)
    (sourceTerm : RawTerm sourceScope) :
    RawTerm.rename secondRenaming
        (RawTerm.rename firstRenaming sourceTerm) =
      RawTerm.rename
        (FX1Poly.Foundation.RawRenaming.compose firstRenaming secondRenaming)
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
      show RawTerm.rename secondRenaming
              (RawTerm.rename firstRenaming
                  (.mkGen someGenerator somePayload someChildren)) =
            RawTerm.rename
              (FX1Poly.Foundation.RawRenaming.compose firstRenaming secondRenaming)
              (.mkGen someGenerator somePayload someChildren)
      -- Step 1: unfold both renames + collapse their `if hVar`
      -- dispatches.  TWO passes of dsimp+simp_only are needed
      -- because dsimp doesn't auto-iterate through the OUTER fold
      -- after the inner produces a fresh mkGen.
      --
      -- Pass 1: outer rename unfolds; inner rename's fold unfolds
      -- (its match reduces because sourceTerm IS `.mkGen ...`).  The
      -- outer fold sees the inner's algebra-applied result later.
      dsimp only [RawTerm.rename, fold, GenAlgebra.canonical]
      simp only [dif_neg hVar]
      -- After pass 1, the LHS still has `fold _ secondRenaming
      -- (mkGen ... innerResult)` — the outer fold isn't yet
      -- unfolded.  Pass 2 forces the outer fold to see the
      -- mkGen and dispatch.
      dsimp only [fold, GenAlgebra.canonical]
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
        exact RawTermChildren.rename_compose
                firstRenaming secondRenaming someChildren

/-- Renaming-renaming fusion on children spines.

In the cons case, the head sits under `headShift`-many binders, so
the renamings lift to `iterateLiftRaw rho_i headShift`.  The head IH
gives:

  rename (iter rho2 shift) (rename (iter rho1 shift) head)
    = rename (compose (iter rho1 shift) (iter rho2 shift)) head

To match the RHS shape, we bridge via
`iterateLiftRaw_RawRenaming_compose_pointwise`:

  iter (compose rho1 rho2) shift ≅ compose (iter rho1 shift) (iter rho2 shift)

The symmetric direction lets us rewrite back into `iter compose` form,
matching the RHS.  `RawTerm.rename_pointwise` does the
conversion at the head's scope. -/
theorem RawTermChildren.rename_compose
    {sourceScope middleScope targetScope : Nat}
    (firstRenaming : FX1Poly.Foundation.RawRenaming sourceScope middleScope)
    (secondRenaming : FX1Poly.Foundation.RawRenaming middleScope targetScope)
    {binderShifts : List Nat}
    (someChildren : RawTermChildren binderShifts sourceScope) :
    RawTermChildren.rename secondRenaming
        (RawTermChildren.rename firstRenaming someChildren) =
      RawTermChildren.rename
        (FX1Poly.Foundation.RawRenaming.compose firstRenaming secondRenaming)
        someChildren := by
  match binderShifts, someChildren with
  | [], .childNil =>
      rfl
  | headShift :: _, .childCons childHead childTail =>
      show RawTermChildren.childCons
              (RawTerm.rename (iterateLiftRaw secondRenaming headShift)
                  (RawTerm.rename (iterateLiftRaw firstRenaming headShift)
                      childHead))
              (RawTermChildren.rename secondRenaming
                  (RawTermChildren.rename firstRenaming childTail)) =
            RawTermChildren.childCons
              (RawTerm.rename
                  (iterateLiftRaw
                      (FX1Poly.Foundation.RawRenaming.compose firstRenaming secondRenaming)
                      headShift)
                  childHead)
              (RawTermChildren.rename
                  (FX1Poly.Foundation.RawRenaming.compose firstRenaming secondRenaming)
                  childTail)
      -- Head: apply rename_compose at the LIFTED scope.
      have headFusionRaw := RawTerm.rename_compose
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
          RawTerm.rename
              (FX1Poly.Foundation.RawRenaming.compose
                  (iterateLiftRaw firstRenaming headShift)
                  (iterateLiftRaw secondRenaming headShift))
              childHead =
            RawTerm.rename
              (iterateLiftRaw
                  (FX1Poly.Foundation.RawRenaming.compose firstRenaming secondRenaming)
                  headShift)
              childHead :=
        RawTerm.rename_pointwise
          (fun position => (iterLiftBridgeForward position).symm)
          childHead
      -- Tail: direct mutual IH.
      have tailFusion :=
        RawTermChildren.rename_compose
          firstRenaming secondRenaming childTail
      -- Chain: head IH, head bridge, tail IH.
      rw [headFusionRaw, headRenameBridge, tailFusion]

end -- mutual

/-! ## Section 3 — Smoke tests

Verify the headline `RawTerm.rename_compose` invokes cleanly on
representative terms. -/

/-- Smoke: rename_compose on `.gen_unit` closes by direct application
(the term has no variables, so the result is the same `gen_unit`
regardless of renamings). -/
theorem RawTerm.rename_compose_unit_smoke
    {sourceScope middleScope targetScope : Nat}
    (firstRenaming : FX1Poly.Foundation.RawRenaming sourceScope middleScope)
    (secondRenaming : FX1Poly.Foundation.RawRenaming middleScope targetScope) :
    RawTerm.rename secondRenaming
        (RawTerm.rename firstRenaming
            (.mkGen .gen_unit () .childNil : RawTerm sourceScope)) =
      RawTerm.rename
        (FX1Poly.Foundation.RawRenaming.compose firstRenaming secondRenaming)
        (.mkGen .gen_unit () .childNil : RawTerm sourceScope) :=
  RawTerm.rename_compose firstRenaming secondRenaming _

/-- Smoke: rename_compose on `.gen_var` at position 0 — exercises
the variable arm of the mutual induction. -/
theorem RawTerm.rename_compose_var_smoke
    {sourceScope middleScope targetScope : Nat}
    (firstRenaming :
        FX1Poly.Foundation.RawRenaming (sourceScope + 1) (middleScope + 1))
    (secondRenaming :
        FX1Poly.Foundation.RawRenaming (middleScope + 1) (targetScope + 1)) :
    RawTerm.rename secondRenaming
        (RawTerm.rename firstRenaming
            (.mkGen .gen_var
                    (⟨0, Nat.zero_lt_succ sourceScope⟩ : Fin (sourceScope + 1))
                    .childNil)) =
      RawTerm.rename
        (FX1Poly.Foundation.RawRenaming.compose firstRenaming secondRenaming)
        (.mkGen .gen_var
                (⟨0, Nat.zero_lt_succ sourceScope⟩ : Fin (sourceScope + 1))
                .childNil) :=
  RawTerm.rename_compose firstRenaming secondRenaming _

end FX1Poly.Core
