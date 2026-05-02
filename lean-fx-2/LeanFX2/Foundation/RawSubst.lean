import LeanFX2.Foundation.RawTerm

/-! # RawSubst — substitution algebra on untyped terms.

`RawTermSubst source target` is `Fin source → RawTerm target`.
`RawRenaming source target` is `Fin source → Fin target`.

## Operations

* `RawTermSubst.identity : RawTermSubst scope scope`
* `RawTermSubst.lift : RawTermSubst src tgt → RawTermSubst (src+1) (tgt+1)`
* `RawTermSubst.singleton (rawArg : RawTerm scope) : RawTermSubst (scope+1) scope`
  — single-binder substitution: position 0 → rawArg, position k+1 → var k
* `RawTermSubst.compose : RawTermSubst a b → RawTermSubst b c → RawTermSubst a c`
* `RawRenaming.identity`, `lift`, `weaken` (shift-by-one)
* `RawTerm.rename : RawTerm src → RawRenaming src tgt → RawTerm tgt`
* `RawTerm.subst : RawTerm src → RawTermSubst src tgt → RawTerm tgt`

## Critical removal vs lean-fx

* **NO `dropNewest`**.  lean-fx had `RawTermSubst.dropNewest : RawTermSubst (scope+1) scope`
  that mapped position 0 → `RawTerm.unit` and position k+1 → `RawTerm.var k`.
  This was a placeholder used by `Subst.singleton.forRaw` to handle the binder
  case "without an argument" — but in lean-fx-2's raw-aware Term, every typed
  binder has a substituted argument's raw form pinned by the type index, so the
  placeholder is never needed.  Substitution always uses `RawTermSubst.singleton`.

## Composition laws

* `compose_assoc : compose (compose σ τ) υ = compose σ (compose τ υ)`
* `lift_compose : (compose σ τ).lift = compose σ.lift τ.lift`
* `subst_subst : (raw.subst σ).subst τ = raw.subst (compose σ τ)`
* `rename_subst : (raw.rename ρ).subst σ = raw.subst (compose (renamingToSubst ρ) σ)`

These are all axiom-free (structural induction on RawTerm).

## Dependencies

* `Foundation/RawTerm.lean` — the raw term family

## Downstream

* `Foundation/Subst.lean` — joint substitution embeds a `RawTermSubst`
* `Reduction/RawPar.lean` — raw reduction uses `RawTerm.subst` for β-reducts
-/

namespace LeanFX2

-- TODO: RawRenaming + RawRenaming.identity + RawRenaming.lift + RawRenaming.weaken
-- TODO: RawTerm.rename (structural recursion)
-- TODO: RawTermSubst structure
-- TODO: RawTermSubst.identity + RawTermSubst.lift + RawTermSubst.singleton
-- TODO: RawTermSubst.compose
-- TODO: RawTerm.subst (structural recursion)
-- TODO: composition + commutation lemmas (axiom-free)

end LeanFX2
