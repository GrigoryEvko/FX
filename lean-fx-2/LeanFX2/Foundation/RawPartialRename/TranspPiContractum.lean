import LeanFX2.Foundation.RawPartialRename.Swap01
import LeanFX2.Foundation.RawSubst.SubstIdentityAndBeta

/-! # LeanFX2.Foundation.RawPartialRename.TranspPiContractum

Raw-level builder for the D2.5.5 transpPi β contractum.  CCHM cubical
transport through a Π type with constant-domain path:

  transp (λ i ⇒ Π A B) f  ⟶  λ x. transp (λ i ⇒ B'[i, x]) (f.weaken @ x)

In de Bruijn at scope `N`: the original codomain
`pathCodomain : RawTerm (N+2)` has slot 0 = Pi-binder (x) and slot 1
= pathLam interval (i).  The contractum's inner `pathLam` binds a
fresh interval (j) at slot 0 and the outer `lam` binds x at slot 1,
so `pathCodomain` must be re-indexed via `swap01` to land in the new
scope structure.

This file ships the contractum as a standalone builder plus its
rename and subst commute lemmas, derived from the
`RawTerm.swap01_rename_lift_lift_commute` /
`RawTerm.swap01_subst_lift_lift_commute` pair shipped in
`Swap01.lean` and the kernel's `RawTerm.weaken_rename_commute` /
`RawTerm.weaken_subst_commute` primitives.

## Root status

Layer 0 raw-syntax foundation primitive.  Strict zero-axiom.
Consumed by the future D2.5.5 cascade:

* `Confluence/RawCd/CubicalAndEquiv.lean` — `cdTranspPiCase` β arm
  fires this contractum.
* `Reduction/RawPar.lean` — `RawStep.par.transpPiBeta` ctor target
  uses this contractum.
* `Confluence/RawCdLemma.lean` — transpPi β arm dispatch.
* `Reduction/RawParCompatible.lean` — rename + subst arms close via
  the two `_rename` / `_subst` commutes here.

Per `feedback_d255_d256_blocker_2026_05_15.md`, the par cascade is
still pending Phases E-K; this file is one of the small foundation
primitives the par ctor's contractum design references.

## Phase F dispatcher design RFC (blocker #1951 resolution, Path 2)

`cdTranspCase`'s `pathLam pathBody` branch currently dispatches:

  `unweaken? pathBody = some _ → developedSource`  (transpReflBeta)
  `unweaken? pathBody = none   → transp cong`     (no β fires)

The transpPi β rule fires inside the `none` branch when pathBody has
the CCHM shape `piTyCode A.weaken B` with B genuinely depending on the
interval (i.e. the WHOLE piTyCode does NOT unweaken — otherwise
transpReflBeta wins).  The dispatch is disjoint by construction:

  * **transpReflBeta**: premise `unweaken? pathBody = some _` —
    the entire path body is in the image of `weaken`, so the path is
    the constant path `λ i ⇒ T`.
  * **transpPiBeta**: premise `unweaken? pathBody = none` AND
    pathBody syntactically equals `piTyCode A.weaken B` for some
    `A : RawTerm scope`, `B : RawTerm (scope+2)`.

These two premises cannot both hold: if pathBody equals
`piTyCode A.weaken B`, `unweaken?` of piTyCode is the conjunctive
check on its children — `unweaken? (A.weaken) = some A` always
succeeds, so the disjunctive failure must come from B failing to
unweaken-at-shifted-position-1 (i.e. B uses the interval).  Conversely,
when pathBody DOES unweaken, B must unweaken at slot 1, which means
the CCHM rule is vacuous (transport through a Π type whose codomain
ignores the interval = transport through a constant type).

The previous Phase A attempt (commit 067ed74, rolled back) used a
`decide (domainCode = codomainUnweakened)` test in the dispatcher;
that approach is Path 1 (decidable structural equality) and was
brittle under non-injective renamings.  Path 2 (disjoint-premise
split) avoids the structural-equality check entirely by relying on
unweaken? disjointness.

Phase F implementation outline (Phase G consumes):

1. Extend `RawStep.par` with `transpPiBeta` ctor whose LHS pattern
   is `RawTerm.transp (RawTerm.pathLam (RawTerm.piTyCode A.weaken B))
   sourceRaw` and whose target uses `transpPiBetaContractum`.  Add a
   premise carrying the witness `B_unweakens_at_slot1 = none` (the
   negation of transpReflBeta's premise).
2. Extend `cdTranspCase`'s `pathLam _` `none` branch with an inner
   `match pathBody` checking for `piTyCode _ _` shape.  When the shape
   matches AND `unweaken? domainCode = some A` succeeds (domain doesn't
   use interval), fire `transpPiBetaContractum codomainCode source`.
   Otherwise fall back to `transp cong`.
3. The deep variant `transpPiBetaDeep` mirrors the shallow ctor with
   `pathRaw →par pathLam (piTyCode A.weaken B)` premise — needed for
   cd_dominates discharge when the path is not literally the β-shape
   on the LHS but reaches it under cd development.

This RFC is the design contract Phase F implements.  No code shipped
here beyond the foundation primitives (def + commutes); Phase F lands
the par ctors + cd extension + cd_lemma arm as a separate cascade. -/

namespace LeanFX2

/-- D2.5.5 transpPi β contractum at scope `N`.  Given:

* `pathCodomain : RawTerm (N+2)` — the original Π-codomain B with
  slot 0 = Π-binder, slot 1 = pathLam interval
* `developedSource : RawTerm N` — the (post-cd) Π-function f

builds the contractum

  `λ x. transp (pathLam (B.rename swap01)) (f.weaken @ x)`

where:

* outer `λ x` binds the Π argument (new slot 0)
* inner `pathLam` binds a fresh interval (new slot 0 at scope N+2)
* `B.rename swap01` re-indexes B so j is slot 0 and x is slot 1
* `f.weaken @ x` η-expands f at the new outer-`lam` scope

Marked `@[reducible]` so the def unfolds in `show`-based proofs
that need to see the explicit lam-transp-pathLam-app-var structure
(per `feedback_lean_reducible_weaken.md`). -/
@[reducible]
def RawTerm.transpPiBetaContractum {scope : Nat}
    (pathCodomain : RawTerm (scope + 2))
    (developedSource : RawTerm scope) : RawTerm scope :=
  RawTerm.lam (
    RawTerm.transp
      (RawTerm.pathLam (pathCodomain.rename RawRenaming.swap01))
      (RawTerm.app developedSource.weaken
        (RawTerm.var ⟨0, Nat.zero_lt_succ _⟩))
  )

/-- The contractum commutes with rename: renaming the whole
contractum by `rho` agrees with rebuilding the contractum after
renaming its inputs.

Proof: rename of `lam` descends with `rho.lift`; rename of `transp`
/ `pathLam` / `app` is homomorphic; the pathLam-body needs swap01
to commute with `rho.lift.lift` (`swap01_rename_lift_lift_commute`);
the app's function arg needs `weaken` to commute with `rho.lift`
(`weaken_rename_commute`); the app's argument `var ⟨0, _⟩` is
preserved by `rho.lift` definitionally (lift sends slot 0 to slot
0).

Consumed by future `RawParRename.lean` arm for
`RawStep.par.transpPiBeta`. -/
theorem RawTerm.transpPiBetaContractum_rename
    {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    (pathCodomain : RawTerm (sourceScope + 2))
    (developedSource : RawTerm sourceScope) :
    (RawTerm.transpPiBetaContractum pathCodomain developedSource).rename rho =
    RawTerm.transpPiBetaContractum
      (pathCodomain.rename rho.lift.lift)
      (developedSource.rename rho) := by
  show RawTerm.lam (
    RawTerm.transp
      (RawTerm.pathLam ((pathCodomain.rename RawRenaming.swap01).rename rho.lift.lift))
      (RawTerm.app (developedSource.weaken.rename rho.lift)
        (RawTerm.var ⟨0, Nat.zero_lt_succ _⟩))
  ) = RawTerm.lam (
    RawTerm.transp
      (RawTerm.pathLam ((pathCodomain.rename rho.lift.lift).rename RawRenaming.swap01))
      (RawTerm.app ((developedSource.rename rho).weaken)
        (RawTerm.var ⟨0, Nat.zero_lt_succ _⟩))
  )
  rw [RawTerm.swap01_rename_lift_lift_commute, RawTerm.weaken_rename_commute]

/-- The contractum commutes with subst: substituting the whole
contractum by `sigma` agrees with rebuilding the contractum after
substituting its inputs.

Proof: same structure as rename — `pathCodomain.rename swap01`
under `sigma.lift.lift` aligns via `swap01_subst_lift_lift_commute`;
`developedSource.weaken` under `sigma.lift` aligns via
`weaken_subst_commute`; `var ⟨0, _⟩` is preserved by `sigma.lift`
definitionally (`sigma.lift` sends slot 0 to `var ⟨0, _⟩`).

Consumed by future `RawParCompatible.lean` arm for
`RawStep.par.transpPiBeta`. -/
theorem RawTerm.transpPiBetaContractum_subst
    {sourceScope targetScope : Nat}
    (sigma : RawTermSubst sourceScope targetScope)
    (pathCodomain : RawTerm (sourceScope + 2))
    (developedSource : RawTerm sourceScope) :
    (RawTerm.transpPiBetaContractum pathCodomain developedSource).subst sigma =
    RawTerm.transpPiBetaContractum
      (pathCodomain.subst sigma.lift.lift)
      (developedSource.subst sigma) := by
  show RawTerm.lam (
    RawTerm.transp
      (RawTerm.pathLam ((pathCodomain.rename RawRenaming.swap01).subst sigma.lift.lift))
      (RawTerm.app (developedSource.weaken.subst sigma.lift)
        (RawTerm.var ⟨0, Nat.zero_lt_succ _⟩))
  ) = RawTerm.lam (
    RawTerm.transp
      (RawTerm.pathLam ((pathCodomain.subst sigma.lift.lift).rename RawRenaming.swap01))
      (RawTerm.app (developedSource.subst sigma).weaken
        (RawTerm.var ⟨0, Nat.zero_lt_succ _⟩))
  )
  rw [RawTerm.swap01_subst_lift_lift_commute, RawTerm.weaken_subst_commute]

end LeanFX2
