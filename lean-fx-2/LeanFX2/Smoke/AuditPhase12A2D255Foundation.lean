import LeanFX2.Foundation.RawPartialRename.Swap01
import LeanFX2.Foundation.RawPartialRename.TranspPiContractum
import LeanFX2.Foundation.RawPartialRename.TranspPiPathRecognizer

/-! # AuditPhase12A2D255Foundation — D2.5.5 foundation primitives.

Reviewer-facing axiom-cleanliness log for the foundation primitives
that prep the D2.5.5 transpPi β cascade.  Every shipped declaration
in this audit set must report "does not depend on any axioms" — the
per-decl `#assert_no_axioms` gates already fail elaboration on any
axiom leak, so this file is the supplementary regression record.

## What landed

**Swap01 family (commits b042fde, 4836f0c, 37fd585, e93efd6)**

The de Bruijn swap of indices 0 and 1 at scope `N+2`, plus its
function-level and term-level commutes with `rho.lift.lift` /
`sigma.lift.lift`.  Used by the transpPi β contractum to re-index
the original Π-codomain `B : RawTerm (N+2)` (slot 0 = Pi-binder,
slot 1 = pathLam interval) into the contractum's new scope (slot 0
= new pathLam interval, slot 1 = outer-lam Pi-arg).

* `RawRenaming.swap01` — def at `RawRenaming (scope+2) (scope+2)`.
* `RawRenaming.swap01_involution` — function-level self-inverse.
* `RawRenaming.swap01_lift_lift_commute` — pointwise commute with
  `rho.lift.lift` at the renaming level.
* `RawTerm.swap01_rename_lift_lift_commute` — term-level lift via
  `rename_compose` + `rename_pointwise`.
* `RawTerm.swap01_subst_lift_lift_commute` — term-level subst lift
  via `rename_subst_commute` + `subst_rename_commute` +
  `subst_pointwise` with a `rename_compose` detour at the `k+2`
  position.

**Contractum builder (commit f54aea8)**

Single-call builder for the CCHM transpPi β contractum

  `λ x. transp (pathLam (B.rename swap01)) (f.weaken @ x)`

plus its rename and subst commutes.  Future cascade arms in
`cdTranspPiCase`, `RawStep.par.transpPiBeta`, `cd_lemma`, and
`RawParCompatible` reference this single shape.

* `RawTerm.transpPiBetaContractum` — `@[reducible] def` at scope N
  taking `pathCodomain : RawTerm (N+2)` + `developedSource : RawTerm N`.
* `RawTerm.transpPiBetaContractum_rename` — 1-line proof via
  `swap01_rename_lift_lift_commute` + `weaken_rename_commute`.
* `RawTerm.transpPiBetaContractum_subst` — 1-line proof via
  `swap01_subst_lift_lift_commute` + `weaken_subst_commute`.

## Why these matter

The D2.5.5 cascade's Phase E-K work (sub-tickets #1651–#1657)
references this foundation set at every arm:

* `cdTranspPiCase` β arm — returns the contractum directly.
* `RawStep.par.transpPiBeta` ctor — contractum is the reduct.
* `RawParRename` arm — closes via `transpPiBetaContractum_rename`.
* `RawParCompatible` arm — closes via `transpPiBetaContractum_subst`.
* `cd_lemma` transpPi arm — relates par steps to the contractum.

By factoring the contractum into a single `@[reducible] def`, the
four cascade consumers stay aligned: any future change to the
contractum's shape propagates through the def, not via diff-prone
inline duplication.

## Audit

Every declaration below must report "does not depend on any
axioms".  The per-decl `#assert_no_axioms` gates in
`Tools/AuditAll/AuditFoundation.lean` already enforce this; the
`#print axioms` invocations below are supplementary reviewer-
facing regression records.
-/

namespace LeanFX2.Smoke

-- Swap01 def + commutes
#print axioms LeanFX2.RawRenaming.swap01
#print axioms LeanFX2.RawRenaming.swap01_involution
#print axioms LeanFX2.RawRenaming.swap01_lift_lift_commute
#print axioms LeanFX2.RawTerm.swap01_rename_lift_lift_commute
#print axioms LeanFX2.RawTerm.swap01_subst_lift_lift_commute

-- Contractum builder + commutes
#print axioms LeanFX2.RawTerm.transpPiBetaContractum
#print axioms LeanFX2.RawTerm.transpPiBetaContractum_rename
#print axioms LeanFX2.RawTerm.transpPiBetaContractum_subst

-- Phase F dispatch recognizer (commit 2026-05-15)
#print axioms LeanFX2.RawTerm.matchTranspPiBetaShape?

end LeanFX2.Smoke
