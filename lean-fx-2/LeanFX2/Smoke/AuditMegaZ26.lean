import LeanFX2.Foundation.TyAct
import LeanFX2.Smoke.AuditMegaZ25

/-! # AuditMegaZ26 — Zero-axiom audit for Tier 3 / MEGA-Z2.6.

MEGA-Z2.6 ships the native `Ty.act`-layer infrastructure that breaks
the `Subst.compose ↔ Ty.subst` circular dependency.  All three
theorems must report "does not depend on any axioms".

The Pattern 3 (homogeneous Allais paired-env), W8 (Tait-Martin-Löf
confluence), and Heterogeneous Univalence headliners must continue to
report zero-axiom — adding `Foundation/TyAct.lean` to the dependency
chain must NOT introduce any axioms anywhere downstream.  This file
imports `AuditMegaZ25` to inherit its zero-axiom regression checks
without duplication.

## What ships

* `Ty.act_pointwise` — extensionality on `Ty.act`.  Two actions
  (possibly distinct Containers) agree on `Ty.act` when they agree
  pointwise on `varToTy`/`actOnRawTerm` and the property survives
  binder lifts.

* `Ty.act_compose` — multi-Container composition.  Three Containers
  (`first`, `second`, `composed`) plus compatibility witnesses (var
  + raw + lift propagation), no dependence on `Action.compose` —
  hence no cycle through `Ty.subst_compose`.

* `Ty.act_identity` — identity law.  An action that acts as identity
  at every scope (varToTy = tyVar, actOnRawTerm = id, propagated under
  lifts) yields `Ty.act t action = t`.

## Proof discipline verified

Every proof body in `Foundation/TyAct.lean` uses `simp only [Ty.act]`
with EXPLICIT lemma list.  None of the proofs invoke
`Ty.subst_compose`, `Ty.subst_pointwise`, or any other lemma whose
proof transitively depends on `Ty.subst`'s body.  Verified by `rg`
over the file body.
-/

-- ============================================================
-- Section 1: The three Z2.6 native theorems (headline deliverable)
-- ============================================================

#print axioms LeanFX2.Ty.act_pointwise
#print axioms LeanFX2.Ty.act_compose
#print axioms LeanFX2.Ty.act_identity

-- ============================================================
-- Section 2: Z2.6 supporting predicates
-- ============================================================

#print axioms LeanFX2.ActPointwiseAgree
#print axioms LeanFX2.ActComposeCompat
#print axioms LeanFX2.ActsAsIdentity

-- ============================================================
-- Section 3: Headliner regression — Pattern 3 (homogeneous Allais)
-- ============================================================

#print axioms LeanFX2.ConvCumul.subst_compatible
#print axioms LeanFX2.ConvCumulHomo.subst_compatible_paired_allais

-- ============================================================
-- Section 4: Headliner regression — W8 Church-Rosser
-- ============================================================

#print axioms LeanFX2.RawStep.par.cd_lemma
#print axioms LeanFX2.RawStep.par.diamond
#print axioms LeanFX2.RawStep.parStar.confluence
#print axioms LeanFX2.Conv.canonicalForm

-- ============================================================
-- Section 5: Headliner regression — Heterogeneous Univalence
-- ============================================================

#print axioms LeanFX2.Univalence
#print axioms LeanFX2.UnivalenceHet
#print axioms LeanFX2.funext

-- ============================================================
-- Section 6: Z2.A bridge equivalence (must remain clean after Z2.6)
-- ============================================================

#print axioms LeanFX2.Ty.act_eq_rename
#print axioms LeanFX2.Ty.act_eq_subst
#print axioms LeanFX2.Ty.act_eq_weaken
