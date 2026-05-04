import LeanFX2.Foundation.Ty
import LeanFX2.Foundation.Subst
import LeanFX2.Foundation.SubstActsOnTy
import LeanFX2.Smoke.AuditMegaZ2B
import LeanFX2.Smoke.AuditMegaZ3

/-! # AuditMegaZ25 — MEGA-Z2.5 status audit (structural finding).

## Mission

MEGA-Z2.5 was chartered to break the post-Z3-redirect circular
dependency `Ty.subst → Ty.act → [Action (Subst level)] → Subst.compose
→ Ty.subst` so that the literal Z3 cascade (`Ty.subst t sigma := Ty.act
t sigma`) can elaborate at the definition site of `Ty.subst` in
`Foundation/Subst.lean`.

## Structural finding

The cycle CANNOT be broken by code shuffling within `Foundation/Subst.lean`
alone, regardless of which of the brief's three options is chosen.  The
fundamental obstruction is:

* `Ty.subst`'s post-redirect body `Ty.act t sigma` requires
  `[Action (Subst level)]` to be in scope at line 101 of
  `Foundation/Subst.lean`.
* The `Action (Subst level)` instance lives in `Foundation/Subst.lean`
  itself (currently lines 932-962).  To enable the redirect, the
  instance must be moved to BEFORE line 101.
* The instance's `compose` field is `Subst.compose` (currently lines
  717-724).  Moving the instance up requires either:
    (a) Moving `Subst.compose` up too (forward-references break)
    (b) Inlining the `compose` field as a lambda (Lean does not
        permit self-reference in instance body — see empirical test
        `/tmp/test_self_ref.lean`)
    (c) Using a `mutual` block (Lean does not register the instance
        in the env until elaboration completes — the lambda body's
        `Ty.act` call still cannot synthesize `[Action (Subst level)]`)
* The instance's `compose_assoc_pointwise` proof currently uses
  `Ty.subst_compose` (`Foundation/Subst.lean:751`), which depends on
  `Ty.subst_pointwise`, which depends on `Ty.subst`.  Any move of
  the proof to before `Ty.subst` requires a complete re-derivation
  of associativity at the `Ty.act` layer — which itself requires
  Ty.act's own associativity lemma (`Ty.act_compose`), which does
  not yet exist.

**Empirical confirmation**: When `Subst.compose`'s body is changed from
`(σ.forTy pos).subst σ2` to `Ty.act (σ.forTy pos) σ2` without moving
the Action instance, Lean reports 81 instances of
"failed to synthesize instance of type class `Action (Subst level)`"
across `Foundation/Subst.lean` and downstream files.  When the redirect
is attempted directly (replacing `Ty.subst`'s body with `Ty.act t
sigma`), Lean reports the same error at line 101 of `Foundation/Subst.lean`.

## Recommended path forward (deferred to MEGA-Z6.B)

The cycle resolution requires a more invasive refactor than Z2.5's
charter envisions.  Two viable strategies:

**Strategy A (file split)**: Move `Ty.subst` out of `Foundation/Subst.lean`
into a new `Foundation/TySubst.lean` that imports both Subst.lean (for
the structure) and SubstActsOnTy.lean (for the typeclass instances).
Define `Ty.subst t sigma := Ty.act t sigma` in this new file.  All
existing `Ty.subst`-using theorems in Foundation/Subst.lean (lines 176-893)
must also move to TySubst.lean or stay in Subst.lean re-stated at
Ty.act layer.

**Strategy B (full Z3 cascade in one commit)**: Land Z3 as a single
atomic refactor that simultaneously:
1. Builds Ty.act-layer infrastructure (Ty.act_pointwise, Ty.act_compose,
   Ty.act_identity, etc.) in Foundation/Ty.lean upstream.
2. Defines the Action instance in Foundation/Ty.lean using only
   structural facts (no Ty.subst dependence).
3. Redirects Ty.subst, Ty.rename, Ty.weaken to Ty.act in
   Foundation/Subst.lean.
4. Cascades the ~250 `simp only [Ty.subst]` / `simp only [Ty.rename]`
   sites to use Ty.act unfolding.

This is the chartered scope of MEGA-Z6.B per `Smoke/AuditMegaZ3.lean`'s
docstring.  Z2.5 cannot ship a functional intermediate state because
the cycle is co-dependent across the entire substitution algebra.

## What this audit certifies

This file re-runs the Z3 milestone audit gates to confirm the project's
headline theorems remain zero-axiom under the unmodified baseline.
The Z2.5 charter — break the cycle while keeping `Ty.subst` body
unchanged — is structurally infeasible without the larger Z6.B
refactor.

The Z2.5 deliverables in the brief (move instance, refactor compose,
audit gates) are documented here as the recommended FUTURE work scope
under Z6.B's umbrella.  The minimal action this file ships is:
* Re-audit headliners zero-axiom under the existing baseline
* Document the structural finding for future agents
-/

namespace LeanFX2

-- ============================================================
-- Section 1: Re-audit baseline headliners zero-axiom
-- ============================================================
-- These are the same headliners that AuditMegaZ3 covers.  Running them
-- here under the AuditMegaZ25 file confirms that the unmodified
-- baseline (no cycle break) preserves all the Z3 milestone guarantees.

-- Pattern 3 paired-env headline (CUMUL-1.7).
#print axioms LeanFX2.ConvCumulHomo.subst_compatible_paired_allais
#print axioms LeanFX2.ConvCumul.subst_compatible

-- W8 confluence milestones.
#print axioms LeanFX2.RawStep.par.cd_lemma
#print axioms LeanFX2.RawStep.par.diamond
#print axioms LeanFX2.RawStep.parStar.confluence
#print axioms LeanFX2.Conv.canonicalForm

-- Heterogeneous Univalence + funext.
#print axioms LeanFX2.Univalence
#print axioms LeanFX2.UnivalenceHet
#print axioms LeanFX2.funext

-- Z2.B bridge equivalences (the precondition for any Z3 cascade).
#print axioms LeanFX2.Ty.act_eq_rename
#print axioms LeanFX2.Ty.act_eq_subst
#print axioms LeanFX2.Ty.act_eq_weaken

-- Subst.compose remains zero-axiom under the unchanged baseline.
#print axioms LeanFX2.Subst.compose

-- The Action (Subst level) instance remains zero-axiom under the
-- unchanged baseline.  Its synthesis-order constraint vs. Ty.subst
-- is what Z6.B must address.
#print axioms LeanFX2.Subst.compose_eq_action

end LeanFX2
