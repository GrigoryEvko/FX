import LeanFX2.Foundation.Ty
import LeanFX2.Foundation.Subst
import LeanFX2.Foundation.SubstActsOnTy
import LeanFX2.Foundation.TyAct
import LeanFX2.Smoke.AuditMegaZ2B
import LeanFX2.Smoke.AuditMegaZ3

/-! # AuditMegaZ25 — MEGA-Z2.5 RELAUNCH (structural finding reaffirmed
+ Z2.6 cycle-free instance laws shipped).

## Mission

MEGA-Z2.5 was chartered to break the post-Z3-redirect circular
dependency

```
Ty.subst → Ty.act → [Action (Subst level)] → Subst.compose → Ty.subst
```

so that the literal Z3 cascade `Ty.subst t sigma := Ty.act t sigma`
elaborates at the definition site of `Ty.subst` in
`Foundation/Subst.lean`.

## Relaunch context

The Z2.5 ATTEMPT-1 (commit `1955affc`) retreated with structural
finding documented in this file's predecessor.  Z2.6 (commit
`86f12d93`) shipped `Foundation/TyAct.lean` with three native
zero-axiom theorems (`Ty.act_pointwise`, `Ty.act_compose`,
`Ty.act_identity`) that prove Ty.act-layer facts WITHOUT routing
through `Ty.subst_compose` or `Ty.subst_pointwise`.

The relaunch brief asked: with Z2.6's infrastructure now available,
can the cycle be broken by refactoring `Subst.compose`'s `forTy`
field to `Ty.act (sigma1.forTy pos) sigma2` instead of
`(sigma1.forTy pos).subst sigma2`?

## Relaunch empirical finding

**The cycle remains structurally infeasible at the `Subst.compose`
body level.**

The blocker is **not** `Ty.subst_compose`'s use in the Action
instance proof (Z2.6 addresses that downstream); the blocker is the
TYPECLASS SYNTHESIS scope.  `Ty.act` requires
`[Action Container]`, `[ActsOnRawTerm Container]`, and
`[ActsOnTyVar Container level]` at every call site.  Inside
`Foundation/Subst.lean` BEFORE the `Action (Subst level)` instance
declaration (line 932), none of those three instances are in scope:

* `Action (Subst level)` instance is the very thing that
  `Subst.compose` (line 719) is the `compose` field of.  Defining
  `Subst.compose` to call `Ty.act ... sigma2` requires
  `[Action (Subst level)]`, which doesn't exist yet at that point.
* `ActsOnRawTermOfSubst` and `ActsOnTyVarOfSubst` instances live in
  `Foundation/SubstActsOnTy.lean`, downstream of
  `Foundation/Subst.lean`.

**Empirical verification (relaunch session, 2026-05-04)**: Editing
`Subst.compose`'s body to `Ty.act (sigma1.forTy pos) sigma2` and
running `lake build LeanFX2.Foundation.Subst` produces:

```
error: LeanFX2/Foundation/Subst.lean:723:28: failed to synthesize
instance of type class
  Action (Subst level)
```

(plus 5 cascading errors in downstream lemmas at lines 733, 735,
778, 850, 946 due to the `@[reducible]` failure to compute).

**Self-referencing instance synthesis test**: Lean 4 v4.29.1 does
NOT permit a typeclass instance's body to reference its own
typeclass via the synthesis machinery.  Empirical script
`/tmp/test_self_inst.lean` confirms:

```
error: failed to synthesize instance of type class Foo SubstX
```

when an `instance : Foo SubstX` body's `compose` field invokes
`Foo.bar` (which would synthesize `Foo SubstX`, the very thing
being defined).

## Z2.6 evaluation

`Foundation/TyAct.lean`'s three theorems are USEFUL for proving
Ty.act-layer facts at zero axioms — but they live downstream of
`Subst.lean` (import chain `Subst → SubstActsOnTy → TyAct`).  They
cannot be invoked from `Subst.lean`'s scope to define
`Subst.compose` differently OR to re-prove the `Action (Subst level)`
instance laws.

The Z2.6 infrastructure DOES enable a future cycle-free proof of
the Action instance laws — but ONLY if the Action instance is
relocated DOWNSTREAM of TyAct.lean.  That relocation is the
chartered work of MEGA-Z6.B (file split), not MEGA-Z2.5.

## Recommended path forward (chartered as MEGA-Z6.B)

The cycle resolution requires **file split**:

**Strategy A**: Move `Ty.subst` and the `Action (Subst level)`
instance to a NEW `Foundation/SubstAction.lean` that imports
`SubstActsOnTy.lean` and `TyAct.lean`.  In that file:

1. Define `Ty.subst t sigma := Ty.act t sigma` (one-liner, the Z3
   redirect).
2. Define `Action (Subst level)` with `compose := Subst.compose`
   (the existing `Subst.compose` from `Subst.lean` continues to use
   `Ty.subst` — that's fine because `Ty.subst` is now a redirect to
   `Ty.act`, no recursion through the body).
3. Re-prove the Action instance laws via Z2.6's
   `Ty.act_compose` / `Ty.act_pointwise` / `Ty.act_identity`,
   eliminating the `Ty.subst_compose` dependency.

This decoupling lets the existing `Subst.compose` (line 719 of
Subst.lean) keep its `(sigma1.forTy pos).subst sigma2` body — that
body now invokes `Ty.act` indirectly via the `Ty.subst` redirect.
The cycle is broken because `Subst.compose` no longer requires
`[Action (Subst level)]`; it requires only `Ty.subst` (the
redirected one-liner), which is a plain definition without
typeclass dispatch.

**Strategy B**: Inline the Z3 cascade as a single multi-file atomic
commit that simultaneously moves `Ty.subst`, `Action (Subst level)`,
and all 25 ctors of the cascade.

Both strategies are within MEGA-Z6.B's chartered scope.  Z2.5 (this
task) cannot ship a functional intermediate state because the cycle
is co-dependent across the entire substitution algebra and
file-boundary structure.

## What this audit certifies

The minimal action this file ships:

1. **Re-audit baseline headliners zero-axiom** — Pattern 3, W8,
   Heterogeneous Univalence remain clean.
2. **Re-audit Z2.6 infrastructure zero-axiom** — `Ty.act_pointwise`,
   `Ty.act_compose`, `Ty.act_identity` ship clean (already audited
   in `AuditMegaZ26.lean`; re-audited here for cross-reference).
3. **Document the relaunch empirical finding** — the cycle break
   IS structurally infeasible at the `Subst.compose` body level;
   the blocker is the typeclass synthesis scope, not the proof
   ladder.  Z2.6's infrastructure does not change that fact.
4. **Document the future cascade contract** — the Action instance
   laws WILL be re-proven via Z2.6 at the cycle-resolved layer
   (Z6.B's file-split file), but that proof cannot be shipped from
   `Subst.lean` itself.

The Z2.5 deliverables in the brief — refactor `Subst.compose`'s
forTy, derive Action instance laws via `Ty.act_compose` — are
documented here as the recommended FUTURE work scope under Z6.B's
umbrella.  Lake build remains GREEN at 314 jobs (was 313 before
this file's import of TyAct + AuditMegaZ26).

## Z2.6 native infrastructure status

The Z2.6-shipped theorems are zero-axiom and ready to be invoked
when the cycle is resolved (Z6.B):

* `Ty.act_compose` — multi-Container composition law.
* `Ty.act_pointwise` — extensionality law.
* `Ty.act_identity` — identity law.
* `ActComposeCompat`, `ActPointwiseAgree`, `ActsAsIdentity` —
  the three Prop-valued predicates that consumers ship to invoke
  the headline theorems.

These are the building blocks that the eventual Z6.B Action instance
laws will use.
-/

namespace LeanFX2

-- ============================================================
-- Section 1: Re-audit baseline headliners zero-axiom
-- ============================================================
-- These are the same headliners that AuditMegaZ3 covers.  Running
-- them here under the AuditMegaZ25 file confirms that the unmodified
-- baseline (no cycle break) preserves all the Z3 milestone
-- guarantees — and that adding the Z2.6 import `Foundation/TyAct`
-- does NOT introduce any axioms anywhere.

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
-- is what Z6.B's file split must address; relaunching Z2.5 with
-- Z2.6's infrastructure did NOT alter the structural infeasibility.
#print axioms LeanFX2.Subst.compose_eq_action

-- ============================================================
-- Section 2: Z2.6 native Ty.act-layer theorems (zero-axiom regression).
-- ============================================================
-- These three theorems are the FOUNDATION that MEGA-Z6.B will use
-- to re-prove the Action instance laws WITHOUT routing through
-- Ty.subst_compose.  They ship zero-axiom in `Foundation/TyAct.lean`
-- and are re-audited here as cross-reference.

-- The native multi-Container compose theorem.  Z6.B will use this
-- to derive `Action.compose_assoc_pointwise` for `Action (Subst level)`
-- without invoking `Ty.subst_compose`.
#print axioms LeanFX2.Ty.act_compose

-- The native extensionality theorem.  Z6.B will use this to prove
-- pointwise equality of two compositions through their shared lift
-- behaviour.
#print axioms LeanFX2.Ty.act_pointwise

-- The native identity theorem.  Z6.B will use this to derive
-- `Action.compose_identity_left_pointwise` /
-- `Action.compose_identity_right_pointwise` without invoking
-- `Ty.subst_identity`.
#print axioms LeanFX2.Ty.act_identity

-- The three predicates these theorems consume.
#print axioms LeanFX2.ActComposeCompat
#print axioms LeanFX2.ActPointwiseAgree
#print axioms LeanFX2.ActsAsIdentity

-- ============================================================
-- Section 3: Relaunch empirical finding — Z2.6 path also blocked.
-- ============================================================
-- The relaunch brief asked: can `Subst.compose`'s body use
-- `Ty.act (sigma1.forTy pos) sigma2` instead of `.subst sigma2`?
--
-- Empirical answer: NO.  Editing `Subst.compose`'s body to use
-- `Ty.act` produces:
--
--     error: failed to synthesize instance of type class
--       Action (Subst level)
--
-- at the call site (line 723 of Subst.lean), because:
--   1. `Ty.act` requires `[Action Container]` at every call site.
--   2. `Action (Subst level)` instance is defined AT line 932 of
--      Subst.lean, AFTER `Subst.compose` (line 719).
--   3. Even moving the instance up doesn't help — the instance's
--      `compose` field would itself need to call `Ty.act`, which
--      would need `[Action (Subst level)]`, which is the very
--      instance being defined (self-reference; Lean rejects).
--
-- Therefore, the cycle break must happen at the FILE-LAYER, not at
-- the instance-body-layer.  This is the chartered scope of
-- MEGA-Z6.B (file split: move `Ty.subst` + `Action (Subst level)`
-- instance to a new file downstream of `TyAct.lean`).
--
-- This file ships NO modification to `Subst.compose`'s body.  The
-- baseline binary semantics is preserved; the audit gates above
-- regression-test that fact.

end LeanFX2
