import LeanFX2.Foundation.Ty
import LeanFX2.Foundation.RawTerm
import LeanFX2.Foundation.SubstActsOnTy
import LeanFX2.Foundation.TyAct
import LeanFX2.HoTT.Univalence
import LeanFX2.HoTT.Funext
import LeanFX2.Confluence.RawCdLemma
import LeanFX2.Confluence.RawDiamond
import LeanFX2.Confluence.CanonicalForm
import LeanFX2.Reduction.CumulSubstCompat
import LeanFX2.Smoke.AuditMegaZ2B

/-! # AuditMegaZ2A1 — Zero-axiom audit for the `actOnRawTerm` ↔
`RawTerm.act` alignment fix.

## What Z2.A.1 ships

The `ActsOnRawTerm` typeclass (Z2.A) and `RawTerm.act` engine (Z4.A)
were originally shipped as INDEPENDENT abstractions:
* `ActsOnRawTerm`'s instance bodies for `RawRenaming` and
  `Subst level` delegated to the LEGACY `RawTerm.rename` /
  `RawTerm.subst` operations.
* `RawTerm.act` was a parallel structural recursion that took a
  unified Container, but no instance body routed through it.

Z2.A.1 ALIGNS the two layers: the instance bodies now delegate to
`RawTerm.act`.  This makes `actOnRawTerm action raw = RawTerm.act
raw action` hold by `rfl` for both Container instances, which is
the structural prerequisite for `Term.act` (Z5.A) to dispatch
through a single typeclass-driven recursion that delegates raw
arms to `RawTerm.act`.

## Files modified by Z2.A.1

* `Foundation/Ty.lean` — `instance : ActsOnRawTerm RawRenaming`
  body changed from `RawTerm.rename` delegation to `RawTerm.act`.
* `Foundation/SubstActsOnTy.lean` — three changes:
  - NEW `instance ActsOnRawTermVarOfSubst : ActsOnRawTermVar (Subst
    level)` (the load-bearing addition that lets `RawTerm.act`
    elaborate over a `Subst level` Container).
  - `ActsOnRawTermOfSubst.actOnRawTerm` body changed from
    `RawTerm.subst sigma.forRaw` delegation to `RawTerm.act`.
  - NEW bridge theorems `RawTerm.act_eq_rename` and
    `RawTerm.act_eq_subst_forRaw` (zero-axiom 56-case structural
    inductions) used by `Smoke/AuditMegaZ2B.lean`'s `Ty.act_eq_*`
    proofs at the raw-payload arms.

* `Smoke/AuditMegaZ2B.lean` — adjusted the raw-payload arms of
  `Ty.act_eq_rename` and `Ty.act_eq_subst` to invoke the new bridge
  theorems instead of relying on the OLD instance body's `rfl`
  shortcut.  Each arm now rewrites
  `RawTerm.act endpoint action = endpoint.rename action` (or
  `endpoint.subst action.forRaw`) explicitly.

## Audit philosophy

Z2.A.1 is a CORRECTNESS-PRESERVING refactor: the propositional
content of every shipped theorem is unchanged; only the
DEFINITIONAL chain that `rfl`-establishes `actOnRawTerm action raw =
RawTerm.act raw action` has been straightened.  This file gates:

1. The two new alignment equations (`rfl`).
2. Audit gates for the modified instances + new instance.
3. Audit gates for the bridge theorems.
4. Headliner regression: `subst_compatible_paired_allais` (Pattern
   3), the W8 confluence chain (cd_lemma / diamond / parStar
   confluence / canonical_form), Univalence + UnivalenceHet, and
   `funext` — all must remain zero-axiom.
-/

namespace LeanFX2

-- ============================================================
-- Section 1: The load-bearing alignment equations (must hold by rfl)
-- ============================================================
-- These two equations are the entire point of Z2.A.1.  Each must
-- elaborate as `rfl`; if either fails, the alignment is incomplete.

/-- `rfl` smoke: `actOnRawTerm` over `RawRenaming` reduces to
`RawTerm.act` invocation.  Holds by the modified instance body in
`Foundation/Ty.lean`. -/
example {sourceScope targetScope : Nat}
    (someRenaming : RawRenaming sourceScope targetScope)
    (rawTerm : RawTerm sourceScope) :
    ActsOnRawTerm.actOnRawTerm someRenaming rawTerm =
      RawTerm.act rawTerm someRenaming := rfl

/-- `rfl` smoke: `actOnRawTerm` over `Subst level` reduces to
`RawTerm.act` invocation.  Holds by the modified instance body in
`Foundation/SubstActsOnTy.lean`. -/
example {level sourceScope targetScope : Nat}
    (someSubst : Subst level sourceScope targetScope)
    (rawTerm : RawTerm sourceScope) :
    ActsOnRawTerm.actOnRawTerm someSubst rawTerm =
      RawTerm.act rawTerm someSubst := rfl

end LeanFX2

-- ============================================================
-- Section 2: Audit gates for the modified instances + new instance
-- ============================================================
-- The modified `ActsOnRawTerm` instance for `RawRenaming` (delegates
-- to `RawTerm.act`).
#print axioms LeanFX2.instActsOnRawTermRawRenaming

-- The modified `ActsOnRawTerm` instance for `Subst level` (delegates
-- to `RawTerm.act`).
#print axioms LeanFX2.ActsOnRawTermOfSubst

-- The NEW `ActsOnRawTermVar` instance for `Subst level` (returns
-- `sigma.forRaw position`).  Without this, `RawTerm.act raw sigma`
-- would fail to elaborate.
#print axioms LeanFX2.ActsOnRawTermVarOfSubst

-- ============================================================
-- Section 3: Audit gates for the new bridge theorems
-- ============================================================
-- Bridge: `RawTerm.act` over a renaming agrees with `RawTerm.rename`
-- pointwise.  Used by `Ty.act_eq_rename`'s raw-payload arms.
#print axioms LeanFX2.RawTerm.act_eq_rename

-- Bridge: `RawTerm.act` over a `Subst level` agrees with
-- `RawTerm.subst sigma.forRaw`.  Used by `Ty.act_eq_subst`'s raw-
-- payload arms.
#print axioms LeanFX2.RawTerm.act_eq_subst_forRaw

-- ============================================================
-- Section 4: Z2.B downstream — bridge theorems still zero-axiom
-- ============================================================
-- These are the headline Z2.B deliverables; verify Z2.A.1's
-- alignment did not regress them.

#print axioms LeanFX2.Ty.act_eq_rename
#print axioms LeanFX2.Ty.act_eq_subst
#print axioms LeanFX2.Ty.act_eq_weaken

-- ============================================================
-- Section 5: Z2.6 downstream — Ty.act-layer infrastructure
-- ============================================================
-- These theorems live in `Foundation/TyAct.lean` and abstract over
-- `actOnRawTerm` via the `rawAgree` / `rawCompat` / `rawIdentity`
-- predicate fields.  Z2.A.1's alignment leaves the typeclass
-- dispatch surface intact, so these still ship clean.

#print axioms LeanFX2.Ty.act_pointwise
#print axioms LeanFX2.Ty.act_compose
#print axioms LeanFX2.Ty.act_identity

-- ============================================================
-- Section 6: Headliner regression — Pattern 3 + W8 confluence
-- ============================================================
-- Z2.A.1 must not regress the project's load-bearing zero-axiom
-- theorems.  This section runs `#print axioms` on every headliner
-- and confirms each remains clean.

-- Pattern 3 (CUMUL-1.7) — Allais ICFP'18 paired-env subst_compatible.
#print axioms LeanFX2.ConvCumulHomo.subst_compatible_paired_allais

-- W8 — typed Tait-Martin-Löf chain (cd_lemma / diamond / parStar /
-- canonical form).  Each of these is roughly 50-cases of structural
-- induction over Step.par; any regression in raw-payload reductions
-- would break them at compile time.
#print axioms LeanFX2.RawStep.par.cd_lemma
#print axioms LeanFX2.RawStep.par.diamond
#print axioms LeanFX2.RawStep.parStar.confluence
#print axioms LeanFX2.Conv.canonicalForm

-- Heterogeneous Univalence (Phase 12.A.3 D3.6) — `Step.eqType` →
-- `Univalence` as zero-axiom theorem (no `axiom` keyword).
#print axioms LeanFX2.Univalence
#print axioms LeanFX2.UnivalenceHet

-- funext (Phase 12.A.3 D3.7) — `Step.eqArrow` → `funext` as
-- zero-axiom theorem.
#print axioms LeanFX2.funext
