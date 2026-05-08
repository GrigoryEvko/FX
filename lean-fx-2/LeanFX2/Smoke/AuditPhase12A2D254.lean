import LeanFX2.Reduction.RawPar
import LeanFX2.Reduction.RawParWeakenInv
import LeanFX2.Reduction.RawParInversion
import LeanFX2.Reduction.RawParRename
import LeanFX2.Reduction.RawParCompatible
import LeanFX2.Reduction.ParRed
import LeanFX2.Reduction.Step
import LeanFX2.Reduction.ConvBridge
import LeanFX2.Confluence.RawCd
import LeanFX2.Confluence.RawCdRename
import LeanFX2.Confluence.RawCdDominates
import LeanFX2.Confluence.RawCdLemma
import LeanFX2.Confluence.ChurchRosser
import LeanFX2.Confluence.CanonicalForm
import LeanFX2.Foundation.RawPartialRename
import LeanFX2.Foundation.RawPartialRenameCommute
import LeanFX2.Bridge
import LeanFX2.Cubical.Transport

/-! # AuditPhase12A2D254 — D2.5.4 transp-refl-β cascade zero-axiom audit.

Closes the loop on the Phase G activation work that landed
`Step.transpRefl` (transp at constant path = identity) plus the full
`cd` cascade.  This file is the reviewer-facing sweep: every shipped
declaration must report "does not depend on any axioms".

## What landed

**Phase G.0 (prerequisite, commit a9e44ec)**
* `RawRenaming.weaken_injective`, `RawRenaming.lift_injective` — every
  injective renaming stays injective under `lift`.
* `RawStep.par.rename_inj_inv` — parallel reduction is closed under
  inverse of injective renamings.  ~110 ctor cases.
* `RawStep.par.weaken_inv` — specialization for `weaken`: par steps
  out of `X.weaken` land in `X'.weaken` for some `X'`.

**Phase G activation (commit cd77f91)**
* `RawStep.par.transpReflBeta` — raw β rule for transp at constant
  path: `transp (pathLam typeRaw.weaken) source ⟶ source'`.
* `RawStep.par.transpReflBetaDeep` — raw β rule for path-developed
  constant path: confluence-only mechanism that fires when cd
  develops the path to `pathLam X.weaken` shape.  Documented
  raw-only via `isDocumentedRawOnlyParity` (typed deep β unnecessary
  because the cd cascade closes through the shallow form).
* `Step.transpReflBeta` — typed β ctor (closes #1555).
* `Step.par.transpReflBeta` — typed par mirror.
* `RawTerm.cdTranspCase` — split helper for cd's transp arm.
* `RawTerm.cdTranspCase_rename` — rename-commute lemma for the helper.
* Compat cascade: `transpReflBeta` / `transpReflBetaDeep` arms in
  `RawParRename`, `RawParCompatible`, `RawParInversion`,
  `RawCdRename`, `RawCdDominates`, `RawCdLemma`.
* Bridge: `Step.par.toRawBridge` arm + `ConvBridge.toConvCumul` arm.

## Why this matters

In cubical type theory, `transp (λ i ⇒ A) x ≡ x` (transport along a
constant path is the identity) is the foundational β rule analogous
to `transp refl A x ≡ x` in observational type theory.  Without this
rule, the kernel's cubical fragment had a hole at the most basic
reduction site.

The deep β ctor (`transpReflBetaDeep`) exists purely to close the
cd cascade: when cd develops a path to `pathLam X.weaken` shape, the
β must fire even though the original term wasn't syntactically a
constant path.  This is the standard Tait-Martin-Löf complete-
development trick.

## Confluence preserved

The shipped ctors do NOT regress confluence.  The four headline
theorems remain zero-axiom after Phase G:
* `RawStep.par.cd_lemma`
* `RawStep.par.diamond`
* `RawStep.parStar.confluence`
* `Conv.canonicalRaw` / `Conv.transRaw`

## Audit

Every declaration below must report "does not depend on any axioms".
-/

-- Phase G.0 prerequisites: injectivity + inverse-rename inversion
#print axioms LeanFX2.RawRenaming.weaken_injective
#print axioms LeanFX2.RawRenaming.lift_injective
#print axioms LeanFX2.RawStep.par.rename_inj_inv
#print axioms LeanFX2.RawStep.par.weaken_inv

-- Phase G activation: cd helper + inversion + compat + cd cascade
#print axioms LeanFX2.RawTerm.cdTranspCase
#print axioms LeanFX2.RawTerm.cdTranspCase_rename
#print axioms LeanFX2.RawTerm.unweaken?_weaken
#print axioms LeanFX2.RawTerm.unweaken?_imp_weaken
#print axioms LeanFX2.RawTerm.cd_weaken
#print axioms LeanFX2.RawStep.par.transp_inv
#print axioms LeanFX2.RawStep.par.pathLam_inv

-- Headline confluence theorems remain zero-axiom after Phase G
#print axioms LeanFX2.RawStep.par.cd_lemma
#print axioms LeanFX2.RawStep.par.diamond
#print axioms LeanFX2.RawStep.parStar.confluence
#print axioms LeanFX2.Conv.canonicalRaw
#print axioms LeanFX2.Conv.transRaw

-- Phase G consumer: named-redex β at Step.par level (Cubical/Transport)
#print axioms LeanFX2.Cubical.constantTypeTransport_betaParStep
#print axioms LeanFX2.Cubical.constantTypeTransport_betaConvCumul
