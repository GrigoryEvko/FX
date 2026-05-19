import LeanFX2.HoTT.TranspCompose
import LeanFX2.HoTT.Path.Composition
import LeanFX2.HoTT.Transport
import LeanFX2.Reduction.Step
import LeanFX2.Reduction.RawParInversion
import LeanFX2.Reduction.RawParCompatible
import LeanFX2.Confluence.RawCd
import LeanFX2.Confluence.RawCdLemma
import LeanFX2.Confluence.RawCdDominates
import LeanFX2.Confluence.RawDiamond

/-! # Smoke/AuditD36S3TranspCompose — D3.6-S3 transp distributes over compose.

Reviewer-facing audit log for Phase D3.6-S3 (#1684): the headline
kernel-internal cubical-β rule

```
transp (pathCompose left right) source  ⟶  transp right (transp left source)
```

ships at zero axioms across THREE layers in a full massive cascade
spanning ~30 files / ~600 lines.

## What ships in v1.0 (D3.6-S3)

### Layer 1 — Kernel constructor extension

* `RawTerm.pathCompose left right` — new binary raw ctor.  All ~20
  kernel files that pattern-match on `RawTerm` extended with
  `pathCompose` arms (Foundation: RawSubst rename / subst / pointwise /
  compose / cross-direction / weakening, RawPartialRename, RawCdRename;
  Algo: RawWHNF headCtor + 7 ?-projection helpers + whnf reach,
  RawWHNFCorrect inversions + headCtor lifts, Eval, Infer, Check;
  RenameIdentity; SubstActsOnTy).
* `RawStep.par.pathComposeCong` — cong rule for parallel reduction
  through the binary pathCompose ctor.
* `RawStep.par.transpCompose` — the headline shallow β rule.
* `RawStep.par.transpComposeDeep` — confluence-closure deep variant
  (path develops to pathCompose via parallel reduction).
* `RawStep.par.pathCompose_inv` — inversion lemma backing the cd
  cascade's deep arm (par from `pathCompose left right` lands at
  another pathCompose).
* `RawTerm.rename_eq_pathCompose_imp` — shape-inversion helper
  (66 nomatch arms + 1 succ arm) for `rename_inj_inv`.

### Layer 2 — Confluence cd cascade

* `RawTerm.cdTranspCase` extended with `pathCompose left right =>
  transp right (transp left developedSource)` arm — fires the β when
  the developed path is syntactically a `pathCompose`.
* `RawTerm.cd` extended with `pathCompose` recursive arm.
* `RawCdLemma`'s `cdTranspCase` first-block extended with the
  pathCompose-specific tactic (rename_i + transpComposeDeep) covering
  the new arm.  Two new explicit cases (`transpCompose` / `transpComposeDeep`)
  in the cd_lemma inductive enumeration.
* `RawCdDominates`'s `transp` arm extended with the pathCompose-specific
  `transpComposeDeep` discharge in the `first` block.  New
  `pathCompose` arm in cd_dominates inductive enumeration.

### Layer 3 — Audit infrastructure

* `assert_term_raw_ctor_delta` budget gate updated from 8 to 7
  (RawTerm grew by 1; Term unchanged).
* `assert_dependent_pair_dependent_budget` adjusted to accommodate
  new cascade dependents.
* `isDocumentedRawOnlyParity` whitelist extended Section E with
  three new entries: `pathComposeCong` / `transpCompose` /
  `transpComposeDeep`.
* `Tools/AuditAll/AuditReduction.lean` adds 4 strict gates for the
  new shipped declarations.
* `HoTT/TranspCompose.lean` ships the meta-level `Path.compose` rename
  + headline `Path.transport_compose` rule, plus typed-Conv specializations
  `Conv.transpComposeConstantLeft` and `Conv.transpComposeBothConstant`
  for the constant-pathLam case (the only typed-level case expressible
  without typed `Term.pathCompose` ctor).

## Why a raw-only typed mirror

At the typed level, `Term.transp` requires its path argument to be
`Term context (Ty.path ...) pathRaw`.  But typed `Term.pathCompose`
(which would produce `Term context (Ty.path carrier left right) ...`
from two paths whose endpoints align) is the v1.1 D3.10 follow-up —
not yet shipped.  Therefore until D3.10 lands, no typed `Term.transp`
can have a path-raw of `RawTerm.pathCompose left right`, making the
β rule structurally a raw-only confluence-closure mechanism.

When D3.10 v1.1 ships typed `Term.pathCompose`, the typed mirrors
`Step.pathComposeCong` / `Step.transpCompose` /
`Step.par.transpCompose` will land alongside, and the three current
raw-only entries will move out of the `isDocumentedRawOnlyParity`
whitelist into the canonical typed cascade.

## Verification

* `lake build LeanFX2` — kernel green (~267 jobs).
* `lake build LeanFX2 LeanFX2Audit` — full audit green; every gate
  below reports "does not depend on any axioms".

Closes D3.6-S3 (#1684) under FULL CASCADE outcome (Outcome C). -/

namespace LeanFX2

-- ============================
-- Section A: Meta-level Path.compose + headline rule
-- ============================

#print axioms LeanFX2.Path.compose
#print axioms LeanFX2.Path.transport_compose

-- ============================
-- Section B: Typed-Conv constant-left case
-- ============================

#print axioms LeanFX2.Conv.transpComposeConstantLeft
#print axioms LeanFX2.Conv.transpComposeBothConstant

-- ============================
-- Section C: Raw cubical-β cascade — the actual headline rule
-- ============================

#print axioms LeanFX2.RawStep.par.pathComposeCong
#print axioms LeanFX2.RawStep.par.transpCompose
#print axioms LeanFX2.RawStep.par.transpComposeDeep
#print axioms LeanFX2.RawStep.par.pathCompose_inv

-- ============================
-- Section D: Surrounding cascade infrastructure remains zero-axiom
-- ============================

#print axioms LeanFX2.RawStep.par.cd_lemma
#print axioms LeanFX2.RawStep.par.diamond
#print axioms LeanFX2.RawStep.par.transp_inv
#print axioms LeanFX2.RawStep.par.cd_dominates

-- ============================
-- Section E: Surrounding D3.6 cascade remains zero-axiom
-- (proves S3 extension does not regress S1/S2)
-- ============================

#print axioms LeanFX2.RawStep.par.uaBeta
#print axioms LeanFX2.RawStep.par.uaBetaDeep
#print axioms LeanFX2.RawStep.par.uaToEquiv_inv
#print axioms LeanFX2.RawStep.par.transpReflBeta
#print axioms LeanFX2.RawStep.par.transpReflBetaDeep
#print axioms LeanFX2.Step.transpReflBeta

end LeanFX2
