import LeanFX2.Reduction.RawParCompatible
import LeanFX2.Reduction.RawParWeakenInv
import LeanFX2.Confluence.RawCd
import LeanFX2.Confluence.RawCdRename
import LeanFX2.Confluence.RawCdLemma
import LeanFX2.Confluence.RawCdDominates

/-! # Smoke/AuditD36S1UaBeta — D3.6-S1 univalence-β cascade audit.

The headline atomic shipment for the kernel-internal univalence-β
reduction rule.  Phase D3.6-S1 ships the actual β-rule cascade
mounted on the vocabulary that P1-P6 set up.

## What S1 ships (the headline of the entire P-series)

`RawStep.par.uaBeta` — the shallow univalence-β raw rule:
```
transp (uaToEquiv proof) source ⟶ equivApply (uaToEquiv proof) source
```
fires when the path argument of `transp` is a `uaToEquiv` head.

`RawStep.par.uaBetaDeep` — the deep variant: when the path develops
to `uaToEquiv proofRawTarget` via parallel reduction, the entire
`transp` reduces to the univalence-β contractum.  Required for
`cd_dominates`'s `cdTranspCase` activation.

## Why no typed mirror

At the typed level, `Term.transp` requires its path argument to be
a `Term context (Ty.path ...) pathRaw`, but `Term.uaToEquiv`
produces type `Ty.equiv leftTy rightTy` (NOT `Ty.path`).  Therefore
no typed `Term.transp` can have a path-raw of `RawTerm.uaToEquiv
proofRaw`, making this β rule structurally a raw-only confluence-
closure mechanism — listed in `isDocumentedRawOnlyParity` alongside
`transpReflBetaDeep`.

## Cascade footprint

* **`Reduction/RawPar.lean`** — two new ctors `uaBeta` + `uaBetaDeep`.
* **`Reduction/RawParRename.lean`** — rename arms threading the
  raw-cong rules through both ctors.
* **`Reduction/RawParCompatible.lean`** — subst arms threading the
  raw-cong rules through both ctors.
* **`Reduction/RawParInversion.lean`** — `transp_inv` extended from
  3-way disjunction to 5-way disjunction (cong / shallow constant-β /
  deep constant-β / shallow ua-β / deep ua-β); new `uaToEquiv_inv`
  inversion lemma backing the cd cascade's deep arm.
* **`Reduction/RawParWeakenInv.lean`** — new `rename_eq_uaToEquiv_imp`
  shape-inversion helper; `transp` arm of `rename_inj_inv` extended
  with two new arms (shallow + deep) discharging the new disjunction
  cases.
* **`Confluence/RawCd.lean`** — `cdTranspCase`'s `uaToEquiv` arm
  rewritten from "rebuild as plain `transp` cong" to "fire β as
  `equivApply (uaToEquiv proof) developedSource`".  cd cascade is
  now activated for univalence-β.
* **`Confluence/RawCdRename.lean`** — `cdTranspCase_rename` lemma
  inherits the new arm via `all_goals rfl`'s structural commute.
* **`Confluence/RawCdLemma.lean`** — three cascading arms: the
  existing `transpCong` arm extended with a uaToEquiv-firing
  branch via the `first` tactic; new `uaBeta` shallow arm closing
  via `equivApplyCong + uaToEquivCong` on the IHs; new `uaBetaDeep`
  deep arm closing via `uaToEquiv_inv` on `pathIH` to recover the
  inner step.
* **`Confluence/RawCdDominates.lean`** — `transp` arm extended with
  the uaToEquiv firing branch via `first` tactic, dispatching to
  `uaBetaDeep` when `cd pathTerm = uaToEquiv proofRaw`.
* **`Tools/StrictHarness/Common.lean`** — `isDocumentedRawOnlyParity`
  extended with `uaBeta` + `uaBetaDeep` documentation entries.

## Zero-axiom verification

Every shipped lemma has its axiom dependency printed below.  Every
declaration must report "does not depend on any axioms" — anything
else would be a regression. -/

namespace LeanFX2

-- ============================
-- Section A: New raw ctors
-- ============================

#print axioms RawStep.par.uaBeta
#print axioms RawStep.par.uaBetaDeep

-- ============================
-- Section B: Inversion lemmas (new)
-- ============================

#print axioms RawStep.par.uaToEquiv_inv
#print axioms RawStep.par.transp_inv

-- ============================
-- Section C: Cascade theorems
-- ============================

-- The full par-step compatibility theorems still pass (they cover all
-- ctors, including the new ones via the threading arms above).
#print axioms RawStep.par.rename
#print axioms RawStep.par.subst_par
#print axioms RawStep.par.subst0_par
#print axioms RawStep.par.rename_compatible
#print axioms RawStep.par.subst_compatible
#print axioms RawStep.par.rename_inj_inv
#print axioms RawStep.par.weaken_inv

-- ============================
-- Section D: Cd helpers
-- ============================

#print axioms RawTerm.cdTranspCase
#print axioms RawTerm.cdTranspCase_rename

-- ============================
-- Section E: Confluence dispatches (cd development uses uaBetaDeep)
-- ============================

#print axioms RawStep.par.cd_dominates
#print axioms RawStep.par.cd_lemma

end LeanFX2
