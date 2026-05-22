import LeanFX2.Reduction.RawParWeakenInv
import LeanFX2.Reduction.Step.Inductive
import LeanFX2.Reduction.ParRed
import LeanFX2.Reduction.ConvBridge
import LeanFX2.Reduction.Cumul.Relation.Inductive
import LeanFX2.Bridge
import LeanFX2.Confluence.RawCd
import LeanFX2.Confluence.RawCdRename
import LeanFX2.Confluence.RawCdDominates
import LeanFX2.Confluence.RawCdLemma
import LeanFX2.Confluence.ChurchRosser
import LeanFX2.Confluence.CanonicalForm
import LeanFX2.Foundation.RawPartialRename
import LeanFX2.Foundation.RawPartialRenameCommute
import LeanFX2.Foundation.Polygraph.StepLabel
import LeanFX2.Foundation.Polygraph.Dim1Extraction

/-! # AuditD252HcompBeta — D2.5.2 hcomp-β cascade zero-axiom audit
(Phases A + B).

Closes the cubical hcomp-β cascade for constant-path sides across
both the raw layer (Phase A) and the typed layer (Phase B).

## What landed in Phase A (raw layer)

**Raw ctors (Reduction/RawPar.lean)**
* `RawStep.par.hcompBeta` — shallow constant-path-sides β rule.
  `hcomp (pathLam X.weaken) cap ⟶ cap'` where the pathLam body
  inner-steps from `X` and the cap steps to `cap'`.
* `RawStep.par.hcompBetaDeep` — deep variant for sides developing to
  `pathLam X.weaken` under parallel reduction.  Required for cd
  cascade closure when the source sides was not literally a
  constant pathLam.

**Cd dispatch (Confluence/RawCd/CubicalAndEquiv.lean)**
* `RawTerm.cdHcompCase` — 67-arm dispatcher.  When developed sides
  is `pathLam X.weaken`, returns developedCap (β fires); otherwise
  rebuilds as plain `hcomp` cong.  Structurally mirrors
  `cdTranspCase`.

**Cd cascade**
* `RawTerm.cdHcompCase_rename` — rename-commute lemma for the helper.
* Raw cascade arms in `RawParRename`, `RawParCompatible`,
  `RawParInversion`, `RawCdRename`, `RawCdDominates`, `RawCdLemma`.

**Inversion**
* `RawStep.par.hcomp_inv` — extended from 2-arm (refl + hcompCong) to
  4-arm (+ hcompBeta + hcompBetaDeep) disjunction.

## What landed in Phase B (typed layer)

**Typed ctors**
* `Step.hcompBeta` (Reduction/Step.lean) — typed β rule firing on
  `Term.hcompPath` (the path-shaped hcomp ctor).  Source's sides
  path is fixed at `RawTerm.pathLam capRaw.weaken` and both
  endpoints are pinned to `capRaw`; the target is `capValue`.
* `Step.par.hcompBeta` (Reduction/ParRed/ParInductive.lean) —
  par-level mirror carrying an inner cap-development premise.
* `ConvCumul.betaHcompPathCumul` (Reduction/Cumul/Relation.lean) —
  conversion-layer mirror used by the bridge.

**Bridge arms**
* `Step.par.ofStep` arm in `ParStepLift.lean` lifting
  `Step.hcompBeta` to `Step.par.hcompBeta` with a `Step.par.refl`
  inner cap step.
* `ConvCumul.ofStep` arm in `ConvBridge.lean` lifting
  `Step.par.hcompBeta` to `ConvCumul.betaHcompPathCumul`.
* `Step.par.toRawBridge` arm in `Bridge.lean` projecting
  `Step.par.hcompBeta` to `RawStep.par.hcompBeta` with refl on the
  sides path (path body is constant `capRawSource`).

## Why this matters

Cubical hcomp with constant-path sides is the cubical analog of
"transp at constant path is identity" (D2.5.4 transpReflBeta).
Without this β rule, the kernel's cubical fragment had a hole at the
hcomp-trivial-filler site.  The semantic justification: in CCHM
cubical, `hcomp [φ → λi. anything] cap` reduces to the cap when the
sides are constant in the cube direction (the filler is the cap
itself).

The deep ctor (`hcompBetaDeep`) now ships a typed mirror as well —
`Step.par.hcompBetaDeep` (Reduction/ParRed/ParInductive.lean) added
in commit fec5de89 (unblock-E.hcompPath.RelaxedBeta, #2068).  Carries
the raw path-reduction premise `RawStep.par sidesPathRawSource
(RawTerm.pathLam capRawSource.weaken)` plus the typed cap step;
mirrors the `transpReflBetaDeep` precedent (#2063) at the hcomp
head.  Restricted to homogeneous endpoints
(`Ty.path carrierType capRawSource capRawSource`) because
`Term.hcompPath` is fixed at homogeneous endpoints; heterogeneous-
endpoint Deep variants remain ROADMAP debt under
unblock-E leaf-coverage.  Parity exception in
`isDocumentedRawOnlyParity` Section I was removed.

## Confluence preserved

The shipped ctors do NOT regress confluence.  The four headline
theorems remain zero-axiom after Phases A + B:
* `RawStep.par.cd_lemma`
* `RawStep.par.diamond`
* `RawStep.parStar.confluence`
* `Conv.canonicalRaw` / `Conv.transRaw`

## Audit

Every declaration below must report "does not depend on any axioms".
-/

-- Raw ctors (Phase A)
#print axioms LeanFX2.RawStep.par.hcompBeta
#print axioms LeanFX2.RawStep.par.hcompBetaDeep

-- Cd dispatch + rename
#print axioms LeanFX2.RawTerm.cdHcompCase
#print axioms LeanFX2.RawTerm.cdHcompCase_rename

-- Inversion
#print axioms LeanFX2.RawStep.par.hcomp_inv

-- Typed ctors + bridge mirrors (Phase B)
#print axioms LeanFX2.Step.hcompBeta
#print axioms LeanFX2.Step.par.hcompBeta
#print axioms LeanFX2.Step.par.hcompBetaDeep
#print axioms LeanFX2.ConvCumul.betaHcompPathCumul

-- Polygraph cascade for hcompBetaDeep (ordinal 112)
#print axioms LeanFX2.Foundation.Polygraph.StepLabel.index
#print axioms LeanFX2.Foundation.Polygraph.StepLabel.fromIndex?

-- Headline confluence theorems remain zero-axiom after Phases A + B
#print axioms LeanFX2.RawStep.par.cd_lemma
#print axioms LeanFX2.RawStep.par.diamond
#print axioms LeanFX2.RawStep.parStar.confluence
#print axioms LeanFX2.Conv.canonicalRaw
#print axioms LeanFX2.Conv.transRaw
