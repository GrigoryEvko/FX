import LeanFX2.Reduction.RawPar
import LeanFX2.Reduction.RawParWeakenInv
import LeanFX2.Reduction.RawParInversion
import LeanFX2.Reduction.RawParRename
import LeanFX2.Reduction.RawParCompatible
import LeanFX2.Confluence.RawCd
import LeanFX2.Confluence.RawCdRename
import LeanFX2.Confluence.RawCdDominates
import LeanFX2.Confluence.RawCdLemma
import LeanFX2.Confluence.ChurchRosser
import LeanFX2.Confluence.CanonicalForm
import LeanFX2.Foundation.RawPartialRename
import LeanFX2.Foundation.RawPartialRenameCommute

/-! # AuditD252HcompBeta — D2.5.2 hcomp-β cascade zero-axiom audit
(Phase A: raw layer only).

Closes the raw-layer cascade for cubical hcomp at constant-path
sides.  Phase A ships the raw ctors plus the full cd cascade
(rename / compat / inversion / cd-rename / cd-dominates / cd-lemma).
Phase B (typed `Step.hcompBeta` + typed par mirror + ConvBridge arm)
lands in a separate future session.

## What landed

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

## Why this matters

Cubical hcomp with constant-path sides is the cubical analog of
"transp at constant path is identity" (D2.5.4 transpReflBeta).
Without this β rule, the kernel's cubical fragment had a hole at the
hcomp-trivial-filler site.  The semantic justification: in CCHM
cubical, `hcomp [φ → λi. anything] cap` reduces to the cap when the
sides are constant in the cube direction (the filler is the cap
itself).

The deep ctor (`hcompBetaDeep`) exists purely to close the cd
cascade: when cd develops the sides to `pathLam X.weaken` shape via
parallel reduction, the β must fire even though the original term
wasn't syntactically a constant pathLam.  Standard Tait-Martin-Löf
complete-development trick, identical in shape to
`transpReflBetaDeep`.

## Confluence preserved

The shipped ctors do NOT regress confluence.  The four headline
theorems remain zero-axiom after Phase A:
* `RawStep.par.cd_lemma`
* `RawStep.par.diamond`
* `RawStep.parStar.confluence`
* `Conv.canonicalRaw` / `Conv.transRaw`

## Phase B (deferred to future session)

Phase B extends the cascade to the typed layer:
* `Step.hcompBeta` — typed β ctor (parallels `Step.transpReflBeta`)
* `Step.par.hcompBeta` — typed par mirror
* `ParRed` / `ParInductive` mirrors
* `ConvBridge` arm
* Update `lift_hcomp_cong` to handle β arms (currently restricted
  to the cong arm only — see `Term/PreservesTerm/TierTwoBinary.lean`).

Until Phase B, both ctors are documented raw-only via
`isDocumentedRawOnlyParity` Section I.

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

-- Headline confluence theorems remain zero-axiom after Phase A
#print axioms LeanFX2.RawStep.par.cd_lemma
#print axioms LeanFX2.RawStep.par.diamond
#print axioms LeanFX2.RawStep.parStar.confluence
#print axioms LeanFX2.Conv.canonicalRaw
#print axioms LeanFX2.Conv.transRaw
