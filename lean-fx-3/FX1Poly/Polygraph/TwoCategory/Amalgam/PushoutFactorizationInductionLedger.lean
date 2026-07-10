import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutVcompInterchangeSplice
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutReseatFillWiring
import FX1Poly.Polygraph.TwoCategory.Amalgam.RealCoprojectionLeft

/-! # Polygraph/TwoCategory/Amalgam/PushoutFactorizationInductionLedger — the r7 LEDGER: the crux BOUNDS, the
residual NARROWS to the top induction, and NOTHING flips (WP-AMALG-2 r7, B4/B5)

r7 attacked the whole-cell factorization completeness (the r6 named node (i)) by shipping the CRUX — the vcomp case
of the factorization induction — plus the general canonical layout, the non-crux reduction lemmas, and the
per-gap decision-to-fill reseat wiring.  This file records the r7 section of the ledger: what shipped, the #2140
answer (the regrouping cochain BOUNDS), the precisely-narrowed residual, the STALE-LEDGER corrections, and the
no-flip verdict.  It flips NOTHING.

## What r7 shipped (each machine-checked, zero-axiom)

  * **`PushoutCanonicalLayout.lean`** — the GENERAL canonical wall/gap layout (`VcompGapPair`: per-gap leading
    walls + trailing wall + vertical upper/lower split; `gapDomLayout` / `gapMidLayout` / `gapCodLayout` +
    `gapUpperLayout` / `gapLowerLayout` / `gapVcompLayout`).  Strictly more general than the r6 `shiftedGap*`
    layout — captures differing inter-gap walls, multi-letter walls, gap-first and wall-ending words.
  * **`PushoutVcompInterchangeSplice.lean`** — THE CRUX `vcompGapInterchangeSplice` (`vcomp (gapUpperLayout …)
    (gapLowerLayout …) ≈ gapVcompLayout …`), built from iterated FREE `TwoCellStep.interchange` with ZERO
    `castBoundary`, non-vacuous on the recon's hand-worked interleaved firing at the real pushout signature; plus
    the non-crux reduction lemmas (`hcompId_conv_idComposite`, `whiskerLeft_conv_hcompIdLeading`,
    `whiskerRight_conv_hcompIdTrailing`).
  * **`PushoutReseatFillWiring.lean`** — the per-gap DECISION-to-FILL wiring (`reseatGapFillOfConv`,
    `reseatDecisionDrivenAssocFill` / `reseatDecisionDrivenLeftUnitFill`, `reseatDecisionDrivenSpliceWitness`) —
    node (ii) closed at the shipped per-gap decision + wire-changing splice granularity.

## The #2140 answer — the interleaved-firing regrouping cochain BOUNDS

The r6 ledger (`PushoutWireChangeLedger.fxAmalg_h2ExtCocycleHandoff`) handed #2140 the open question "does the
interleaved-monad-firing regrouping cochain BOUND?"  At the disjoint `involution +_M monad` scope the answer is
**YES**: `vcompGapInterchangeSplice` trivializes the regrouping by a FREE coboundary — the middle-four interchange
is a cast-free constructor (`TwoCellStep.interchange`) inside every saturated conv, at every signature.  So the
cochain is a COBOUNDARY, not a genuine H² class.  This RECLASSIFIES the r6 wall from "possible H² coherence
obstruction" to "authorable cast-free engineering".

**Provenance of the cast-freeness.**  The monad lane's own `wordMul_vcompGen` spent ~100 dense cast lines only
because `wordFromCounts` / `composeCounts` carry `composePath`-associativity casts (`MonadWordVcompGen.lean`,
`monadCastBoundary_castBoundary` / `castBoundary_wordCongr` seam-fusion).  The canonical layout INTERLEAVES the
walls, so every layout boundary is built with matching `composePath` nesting and NO cast survives — the same
absorption the r6 shifted splice found (`multiGapShiftedSplice`, no `castBoundary`).

## The precisely-narrowed residual (the named node)

The full arbitrary-word Decidable still needs the TOP-LEVEL factorization induction `pushoutFactorize`: an
arbitrary pushout cell FACTORS into a `VcompGapPair` layout with a convertibility to it.  With the crux (vcomp) and
the reduction lemmas (id / whisker) shipped, the residual is exactly:

  * **the reconstruction bridge** — read a CANONICAL `VcompGapPair` list off an arbitrary cell's boundary via
    `blockDecompose`↔`composePath` (`InterleavingNF.lean`'s alternating decomposition), keyed to B1's wall-count
    skeleton (`wallLetterCount_dom_eq_cod`);
  * **the top induction assembly** — the 5-case structural induction (`gen` = one pure-`t` gap; `id` / `whisker`
    via the reduction lemmas; `vcomp` via the crux) producing ONE layout keyed to that canonical decomposition;
  * **the decider wiring** — `pushoutFullTwoSidedDecision` from the factorization + `pushoutRightImageTwoSidedDecision`
    (per gap) + `multiGapShiftedSplice` (isTrue thread) + `arityFoldRealPushoutCongruence` (isFalse, already total).

Named node: **the top-level `pushoutFactorize` induction assembly + the reconstruction bridge + the decider
wiring**.  This is COMPLETENESS engineering, NOT an impossibility — there is no obstruction cell (B1 refutes both
r5 obstruction candidates; the crux refutes the cochain-bound worry).

## STALE-LEDGER corrections (do not re-cite these as open)

  * `DispatchLedger.lean`'s "LEFT real coprojection — `inclusionLeftTwoReal` does not exist" jam is **STALE**:
    `inclusionLeftTwoReal` SHIPS (`RealCoprojectionLeft.lean:87`, `#check`ed below) with
    `fxAmalg_hasRealGeneratorCoprojectionLeft = true` (`:140`).  Both right AND left real coprojections now ship.
  * `DispatchSaturated.lean:44-48` residual (i) "genuine-generator coprojection needs `interpretWordFrom_map` …
    `= false`" is SUPERSEDED for the coprojection question by the shipped real coprojections.

## HELD — no flip (the honest r7 verdict)

`fxAmalg_hasFullSaturatedPushoutDispatch` (`DispatchSaturated.lean`) stays `false`; `fxAmalg_hasGeneralPushoutDispatch`
(`PushoutBundle.lean`) stays `false`; `fxAmalg_factorizationCompletenessStaysWalled` (`PushoutWireChangeLedger.lean`),
`fxAmalg_pushoutNormalFormSpliceStaysWalled` (`PushoutNormalForm.lean`),
`fxAmalg_arbitraryCellFactorizationStaysWalled` (`PushoutMultiGapFactorization.lean`) stay `true`.  **#2043 does NOT
close** — WP-AMALG-3 inherits the shared-generator scope.  This file adds markers ONLY; it touches no shipped
marker.  No fabricated flip.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The shipped ingredients, machine-witnessed -/

-- THE CRUX — the vcomp case of the factorization induction, built from free interchange (the cochain BOUNDS).
#check @vcompGapInterchangeSplice
-- The per-gap reseat wiring — a right-image conv packs into a splice-ready fill (node (ii)).
#check @reseatGapFillOfConv
-- STALE-LEDGER witness — the LEFT real coprojection EXISTS (refuting the DispatchLedger "does not exist" jam).
#check @inclusionLeftTwoReal

/-! ## Honesty markers — the r7 ledger -/

/-- ★★★ **Honesty marker — r7 ships the CRUX and FLIPS NOTHING; #2043 stays OPEN.**  `= true` (the honest r7
verdict).  This round shipped the general canonical layout (`PushoutCanonicalLayout.lean`), THE CRUX vcomp-case
splice `vcompGapInterchangeSplice` (`PushoutVcompInterchangeSplice.lean`, cast-free from iterated free interchange,
non-vacuous on the interleaved firing), the non-crux reduction lemmas, and the per-gap decision-to-fill reseat
wiring (`PushoutReseatFillWiring.lean`).  It did NOT ship the top-level `pushoutFactorize` induction, and it FLIPPED
NO marker: `fxAmalg_hasFullSaturatedPushoutDispatch` (`DispatchSaturated.lean`) stays `false`,
`fxAmalg_hasGeneralPushoutDispatch` (`PushoutBundle.lean`) stays `false`,
`fxAmalg_factorizationCompletenessStaysWalled` / `fxAmalg_pushoutNormalFormSpliceStaysWalled` /
`fxAmalg_arbitraryCellFactorizationStaysWalled` stay `true`.  #2043 does NOT close — WP-AMALG-3 inherits the
shared-generator scope.  No fabricated flip.  `= true`. -/
def fxAmalg_r7ShipsCruxNoFlip : Bool := true

/-- ★★ **Honesty marker — the residual NARROWS to the top induction + reconstruction bridge + decider wiring.**
`= true` (the wall honestly held, precisely narrowed).  With the crux (vcomp case) and the non-crux reduction
lemmas (id / whisker) shipped, the whole-cell factorization completeness needs exactly three remaining pieces: (a)
the reconstruction bridge (`blockDecompose`↔`composePath`, keyed to B1's wall skeleton) reading a canonical
`VcompGapPair` list off an arbitrary cell; (b) the top-level 5-case induction assembly producing one layout keyed
to that decomposition; (c) the decider wiring `pushoutFullTwoSidedDecision` (factorization + per-gap
`pushoutRightImageTwoSidedDecision` + `multiGapShiftedSplice` isTrue thread + `arityFoldRealPushoutCongruence`
isFalse, already total).  This is COMPLETENESS engineering, NOT impossibility — no obstruction cell exists (B1
refutes both r5 obstruction candidates; the crux refutes the cochain-bound worry).  Named node: the top-level
`pushoutFactorize` induction assembly + reconstruction bridge + decider wiring.  `= true`. -/
def fxAmalg_r7NamedResidualTopInduction : Bool := true

/-- **Honesty marker — the DispatchLedger LEFT-coprojection "does not exist" jam is STALE (r7 correction).**
`= true` (the stale flag is honestly raised).  `DispatchLedger.lean`'s r1/r3 jam "LEFT real coprojection —
`inclusionLeftTwoReal` does not exist" is refuted by the SHIPPED `inclusionLeftTwoReal` (`RealCoprojectionLeft.lean`,
`#check`ed above) with `fxAmalg_hasRealGeneratorCoprojectionLeft = true`; `DispatchSaturated.lean`'s residual (i)
"genuine-generator coprojection needs `interpretWordFrom_map` … `= false`" is likewise superseded FOR THE
COPROJECTION QUESTION (both right and left real coprojections ship).  Do not re-cite these as open.  This is a
STALE-FLAG marker; the FULL dispatch stays walled on the top induction (`fxAmalg_r7NamedResidualTopInduction`), not
on the coprojection.  `= true`. -/
def fxAmalg_dispatchLedgerLeftCoprojectionStaleFlag : Bool := true

end FX1Poly.Polygraph.Amalgam
