import FX1Poly.Polygraph.TwoCategory.Table.FrobeniusFoldInstance
import FX1Poly.Polygraph.TwoCategory.Table.FrobeniusFusionNF

/-! # Polygraph/TwoCategory/Table/FrobeniusResumeLedger — the FROB-RESUME r1 (#2017) per-brick honest ledger
+ the POLY-TAB migration hook

FROB-RESUME r1 resumes WP-FROB-4 (#2017) on the POLY-TAB (table-driven polygraph) architecture, carrying the
Frobenius spider word problem onto BOTH carriers: carrier B (`List BrauerAtom`, the union-find word engine) where
the decision already lives, and carrier A (`RawTwoCellExpr frobeniusModeSignature`, the free-2-cell expression tree
the POLY-TAB `SaturatedConvOver` layer rides).  This file records what each brick shipped, what stays honestly open
with the exact residual, and the POLY-TAB migration note.

## B1 — THE B-TO-A WIRING (SHIPPED, `Table/FrobeniusReadback.lean`)

`readbackToWord : RawTwoCellExpr frobeniusModeSignature .. -> List BrauerAtom` — the A -> B readback (the recon's
chosen direction: a total structural map on the five `RawTwoCellExpr` constructors, NOT the `Option`-valued
`interpretWordFrom`), transporting the union-find partition invariant `extraSpiderDiagramOf` onto carrier A as
`frobeniusSpiderInvariant`.  Row-preservation for all four `FrobeniusLawRel` rows is the shipped seed soundness
(`frobeniusSpiderInvariant_{unitLeft,frobLeft,frobRight,special}`); non-vacuity is a real fusion row realizing the
connected `{2,2,[0,0,0,0]}` block.  Marker `fxTab_hasFrobeniusReadbackInvariant = true`.  Obstruction (1) [the word
interpreter is not wired] RESOLVED.

## B2 — THE DEEP FOLDREL INSTANCE (PARTIAL, `Table/FrobeniusFoldInstance.lean`)

The deep invariant as `rowConvInvariant` legs: the GENERIC-row `rowsPreserve` leg
(`frobeniusSpiderInvariant_rowsPreserve`, all four rows via seed soundness) and the `vcompCongrLeft` context leg
(`frobeniusSpiderInvariant_vcompLeftPreserves`, routed `spiderConv_complete` -> the shipped uniform suffix
congruence -> `spiderConv_partitionSound`, conditional on `0 < bottomCount` + `BrauerWordInRange`) SHIP, fired
non-vacuously on the `frobLeft` fusion whiskered by `μ`.  Marker `fxTab_hasDeepDiagramFoldLegs = true`.

RESIDUAL, banked precisely (`fxTab_hasDeepDiagramFoldInstance = false`): the FULL six-leg `rowConvInvariant_foldEq`
instance needs (a) `fullPreserves` — the 13-arm `TwoCellConvFull` whose `ofConv` embeds the whole `TwoCellConv`
structural inductive (a nested induction re-expressing the free-2-category laws as `extraSpiderDiagramOf`-word
identities), and (b) the boundary-CHANGING legs (`vcompCongrRight` + the two whisker pad legs), which need a GENERAL
`extraSpiderDiagramOf`-level pad congruence whose shipped carrier-B form carries a `0 < bottomCount` reachability
precondition VIOLATED at the NIL-boundary cells (e.g. `η : id => t`).  Obstruction (3) [the `matchingSameComponent`
whisker gate + the open `relationAgrees`] DISSOLVES on carrier A: its context closure is gate-free
`whiskerLeftCongr` / `whiskerRightCongr`, so the gate never appears in these legs.

## B3 — THE FUSION-NF COMPLETENESS RESUMPTION (DECISION SHIPPED; realization PARTIAL, `Table/FrobeniusFusionNF.lean`)

Completeness + the decision are ALREADY shipped UNCONDITIONALLY (`Frobenius/SpiderCompleteness.lean`, no crossing
comb): `spiderConv_complete` (equal `extraSpiderDiagramOf` ⟹ `SpiderConv`), `instDecidableSpiderConv`, both verdicts
(`spiderConvDecision_bothVerdicts` — `isTrue` on `frobLeft`, `isFalse` on `H`-vs-identity).  The FROB master
`fxFrob_hasSpiderConvDecision = true` is already flipped hypothesis-free — so B3's headline ("if completeness closes:
the #2017 decision + both verdicts") holds WITHOUT new code.  This resume adds the carrier-A face of the
spider-fusion normal form (`fxTab_hasCarrierASpiderFusion = true`): the connected `2 ⇒ 2` Frobenius cells fuse to the
canonical connected spider `canonicalSpiderOf 2 2` on the deep invariant, the left-unit cell fuses to the `1 ⇒ 1`
strand, and the canonical-spider structural recursion (`canonicalSpiderOf_mergeStep` / `_fanStep`) the general
realization folds over.

RESIDUAL (`fxTab_hasGeneralAritySpiderRealization = false`, echoing `fxFrob_hasSpiderFusionNF = false`): the
GENERAL-arity realization `extraSpiderDiagramOf m (canonicalSpiderOf m n) = ⟨m, n, replicate (m+n) 0⟩` for ALL `m`,
`n` is a comb-FREE `foldl` induction over `processBrauer`; its crux is the seed-merge step lemma (prepending
`multAt 0` merges the first two seed wires into the fresh output) — union-find surgery on `stepWiring` /
`unionFindJoin` / fresh-node allocation.  Decoupled from the DECISION (already unconditional); honestly unbuilt.

## HONEST WALLS (unchanged, correctly walled)

  * Cospan closed-count decision — PERMANENTLY walled (`fxFrob_hasCospanClosedCountPermanentWall = true`); the fold
    invariant MUST be the partition-only `extraSpiderDiagramOf`, never the full `spiderDiagramOf`.
  * Carrier-B row-level suffix congruence — walled at B (`fxFrob_hasRowLevelSuffixCongruence = false`), DISSOLVED at
    carrier A (one `whiskerRightCongr` constructor); irrelevant to the fold, which rides carrier A.
  * Multi-block partition→permutation bridge (crossing fragment) — OPEN, off the corelation decision path.

## POLY-TAB migration hook

The Frobenius lane migration takes the **A-carrier presentation**: the free-2-cell `SaturatedConvOver
frobeniusModeSignature FrobeniusLawRel` (`Table/FrobeniusSeed.lean`), whose row-suffix congruence is one generic
`whiskerRightCongr` (the r10 wall dissolved at the seed).  The B1 readback (`readbackToWord`) is the bridge from that
presentation to the shipped carrier-B decision, so a POLY-TAB consumer decides a carrier-A Frobenius 2-cell
convertibility by reading it to a word and running `instDecidableSpiderConv` — no new decision machinery.  The deep
`foldEq` instance (B2 residual) is the remaining piece to make the transport a full `IsSaturatedCongruence` value.

Raw Lean 4 + Init; the aggregate is a `Bool` conjunction of the shipped-brick markers, the open residuals documented
separately.  Additive: nothing outside `Table/` is touched.  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph.Table

open FX1Poly.Polygraph
  (fxTab_hasFrobeniusReadbackInvariant fxTab_hasDeepDiagramFoldLegs fxTab_hasDeepDiagramFoldInstance
    fxTab_hasCarrierASpiderFusion fxTab_hasGeneralAritySpiderRealization
    fxFrob_hasSpiderConvDecision fxFrob_hasConnectedSpiderNF fxFrob_hasSpiderFusionNF)

/-! ## The FROB-RESUME r1 aggregate verdict -/

/-- ★ **The FROB-RESUME r1 (#2017) aggregate verdict — the SHIPPED bricks.**  Conjunction of the bricks that CLOSE:
B1 the B->A wiring + transported deep invariant (`fxTab_hasFrobeniusReadbackInvariant`), B2 the deep `rowConvInvariant`
legs that ship (`fxTab_hasDeepDiagramFoldLegs`), B3 the carrier-A spider fusion (`fxTab_hasCarrierASpiderFusion`), and
the already-shipped #2017 DECISION + connected Fauser NF (`fxFrob_hasSpiderConvDecision`, `fxFrob_hasConnectedSpiderNF`,
both hypothesis-free).  `= true`. -/
def fxTab_frobResumeR1Complete : Bool :=
  fxTab_hasFrobeniusReadbackInvariant
    && fxTab_hasDeepDiagramFoldLegs
    && fxTab_hasCarrierASpiderFusion
    && fxFrob_hasSpiderConvDecision
    && fxFrob_hasConnectedSpiderNF

/-- The aggregate verdict computes to `true`. -/
theorem fxTab_frobResumeR1Complete_holds : fxTab_frobResumeR1Complete = true := rfl

/-! ## The precisely-banked open residuals -/

/-- ★ **The FROB-RESUME r1 open residuals — HONESTLY open, decoupled from the shipped decision.**  Two pieces stay
`false`: (B2) the FULL deep `foldEq` instance `fxTab_hasDeepDiagramFoldInstance` (needs `fullPreserves` + the `n = 0`
boundary-pad edge), and (B3) the general-arity connected realization `fxTab_hasGeneralAritySpiderRealization`
(= `fxFrob_hasSpiderFusionNF`, the seed-merge union-find induction).  Neither blocks the #2017 decision, which is
already unconditional.  This records their honest `false` state as a conjunction. -/
def fxTab_frobResumeR1Residual : Bool :=
  fxTab_hasDeepDiagramFoldInstance
    || fxTab_hasGeneralAritySpiderRealization
    || fxFrob_hasSpiderFusionNF

/-- The residual conjunction computes to `false` — the two open pieces are genuinely unbuilt (not silently claimed). -/
theorem fxTab_frobResumeR1Residual_isOpen : fxTab_frobResumeR1Residual = false := rfl

/-! ## The #2017 decision is shipped hypothesis-free -/

/-- ★ **The #2017 decision leg is shipped hypothesis-free.**  The extraspecial (corelation) word problem decision
`fxFrob_hasSpiderConvDecision` is `true` unconditionally (no `S_n` crossing comb), independently of the two open
residuals — so #2017's decidable-word-problem headline is DELIVERED.  What stays open is the general spider-fusion NF
realization (`fxFrob_hasSpiderFusionNF`), an unbuilt comb-free induction, not a decision blocker. -/
theorem fxTab_frobResumeR1_decisionShipped :
    fxFrob_hasSpiderConvDecision = true ∧ fxFrob_hasSpiderFusionNF = false :=
  ⟨rfl, rfl⟩

end FX1Poly.Polygraph.Table
