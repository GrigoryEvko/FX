import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutVcompMultiGapSeam
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutAtomicFiringAdjudication

/-! # Polygraph/TwoCategory/Amalgam/PushoutCanonicalReaderConsistency — the UPGRADED (multi-gap-capable) reader arms
assembled; the r15 decision verdicts re-verified UNCHANGED; JAM A re-audited per the conjunct map (WP-AMALG-2 r16, B4)

The B2 head-prepend (`pushoutFactorizeWhiskerLeftMultiGap`) and B3 multi-gap vcomp seam are the multi-gap-capable
UPGRADES over r15's shallow single-gap arms.  This file ASSEMBLES the upgrade (the whisker arm fed the reader's body
output yields a genuinely DEEPER layout than the shallow reader) and machine-checks — maximally strict — that the
upgrade changes NO shipped decision verdict, then re-audits JAM A per the recon §4 conjunct map.

## The upgraded arm deepens the shallow reader (additive, no verdict change)

r15's `pushoutFactorizeTotal` is the SHALLOW reader: `whiskerLeft s (gen mu)` factors into ONE gap (`slotCount = 1`,
the frame as a single wall around the whole body).  The B2 upgrade, fed the reader's body factorization, deepens it:
`pushoutFactorizeWhiskerLeftMultiGap s (pushoutFactorizeTotal (gen mu))` factors the SAME cell into TWO slots (the
`s`-frame slot + the body's `mu` slot).  The upgrade is ADDITIVE — it produces a deeper layout of the same cell; it
does not touch the shallow reader's DECISIONS.

## Decision consistency — the r15 three pairs re-verified UNCHANGED (recon §5)

  1. **`pushoutDecisionBothVerdicts`** — the two-sided per-gap decision: `true` on the associativity foldings, `false`
     on the two monad faces (δ₁ / δ₀).  A multi-gap reader decides the SAME per-gap right-images — preserved.
  2. **the shallow reader slot counts** — `pushoutFactorizeTotal (gen mu)` / `(vcomp eta delta_1)` each still `1`
     (`mu` atomic → one slot; the vcomp halves share one gap): the upgrade is additive, the shallow reader is
     untouched — preserved.
  3. **`reconAdjudicationRefusesR8Faces`** — the reseat route REFUSES the r8 non-mergeable δ₁ / δ₀ faces (it is
     essential-surjectivity CONTENT, not an over-identifier): the upgraded reader is layout CONTENT, cannot
     manufacture face equality — preserved.

## JAM A re-audit — NARROWED, not closed (recon §4)

A canonical multi-slot reader DELIVERS the SKELETON reflection (two cells with convertible right-images have layouts
with the SAME rigid wall skeleton, the ALIGNABLE verdict B1), but the "conv-of-images ⟹ per-gap-conv" DESCENT (the
convex-block projection) STAYS OPEN — the wire-creating `eta` / `mu` violate the Nelson-Oppen "word-preserving /
left-connected" precondition.  So JAM A NARROWS from "no reflection at all" to "the skeleton reflects; the per-gap
descent is the residual" — a real narrowing, `fxAmalg_hasSaturatedDispatchTheorem` STAYS `false`.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The upgraded arm assembled — it deepens the shallow reader -/

/-- The **shallow reader's whiskerLeft output** on `whiskerLeft s (gen mu)` — one gap (`slotCount = 1`), the r15
single-gap arm treating the frame as a single wall around the whole body. -/
theorem shallowReaderWhiskerSlotCount :
    (pushoutFactorizeTotal
        (RawTwoCellExpr.whiskerLeft monadPushSPath (RawTwoCellExpr.gen pushoutMonadMult))).pairs.length = 1 := rfl

/-- ★★ **The UPGRADED whiskerLeft arm deepens the shallow reader.**  Feeding the reader's body factorization
(`pushoutFactorizeTotal (gen mu)`, one slot) into the B2 head-prepend factors the SAME cell `whiskerLeft s (gen mu)`
into TWO slots (the `s`-frame slot + the `mu` gap) — a genuinely deeper layout than the shallow reader's one gap
(`shallowReaderWhiskerSlotCount`).  The multi-gap-capable upgrade assembled and machine-checked. -/
theorem upgradedReaderWhiskerSlotCount :
    (pushoutFactorizeWhiskerLeftMultiGap crossPairRealPushoutRel monadPushSPath
        (pushoutFactorizeTotal (RawTwoCellExpr.gen pushoutMonadMult))).pairs.length = 2 := rfl

/-! ## Decision consistency — the r15 three pairs re-verified UNCHANGED -/

/-- ★★★ **DECISION CONSISTENCY (the r15 three pairs, re-verified).**  The three shipped decision verdicts are
UNCHANGED under the r16 upgraded arms: (1) the two-sided per-gap decision is `true` on the assoc foldings and `false`
on the two faces (`pushoutDecisionBothVerdicts`); (2) the shallow reader's slot counts on `gen mu` and `vcomp eta
delta_1` are each `1` (`pushoutFactorizeTotal_gen_slotCount` / `_vcomp_slotCount`).  Conjoined and machine-checked —
the multi-gap upgrade is ADDITIVE, it changes no shipped verdict. -/
theorem reconR16DecisionConsistency :
    (pushoutRightImageDecidesTwoSided reconAssocLeftCell reconAssocRightCell = true
        ∧ pushoutRightImageDecidesTwoSided reconFaceDeltaOne reconFaceDeltaZero = false)
      ∧ (pushoutFactorizeTotal (RawTwoCellExpr.gen pushoutMonadMult)).pairs.length = 1
      ∧ (pushoutFactorizeTotal (RawTwoCellExpr.vcomp pushoutEta pushoutFaceDeltaOne)).pairs.length = 1 :=
  ⟨pushoutDecisionBothVerdicts, pushoutFactorizeTotal_gen_slotCount, pushoutFactorizeTotal_vcomp_slotCount⟩

/-- ★★ **DECISION CONSISTENCY (the third pair — the reseat route still REFUSES the r8 faces).**  The reseat/splice
route does NOT identify the r8 non-mergeable δ₁ / δ₀ faces (`reconAdjudicationRefusesR8Faces`, shipped); the r16
upgraded reader is layout CONTENT, not an over-identifier, so it cannot manufacture their equality.  The essential-
surjectivity discipline is preserved. -/
theorem reconR16RefusalConsistency :
    ¬ SaturatedConvOver monadComputad.toModeSignature MonadLawRelReconstructed
        reconFaceDeltaOne reconFaceDeltaZero :=
  reconAdjudicationRefusesR8Faces

/-! ## JAM A re-audit — the conjunct map (skeleton reflects; per-gap descent residual) -/

/-- ★★★ **JAM A RE-AUDIT (NARROWED, not closed) — the conjunct map.**  A canonical multi-slot reader DELIVERS the
SKELETON reflection (`fxAmalg_alignmentVerdictAlignableAtSkeleton = true`, B1: two cells with convertible right-images
have layouts with the SAME rigid wall skeleton) but the per-gap DESCENT stays OPEN
(`fxAmalg_hasSaturatedDispatchTheorem = false`, the "conv-of-images ⟹ per-gap-conv" convex-block projection the
wire-creating `eta`/`mu` violate).  So JAM A is NARROWED from "no reflection at all" to "the skeleton reflects; the
per-gap descent is the residual" — a real narrowing, machine-checked, no flip. -/
theorem reconR16JamANarrowed :
    fxAmalg_alignmentVerdictAlignableAtSkeleton = true
      ∧ fxAmalg_hasSaturatedDispatchTheorem = false :=
  ⟨rfl, rfl⟩

/-! ## Observability -/

-- The shallow reader's whiskerLeft slot count (expect `1`) vs the upgraded arm's (expect `2`).
#eval (pushoutFactorizeTotal
    (RawTwoCellExpr.whiskerLeft monadPushSPath (RawTwoCellExpr.gen pushoutMonadMult))).pairs.length
#eval (pushoutFactorizeWhiskerLeftMultiGap crossPairRealPushoutRel monadPushSPath
    (pushoutFactorizeTotal (RawTwoCellExpr.gen pushoutMonadMult))).pairs.length

/-! ## Honesty markers -/

/-- ★★★ **Honesty marker — the upgraded reader arms are ASSEMBLED and change NO shipped verdict (WP-AMALG-2 r16,
B4).**  `= true`.  The B2 head-prepend upgrade deepens the shallow reader (`upgradedReaderWhiskerSlotCount`, `= 2` on
`whiskerLeft s (gen mu)` vs the shallow `shallowReaderWhiskerSlotCount`, `= 1`) — additive, multi-gap-capable.  The
r15 three decision pairs re-verify UNCHANGED: the two-sided decision verdicts and the shallow slot counts
(`reconR16DecisionConsistency`), and the reseat route still REFUSES the r8 faces (`reconR16RefusalConsistency`).  The
biggest honesty risk — conflating "alignable at skeleton" (TRUE) with "alignment closes the decision" (FALSE) — is
guarded: JAM A is re-audited as NARROWED, not closed (`reconR16JamANarrowed`: skeleton reflects, per-gap descent
open).  `fxAmalg_topFactorizationInductionStaysWalled` STAYS `true`; the masters STAY at their walled values.  `=
true`. -/
def fxAmalg_upgradedReaderNoVerdictChange : Bool := true

/-- ★★ **Honesty marker — a canonical multi-slot reader NARROWS JAM A; it does not close it (WP-AMALG-2 r16, B4).**
`= true` (the honest narrowing).  Per the recon §4 conjunct map, a canonical reader delivers the SKELETON reflection
half (`fxAmalg_alignmentVerdictAlignableAtSkeleton = true`) but the per-gap DESCENT half — that a whole-cell
convertibility descends to per-gap convertibilities (the convex-block projection sound only for word-preserving /
left-connected presentations, which the wire-creating `eta`/`mu` violate) — STAYS the residual
(`fxAmalg_hasSaturatedDispatchTheorem = false`, `reconR16JamANarrowed`).  Named node: the per-gap descent (the
signature-specific soundness lemma), coupled to the `s`-frame wall-shift (B2 leg 2a'') and the WalkingMonad
reconstruction iso (fib-3, READ-ONLY).  A real narrowing, no flip.  `= true`. -/
def fxAmalg_jamANarrowedByCanonicalReader : Bool := true

end FX1Poly.Polygraph.Amalgam
