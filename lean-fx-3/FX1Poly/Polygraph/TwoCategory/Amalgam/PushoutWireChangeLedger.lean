import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWallCountInvariance
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadWordVcompGen

/-! # Polygraph/TwoCategory/Amalgam/PushoutWireChangeLedger — the r6 LEDGER: the wire-changing wall, correctly
NARROWED, and the #2140 H2-EXT handoff (WP-AMALG-2 r6, B3/B5 — the dichotomy round)

r6 adjudicated the #2043 wire-changing wall.  Neither pure horn is the whole truth: the FIRST-HORN STRUCTURE is
TRUE and shipped (the wall-count invariance, `PushoutWallCountInvariance.lean`, B1); the first horn's "…and the
arbitrary-word Decidable then assembles" OVERREACHES; the residual is a CONSUME-only COMPLETENESS object, NOT a
genuine no-go — the second horn's obstruction candidates are BOTH refuted.  This file records the r6 section of the
ledger: what shipped, what the residual REALLY is (a real narrowing, not a re-statement), the named nodes, and the
first-2-cocycle handoff to #2140.  It flips NOTHING.

## What B1 shipped (the first-horn STRUCTURE, machine-checked)

`PushoutWallCountInvariance.lean` turned the r5 PROSE ("a wire-changing gap shifts the walls but there are no
`s`-generators") into a forward statement:

  * `wallLetterCount_dom_eq_cod` — every pushout 2-cell preserves the `s`-wall count dom-to-cod (the `gen` case is
    the wall-free boundary of a reconstructed generator; walls live only in inert whisker contexts).
  * `saturatedConv_boundary_wallCount_eq` — under conversion the boundary is a SHARED index, so walls cannot move.
  * `noGeneratorStraddlesWall` — no fired monad law has an `s` in its domain or codomain.

⟹ **Second-horn obstruction (α) [a wall is CONSUMED] is REFUTED** — the wall count is a HARD invariant, doubly.
And obstruction (β) [canonical form not unique when shifts interact] is REFUTED for the structure: the shift is
deterministic (wall `k` sits at cumulative offset `k + Σ_{j<k} width(gap_j)`; a wire-changing gap `t^a ⇒ t^b`
shifts the walls to its right by exactly `b − a`, a running sum of gap-boundary data, no interaction pathology).
There is NO obstruction cell.  The residual is completeness, not impossibility.

## The r5 residual (ii), correctly DEMOTED (the real narrowing)

`PushoutMultiGapFactorization.lean` residual (ii) claimed the reconstructed-signature reseat object "does NOT yet
exist" — the signature-transported image of the CONSUME-only monad word-multiplicativity, needed to collapse a
wire-changing gap to its Eilenberg–Zilber normal form.  **This is an OVERSTATEMENT, corrected here:**

  * `WalkingMonad/MonadWordVcompGen.wordMul_vcompGen` (`#check`ed below) DOES exist over the GENERIC carrier
    `SaturatedConvOver monadModeSignature MonadLawRel` — the monad word-multiplicativity, born generic.
  * `Amalgam/ReconstructedDecision.reseatReflect` (`#check`ed below) already TRANSPORTS a generic monad conv
    (`SaturatedConvOver monadModeSignature MonadLawRel` of reseat-cells) onto the RECONSTRUCTED signature
    (`SaturatedConvOver monadComputad.toModeSignature MonadLawRelReconstructed`) — unconditionally.

So the residual is NOT "the object does not exist".  It is the **ASSEMBLY** `wordMul_vcompGen ∘ reseatReflect` into
a per-gap reconstructed collapse (aligning the `wordFromCounts` cells `wordMul_vcompGen` speaks with the
`reseatCell` images `reseatReflect` consumes) PLUS the whole-cell factorization induction.  A genuine narrowing:
the ingredients are located and shipped; only the gap-by-gap regrouping of interleaved monad firings is unwritten.

## The genuine residual — the FACTORIZATION-COMPLETENESS wall (named nodes)

The full arbitrary-word Decidable needs the converse `equal-fold ⟹ convertible` for the WHOLE cell
(`RealLawDispatch.lean:242-252` names it): an arbitrary interleaved pushout cell is CONVERTIBLE-to a
wall/gap-whiskered (shifted-gap) form, so its boundary has ONE canonical NF.  Two named nodes:

  * **`the whole-cell factorization induction`** — re-group interleaved monad firings gap-by-gap via
    interchange/Godement (the wall-commute is FREE, `crossComponentWhiskerCommute`); the residual (i)
    purification / convex-block projection (`DispatchSaturated.lean` residual (iii)) is the DUAL framing of this
    same obligation (Nelson–Oppen purification = project the pushout derivation back to per-gap monad derivations).
  * **`the per-gap gap-EZ reseat assembly`** — `wordMul_vcompGen ∘ reseatReflect` aligned into a per-gap
    reconstructed collapse (the narrowed residual (ii) above).

Neither is authorable in the Amalgam lane this round (the monad-lane regrouping is CONSUME-only), and neither is an
impossibility.

## The #2140 H2-EXT handoff (the plan-move-40 seed)

The whole-cell factorization-completeness obstruction — the non-existence (this round) of a whole-cell NF weaving
the monad EZ normal form through the `s`-whisker contexts — is exactly a COHERENCE 2-COCYCLE on the pushout: the
failure to trivialize the interleaved-firing regrouping cochain.  Handed to #2140 as the FIRST 2-cocycle
candidate: **"does the interleaved-monad-firing regrouping cochain bound?"**  If it bounds, the factorization
completeness follows and the arbitrary-word Decidable assembles; if not, the coherence obstruction is a genuine
H² class.

## HELD — no flip (the honest verdict)

`fxAmalg_hasFullSaturatedPushoutDispatch` (`DispatchSaturated.lean`) stays `false`; `fxAmalg_hasGeneralPushoutDispatch`
(`PushoutBundle.lean`) stays `false`; `fxAmalg_pushoutNormalFormSpliceStaysWalled`,
`fxAmalg_multiGapFactorizationStaysWalled`, `fxAmalg_arbitraryCellFactorizationStaysWalled` stay `true`.  **#2043
does NOT close** at the wire-changing / shared-generator scope (WP-AMALG-3 inherits it).  This file adds markers
ONLY; it touches no shipped marker.  No fabricated flip.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The narrowing, machine-witnessed: the reseat ingredients EXIST -/

-- The GENERIC monad word-multiplicativity `wordMul_vcompGen` EXISTS (over `SaturatedConvOver monadModeSignature
-- MonadLawRel`) — refuting the r5 residual (ii) "the object does not exist".
#check @wordMul_vcompGen
-- The reconstructed-signature transport `reseatReflect` EXISTS (generic monad conv ↦ reconstructed-signature conv)
-- — the second half of the located, shipped reseat ingredients.
#check @reseatReflect

/-! ## Honesty markers — the r6 ledger -/

/-- ★★★ **Honesty marker — the r5 reseat-object "does not exist" residual is DEMOTED (r6 correction).**  `= true`:
the reconstructed-signature reseat is NOT a missing object.  Its two ingredients are located and shipped —
`WalkingMonad/MonadWordVcompGen.wordMul_vcompGen` (the GENERIC monad word-multiplicativity over `SaturatedConvOver
monadModeSignature MonadLawRel`) and `Amalgam/ReconstructedDecision.reseatReflect` (the reconstructed-signature
transport of a generic monad conv), both `#check`ed above.  So the r5 residual (ii) is DEMOTED from "the object
does not exist" to "the ASSEMBLY `wordMul_vcompGen ∘ reseatReflect` into a per-gap reconstructed collapse is
unwritten" — a genuine narrowing (the ingredients EXIST; only the alignment + regrouping is residual).  This is a
DEMOTION of the residual framing, NOT a claim that completeness is discharged.  `= true`. -/
def fxAmalg_wordMulReseatObjectExists : Bool := true

/-- **Honesty marker — the FACTORIZATION-COMPLETENESS wall stays walled (the genuine r6 residual).**  `= true` (the
wall is honestly held).  The first-horn STRUCTURE ships (B1, the wall-count invariance); what OVERREACHES is "…and
the arbitrary-word Decidable then assembles".  The residual is the converse `equal-fold ⟹ convertible` for the
WHOLE cell: an arbitrary interleaved pushout cell is CONVERTIBLE-to shifted-gap (wall/gap-whiskered) form.  Two
named nodes: (a) the WHOLE-CELL FACTORIZATION INDUCTION (re-group interleaved monad firings gap-by-gap via
interchange/Godement — the wall-commute FREE via `crossComponentWhiskerCommute`; the dual framing of residual (i)
purification, `DispatchSaturated.lean` residual (iii)); (b) the PER-GAP GAP-EZ RESEAT ASSEMBLY (`wordMul_vcompGen ∘
reseatReflect` aligned per gap — the narrowed residual (ii)).  This is COMPLETENESS, NOT impossibility: there is no
obstruction cell (obstructions (α)/(β) both REFUTED by B1).  Named node: the pushout whole-cell factorization NF.
Not authorable in the Amalgam lane (the monad-lane regrouping is CONSUME-only).  `= true`. -/
def fxAmalg_factorizationCompletenessStaysWalled : Bool := true

/-- ★ **Honesty marker — the H2-EXT #2140 handoff (the plan-move-40 seed).**  `= true`: the whole-cell
factorization-completeness obstruction (the non-existence THIS ROUND of a whole-cell NF weaving the monad
Eilenberg–Zilber form through the `s`-whisker contexts) is packaged as the FIRST 2-COCYCLE CANDIDATE for #2140 —
the failure to trivialize the interleaved-monad-firing regrouping cochain is exactly a coherence 2-cocycle on the
pushout.  Handed to #2140 as: "does the interleaved-monad-firing regrouping cochain BOUND?"  (Bounds ⟹ factorization
completeness ⟹ the arbitrary-word Decidable assembles; does not bound ⟹ a genuine H² coherence class.)  This is a
HANDOFF marker, not a discharge.  `= true`. -/
def fxAmalg_h2ExtCocycleHandoff : Bool := true

/-- **Honesty marker — r6 NARROWS the wire-changing residual and FLIPS NOTHING; #2043 stays OPEN.**  `= true` (the
honest r6 verdict).  This round shipped the first-horn STRUCTURE (the wall-count invariance, B1 — obstructions
(α)/(β) refuted) and correctly DEMOTED the r5 reseat "object does not exist" residual to an assembly residual (the
ingredients `wordMul_vcompGen` / `reseatReflect` EXIST).  It did NOT ship the whole-cell factorization completeness
/ the arbitrary-word Decidable, and it FLIPPED NO marker: `fxAmalg_hasFullSaturatedPushoutDispatch`
(`DispatchSaturated.lean`) stays `false`, `fxAmalg_hasGeneralPushoutDispatch` (`PushoutBundle.lean`) stays `false`,
`fxAmalg_pushoutNormalFormSpliceStaysWalled` / `fxAmalg_multiGapFactorizationStaysWalled` /
`fxAmalg_arbitraryCellFactorizationStaysWalled` stay `true`.  #2043 does NOT close — WP-AMALG-3 inherits the
wire-changing / shared-generator scope.  No fabricated flip.  `= true`. -/
def fxAmalg_r6NarrowsWireChangeResidual : Bool := true

end FX1Poly.Polygraph.Amalgam
