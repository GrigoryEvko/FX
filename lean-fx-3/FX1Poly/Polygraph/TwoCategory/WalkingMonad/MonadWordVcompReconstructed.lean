import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadWordVcompGen
import FX1Poly.Polygraph.TwoCategory.Amalgam.MonadReseatInverse

/-! # WalkingMonad/MonadWordVcompReconstructed — the VERTICAL word multiplicativity RESEATED onto the
reconstructed pushout signature (WP-AMALG-2 r14, Brick B1 — Finding-C's cross-lane reseat)

`MonadWordVcompGen.wordMul_vcompGen` closed the vertical word multiplicativity over the GENERIC carrier
`SaturatedConvOver monadModeSignature MonadLawRel`.  The pushout world (Amalgam) speaks a DIFFERENT signature —
`monadComputad.toModeSignature` with `MonadLawRelReconstructed`.  Finding-C (`PushoutWallFreeInversionLedger`) was
blocked NOT on proving `wordMul_vcompGen` but on TRANSPORTING it onto that reconstructed signature — the r10
"signature-transported reseat" the pushout lane could not author.  r14 gives the Amalgam lane ownership of
`WalkingMonad/`, so this file authors it, ADDITIVELY (the shipped `wordMul_vcomp` / `wordMul_vcompGen` untouched,
consumed READ-ONLY).

The transport is cheap: every ingredient is shipped.

  * **`reconWordFromCounts`** — the reconstructed-signature canonical word, DEFINED as the inverse-reseat image
    `reseatCellInv (wordFromCounts cc)`.  So the reseat homomorphism lemmas do all the structural work — no word
    structure is re-derived over the reconstructed carrier.
  * ★★ **`wordMul_vcompReconstructed`** — the vertical word multiplicativity over `monadComputad.toModeSignature`
    `MonadLawRelReconstructed`: `reseatConvBackward (wordMul_vcompGen …)` transports the generic conv, then
    `reseatCellInv_vcomp` + `reseatCellInv_castBoundary` (both `rfl` / `cases;rfl`) distribute `reseatCellInv` over
    the `vcomp` / `castBoundary` structure, folding each `reseatCellInv (wordFromCounts _)` into
    `reconWordFromCounts _`.  The reconstructed word being the inverse-reseat image is exactly what makes this a
    one-line transport rather than a re-derivation.

Truth probes on the r8-counterexample-shaped cells (`PushoutFinestPayloadZip`'s `s·t·s` middle 1-cell, gaps `[t]`
/ `[t,t]`): the genuine merges `t²⇒t` (`composeCounts [1,1] [2] = [2]`) and `t³⇒t²` (`composeCounts [1,1,1] [2,1]
= [2,1]`) FIRE; the r8 δ₁/δ₀ non-mergeable faces STAY refuted by the shipped `reconFacesDecideFalse` (this reseat
is essential-surjectivity CONTENT, not an over-identification — it merges the mergeable, and a lift of
`wordMul_vcompGen`, which respects `composeCounts`, cannot manufacture the faces' equality).

Raw Lean 4 + Init; `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; the reseat kit is all
`rfl` / `cases;rfl`, so the transport is propext-clean by construction.  Per-declaration `#assert_no_axioms` gated
in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The reconstructed-signature canonical word -/

/-- The **reconstructed-signature canonical word** — the bespoke Eilenberg–Zilber word `wordFromCounts cc`
transported by the inverse reseat functor onto `monadComputad.toModeSignature`.  Its boundaries are the
`reseatPathInv` images of the bespoke word's boundaries (`countsDomainPath cc` / `monadTPower cc.length`). -/
def reconWordFromCounts (cc : List Nat) :
    RawTwoCellExpr monadComputad.toModeSignature
      (reseatPathInv (countsDomainPath cc)) (reseatPathInv (monadTPower cc.length)) :=
  reseatCellInv (wordFromCounts cc)

/-- `reconWordFromCounts` unfolds to the inverse-reseat image of the bespoke word (`rfl`). -/
theorem reconWordFromCounts_eq (cc : List Nat) :
    reconWordFromCounts cc = reseatCellInv (wordFromCounts cc) := rfl

/-! ## ★★ THE RESEAT — vertical word multiplicativity over the reconstructed signature -/

/-- ★★ **The RESEAT: vertical word multiplicativity over the reconstructed pushout signature.**  The reconstructed
twin of `wordMul_vcompGen`: vertically composing two reconstructed canonical words is the reconstructed canonical
word of their block-sum composition (`composeCounts`), up to the `reseatPathInv`-image boundary casts.  This is
exactly the conv `PushoutNormalForm.pushoutRightImageCompletenessLift` consumes — Finding-C's cross-lane residual,
now authorable.

Route: `reseatConvBackward (wordMul_vcompGen ccR ccL hlen)` yields the conv between
`reseatCellInv (vcomp (word ccL) (cast (word ccR)))` and `reseatCellInv (cast (word (composeCounts ccL ccR)))`;
`reseatCellInv_vcomp` (`rfl`) and `reseatCellInv_castBoundary` (`cases;rfl`) distribute `reseatCellInv` over the
`vcomp` / `castBoundary` structure, each `reseatCellInv (wordFromCounts _)` folding definitionally into
`reconWordFromCounts _`.  No word structure re-derived. -/
theorem wordMul_vcompReconstructed (ccR ccL : List Nat) (hlen : ccL.length = listSum ccR) :
    SaturatedConvOver monadComputad.toModeSignature MonadLawRelReconstructed
      (RawTwoCellExpr.vcomp (reconWordFromCounts ccL)
        (RawTwoCellExpr.castBoundary
          (congrArg reseatPathInv (wordMul_vcomp_hmid ccL ccR hlen)) rfl
          (reconWordFromCounts ccR)))
      (RawTwoCellExpr.castBoundary
        (congrArg reseatPathInv (wordMul_vcomp_hdom ccL ccR hlen))
        (congrArg reseatPathInv (congrArg monadTPower (composeCounts_length ccL ccR)))
        (reconWordFromCounts (composeCounts ccL ccR))) := by
  have base := reseatConvBackward (wordMul_vcompGen ccR ccL hlen)
  rw [reseatCellInv_vcomp, reseatCellInv_castBoundary, reseatCellInv_castBoundary] at base
  exact base

/-! ## Truth probes on the r8-counterexample-shaped cells -/

/-- Truth probe (r8 gap `[t,t]`, the genuine merge): two reconstructed identity strands vertically composed with the
width-2 merge gadget IS the reconstructed merge — `composeCounts [1,1] [2] = [2]`, a genuine reconstructed `t²⇒t`.
The reconstructed twin of `wordMul_vcomp_smoke_mergeGen`; the reseat FIRES on a real merge. -/
theorem wordMul_vcompReconstructed_smoke_merge :
    SaturatedConvOver monadComputad.toModeSignature MonadLawRelReconstructed
      (RawTwoCellExpr.vcomp (reconWordFromCounts [1, 1])
        (RawTwoCellExpr.castBoundary
          (congrArg reseatPathInv (wordMul_vcomp_hmid [1, 1] [2] rfl)) rfl
          (reconWordFromCounts [2])))
      (RawTwoCellExpr.castBoundary
        (congrArg reseatPathInv (wordMul_vcomp_hdom [1, 1] [2] rfl))
        (congrArg reseatPathInv (congrArg monadTPower (composeCounts_length [1, 1] [2])))
        (reconWordFromCounts (composeCounts [1, 1] [2]))) :=
  wordMul_vcompReconstructed [2] [1, 1] rfl

/-- Truth probe (r8 gaps `[t]` then `[t,t]`, the mixed merge): three reconstructed strands over the two-block
partition `[2,1]` — `composeCounts [1,1,1] [2,1] = [2,1]`, a genuine reconstructed `t³⇒t²`.  Confirms the reseat
fires on a MULTI-block layout, not only the single-gap merge. -/
theorem wordMul_vcompReconstructed_smoke_mixed :
    SaturatedConvOver monadComputad.toModeSignature MonadLawRelReconstructed
      (RawTwoCellExpr.vcomp (reconWordFromCounts [1, 1, 1])
        (RawTwoCellExpr.castBoundary
          (congrArg reseatPathInv (wordMul_vcomp_hmid [1, 1, 1] [2, 1] rfl)) rfl
          (reconWordFromCounts [2, 1])))
      (RawTwoCellExpr.castBoundary
        (congrArg reseatPathInv (wordMul_vcomp_hdom [1, 1, 1] [2, 1] rfl))
        (congrArg reseatPathInv (congrArg monadTPower (composeCounts_length [1, 1, 1] [2, 1])))
        (reconWordFromCounts (composeCounts [1, 1, 1] [2, 1]))) :=
  wordMul_vcompReconstructed [2, 1] [1, 1, 1] rfl

/-- **ESTABLISHED — the VERTICAL word multiplicativity is RESEATED onto the reconstructed pushout signature.**
`reconWordFromCounts` (the inverse-reseat image of the canonical word) and `wordMul_vcompReconstructed` over
`SaturatedConvOver monadComputad.toModeSignature MonadLawRelReconstructed`, ADDITIVE (the shipped `wordMul_vcomp` /
`wordMul_vcompGen` untouched).  This is the conv `pushoutRightImageCompletenessLift` consumes — Finding-C's
cross-lane residual made authorable.  The reseat FIRES on the r8 merges (`_smoke_merge` / `_smoke_mixed`) and the
r8 non-mergeable δ₁/δ₀ faces STAY refuted (`reconFacesDecideFalse`, shipped) — CONTENT, not over-identification.
`= true`. -/
def fxAmalg_hasReconstructedWordVcompReseat : Bool := true

end FX1Poly.Polygraph.Amalgam
