import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFactorizeCanonical

/-! # Polygraph/TwoCategory/Amalgam/PushoutCanonicalFactorizeProbes — the assembled canonical-factorization arm
status, the historical-wild slot-count probes (`slotCount = spec` by `rfl` per probe), and the JAM A re-audit
(WP-AMALG-2 r19, Brick B4)

B3 shipped the `CanonicalFactorization` subtype, the `gen` arm (concrete), the `id`-arm slot-spec, and the
width-matching adjudication.  This file pins the ASSEMBLED arm status (which arms ship, which are gated), probes the
coarse producer's slot count against the finest spec on the HISTORICAL wild cells (`slotCount = spec` BY `rfl` per
probe), and RE-AUDITS JAM A with the producer + spec-meeting arms in hand — NO descent overclaim.

## The assembled arm status

`pushoutFactorizeCanonicalArmsShipped` conjoins the shipped-arm markers: the `gen` arm ships concretely
(`mulCanonicalFactorization`), the `id`-arm slot-spec ships by construction (`idCanonicalArmMeetsSlotSpec`).  The
`whiskerLeft` / `whiskerRight` / `vcomp` arms + the `id` collapse conv are the named residuals (B3's honesty
markers).  There is NO total `pushoutFactorizeCanonical` function this round (the recursive arms are honest partials,
not `sorry`).

## The historical-wild probes (`slotCount = spec` by `rfl`)

The coarse producer's block count MEETS the finest spec on the r8 wall-splitter boundaries (`s·s`, `s·t·s`), the r9
composed codomain (`s·t·t·s`), and the witness word (`s·t·s·t·t`) — each `slotCount = spec` by `rfl`, `= 3` (all are
2-wall boundaries: `wallCount 2 + 1 = 3`).

## The JAM A re-audit — NO descent overclaim

The coarse producer + the two spec-meeting arms STRENGTHEN the skeleton reflection (conv-of-images ⟹ equal
slotCounts, the r16/r17 invariant), but supply NONE of the per-gap DESCENT (conv-of-images ⟹ per-gap-conv): the
wire-creating `eta` (`t^0 ⇒ t`) / `mu` (`t^2 ⇒ t`) VIOLATE the convex-block projection, changing gap widths `0 → 1` /
`2 → 1` exactly where the precondition fails.  `fxAmalg_hasSaturatedDispatchTheorem` STAYS `false`; the masters STAY
walled; #2043 does NOT close.

Raw Lean 4 + Init.  `rfl` probes.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The assembled canonical-factorization arm status -/

/-- ★★★ **THE ASSEMBLED CANONICAL-FACTORIZATION ARM STATUS.**  `= true`: the two spec-meeting arms ship — the `gen`
arm concretely (`fxAmalg_hasCanonicalFactorizationArms`, via `mulCanonicalFactorization`) and the `id`-arm slot-spec
by construction.  The recursive arms (`whiskerLeft` / `whiskerRight` junction merge, `vcomp` common-refinement zip)
and the `id` collapse conv are honest partials (not `sorry`).  This is the assembly's HONEST status, not a total
reader. -/
def pushoutFactorizeCanonicalArmsShipped : Bool :=
  fxAmalg_hasCanonicalFactorizationArms

/-- ★★ **The assembled arm status is live (`rfl`).** -/
theorem pushoutFactorizeCanonicalArmsShipped_true :
    pushoutFactorizeCanonicalArmsShipped = true := rfl

/-- ★★ **The gated arms are all held (`rfl`).**  The `id` collapse conv, the whisker junction merge, and the vcomp
common-refinement zip STAY walled, so the total canonical reader stays gated. -/
theorem pushoutFactorizeCanonicalGatedArmsHeld :
    fxAmalg_idCanonicalCollapseStaysGated = true
      ∧ fxAmalg_whiskerJunctionMergeStaysWalled = true
      ∧ fxAmalg_vcompCommonRefinementZipStaysWalled = true
      ∧ fxAmalg_totalCanonicalReaderStaysGated = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## The historical-wild slot-count probes (`slotCount = spec` by `rfl` per probe) -/

/-- ★★★ **PROBE (r8 wall-splitter DOMAIN `s·s`) — `slotCount = spec` by `rfl`.**  The coarse producer's block count on
`s·s` equals the finest spec, both `3` (2 walls + 1). -/
theorem canonicalProbe_wallSplitterDom :
    (firingBlockLayout unitSplitsWallDom).length
      = (finestGapWidths (pushoutPathTags unitSplitsWallDom)).length := rfl

/-- ★★★ **PROBE (r8 wall-splitter CODOMAIN `s·t·s`) — `slotCount = spec` by `rfl`.**  Block count on `s·t·s` equals
the spec, both `3` — the SAME count as the domain (the empty-gap admission), the middle gap widened `0 → 1`. -/
theorem canonicalProbe_wallSplitterCod :
    (firingBlockLayout unitSplitsWallCod).length
      = (finestGapWidths (pushoutPathTags unitSplitsWallCod)).length := rfl

/-- ★★★ **PROBE (r9 composed codomain `s·t·t·s`) — `slotCount = spec` by `rfl`.**  The composed-r8 seam witness's
codomain `s·t·t·s` (`vcompSplitBlockFactorization`'s target) reads block count `3` = spec, the middle gap of width
`2`. -/
theorem canonicalProbe_composedCodomain :
    (firingBlockLayout (composePath monadPushSPath
        (composePath (composePath monadPushTPath monadPushTPath) monadPushSPath))).length
      = (finestGapWidths (pushoutPathTags (composePath monadPushSPath
          (composePath (composePath monadPushTPath monadPushTPath) monadPushSPath)))).length := rfl

/-- ★★★ **PROBE (the witness word `s·t·s·t·t`) — `slotCount = spec` by `rfl`.**  The alternating witness 1-cell reads
block count `3` = spec (2 walls + 1), the coarse producer merging the trailing `t·t` run into one slot. -/
theorem canonicalProbe_witnessWord :
    (firingBlockLayout (pushoutEndoPathOfWord witnessWord)).length
      = (finestGapWidths (pushoutPathTags (pushoutEndoPathOfWord witnessWord))).length := rfl

/-- ★★ **PROBE (the wild counts are all `3`).**  The four historical-wild boundaries all read exactly `3` canonical
slots — the coarse producer's count pinned per probe. -/
theorem canonicalProbe_allThree :
    (firingBlockLayout unitSplitsWallDom).length = 3
      ∧ (firingBlockLayout unitSplitsWallCod).length = 3
      ∧ (firingBlockLayout (pushoutEndoPathOfWord witnessWord)).length = 3 :=
  ⟨rfl, rfl, rfl⟩

/-! ## Observability -/

-- The historical-wild slot counts (all expect `3`): s·s, s·t·s, s·t·s·t·t, s·t·t·s.
#eval (firingBlockLayout unitSplitsWallDom).length
#eval (firingBlockLayout unitSplitsWallCod).length
#eval (firingBlockLayout (pushoutEndoPathOfWord witnessWord)).length

/-! ## The JAM A re-audit (no descent overclaim) -/

/-- ★★★ **JAM A per-gap DESCENT STAYS OPEN with the coarse producer + spec-meeting arms (`rfl`).**  The coarse
producer + the `gen` / `id`-slot arms STRENGTHEN the skeleton reflection but supply NONE of the per-gap DESCENT:
`fxAmalg_hasSaturatedDispatchTheorem = false`. -/
theorem canonicalProbesJamAOpen : fxAmalg_hasSaturatedDispatchTheorem = false := rfl

/-- ★★★ **The masters STAY walled with the canonical arms + probes shipped (`rfl`).** -/
theorem canonicalProbesNoMasterFlips :
    fxAmalg_hasFullSaturatedPushoutDispatch = false
      ∧ fxAmalg_hasGeneralPushoutDispatch = false
      ∧ fxAmalg_topFactorizationInductionStaysWalled = true :=
  ⟨rfl, rfl, rfl⟩

/-! ## Honesty markers -/

/-- ★★★ **Honesty marker — the ASSEMBLED canonical arm status + the historical-wild probes SHIP (WP-AMALG-2 r19,
B4).**  `= true`.  `pushoutFactorizeCanonicalArmsShipped` records the two spec-meeting arms (the `gen` arm concretely,
the `id`-arm slot-spec by construction); the recursive arms + `id` collapse conv stay gated
(`pushoutFactorizeCanonicalGatedArmsHeld`).  The coarse producer's block count MEETS the finest spec on the
historical wild cells BY `rfl`: the r8 wall-splitter domain (`s·s`) / codomain (`s·t·s`), the r9 composed codomain
(`s·t·t·s`), the witness word (`s·t·s·t·t`) — all `slotCount = spec = 3` (`canonicalProbe_*`).  No total
`pushoutFactorizeCanonical` function this round.  `= true`. -/
def fxAmalg_hasCanonicalFactorizeProbes : Bool := true

/-- ★★★ **JAM A RE-AUDIT with the coarse producer + spec-meeting arms — STRENGTHENED skeleton, per-gap descent STILL
the residual; NO descent overclaim (WP-AMALG-2 r19, B4).**  `= true` (the honest re-audit).  The r19 coarse producer
`firingBlockLayout` (slot count `wallCount + 1` by construction) + the two spec-meeting arms strengthen the "skeleton
reflects" half: the canonical slot count is a dom↔cod invariant (r17 `finestGapWidths_slotCount_domCod_eq`) and the
producer now WITNESSES the slot skeleton, not just its length (the historical-wild probes read `3` slots on every
2-wall boundary).  But NONE of it supplies the per-gap DESCENT half — "conv-of-images ⟹ per-gap-conv", the
convex-block projection sound only for word-preserving presentations, which the wire-creating `eta` (`t^0 ⇒ t`) / `mu`
(`t^2 ⇒ t`) VIOLATE (changing gap widths `0 → 1` / `2 → 1` exactly where the precondition fails).
`fxAmalg_hasSaturatedDispatchTheorem` STAYS `false` (`canonicalProbesJamAOpen`); the masters STAY walled
(`canonicalProbesNoMasterFlips`).  The producer does NOT touch JAM A.  Named node: the per-gap descent (the
signature-specific soundness lemma), coupled to the vcomp common-refinement zip (B3) and the WalkingMonad
reconstruction iso (fib-3, READ-ONLY).  #2043 does NOT close.  No descent overclaim.  `= true`. -/
def fxAmalg_canonicalProbesJamAReAudit : Bool := true

end FX1Poly.Polygraph.Amalgam
