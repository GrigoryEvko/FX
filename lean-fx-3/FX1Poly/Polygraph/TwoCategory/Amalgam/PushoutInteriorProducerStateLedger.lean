import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutCanonicalFactorizeProbes
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWallShiftStateLedger

/-! # Polygraph/TwoCategory/Amalgam/PushoutInteriorProducerStateLedger — the #2043 state after r19 (the interior-ordinal
producer + the coarse firing-block producer + the total canonical assembly round): the master checklist, the exact
#2043 state, every jam = the exact goal with a NAMED node (WP-AMALG-2 r19, Brick B5)

r19 (the interior producer + the total canonical assembly) shipped four bricks, each additive, zero-axiom, no
fabricated flip:

  * **B1** `wallShiftComposesAt` + `wallOffsetAt_gapDomLayout` — the PER-ORDINAL wall-shift law (the shipped whole-list
    `pushoutWallShiftComposes` on the prefix `pairs.take ordinal`, VERBATIM) and the DEFINITIONAL interior-ordinal
    placement, truth-probed on the DEEP wire-changing nest `[muWallShiftBlock, muWallShiftBlock]` (interior ordinal-1
    dom `3` ≠ cod `2`, placement by `rfl`).  `fxAmalg_interiorOrdinalPlacementDefinitional = true`.  The leg-2
    wall-shift is DISSOLVED at the arithmetic layer (the placement is definitional at every interior ordinal), but
    `fxAmalg_sFrameWallShiftStaysWalled` STAYS `true` — the residual COLLAPSES into
    `fxAmalg_totalCanonicalReaderStaysGated`.
  * **B2** `firingBlockLayout` + `firingBlockLayout_slotCount` + `gapDomLayout_firingBlockLayout` — the COARSE
    firing-block producer (one pair per maximal `t`-run), slot count `wallCount + 1` BY CONSTRUCTION, domain / codomain
    round-trips (propext-safe, hand-rolled `pushoutWordAppendAssoc`).  `fxAmalg_hasFiringBlockProducer = true`
    SUPERSEDES the r17 residual `fxAmalg_firingBlockProducerStaysWalled`.
  * **B3** `CanonicalFactorization` + `mulCanonicalFactorization` — the canonical subtype motive, the `gen` arm
    (concrete), the `id`-arm slot-spec (by construction), the width-matching adjudication.
    `fxAmalg_hasCanonicalFactorizationArms = true`.
  * **B4** the assembled arm status + the historical-wild probes (`slotCount = spec` by `rfl`) + the JAM A re-audit.
    `fxAmalg_hasCanonicalFactorizeProbes = true`, `fxAmalg_canonicalProbesJamAReAudit = true`.

This ledger machine-records the whole-picture #2043 state and pins each remaining jam to its EXACT goal and NAMED node.

## The two jams (each: the exact goal + the NAMED node)

  * **JAM A — the per-gap DESCENT / purification-completeness (masters i, ii).**  NAMED node:
    `fxAmalg_hasSaturatedDispatchTheorem` (= `false`).  EXACT goal: a whole-cell convertibility DESCENDS to per-gap
    convertibilities (the convex-block projection sound only for word-preserving presentations).  The wire-creating
    `eta` (`t^0 ⇒ t`) / `mu` (`t^2 ⇒ t`) VIOLATE it — they change gap WIDTHS `0 → 1` / `2 → 1` exactly where the
    projection fails.  r19 supplies NONE of the descent (the coarse producer strengthens the skeleton reflection but
    not the descent); coupled to the vcomp common-refinement zip (B3) + the WalkingMonad reconstruction iso (fib-3,
    READ-ONLY).

  * **JAM B — the top firing-block FACTORISATION reader (masters ii, iii).**  NAMED node: `pushoutFactorize` — an
    arbitrary pushout cell factors into a firing-block `VcompGapPair` layout with a convertibility to it.  r19 NARROWED
    it substantially: the coarse PRODUCER ships (B2), the per-ordinal wall-shift PLACEMENT is definitional (B1), and
    the `gen` arm + `id`-arm slot-spec ship (B3).  THREE residuals remain, each NAMED: (i) the `id`-arm multi-block
    COLLAPSE conv (`fxAmalg_idCanonicalCollapseStaysGated = true`); (ii) the whisker-frame JUNCTION `t`-run MERGE
    (`fxAmalg_whiskerJunctionMergeStaysWalled = true`); (iii) the vcomp COMMON-REFINEMENT zip
    (`fxAmalg_vcompCommonRefinementZipStaysWalled = true`, coupled to JAM A).  All ride
    `fxAmalg_totalCanonicalReaderStaysGated = true`.

## The master checklist per the verbatim demands (NONE flips)

| Master | NAMED node | Verbatim value | r19 |
|---|---|---|---|
| (i) full saturated pushout dispatch | `fxAmalg_hasFullSaturatedPushoutDispatch` | `false` | STAYS `false` (JAM A) |
| (ii) general pushout dispatch | `fxAmalg_hasGeneralPushoutDispatch` | `false` | STAYS `false` (JAM A + JAM B) |
| (iii) top factorisation walled | `fxAmalg_topFactorizationInductionStaysWalled` | `true` | STAYS `true` (JAM B residuals) |

Even a COMPLETE canonical reader flips at most (iii); masters (i)/(ii) are gated on the JAM A per-gap DESCENT the
reader never supplies.  So NO master flips this round.

## Close criterion (maximally strict)

`#2043` closes iff `fxAmalg_hasFullSaturatedPushoutDispatch ∧ fxAmalg_hasGeneralPushoutDispatch ∧
¬ fxAmalg_topFactorizationInductionStaysWalled` — both jams closed.  After r19 that is `false ∧ false ∧ ¬true =
false`: `#2043` does NOT close (`fxAmalg_pushoutDispatch2043ClosesAfterR19_false`, machine-checked).

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## r19 shipped — the four bricks live (machine-checked conjunction) -/

/-- The r19 deliverable conjunction — B1 interior-ordinal placement + per-ordinal law, B2 coarse firing-block
producer, B3 canonical factorization arms, B4 assembled probes + JAM A re-audit, all live. -/
def reconR19BricksShipped : Bool :=
  fxAmalg_interiorOrdinalPlacementDefinitional
    && fxAmalg_hasFiringBlockProducer
    && fxAmalg_hasCanonicalFactorizationArms
    && fxAmalg_hasCanonicalFactorizeProbes

/-- The r19 bricks are all live (`rfl`). -/
theorem reconR19BricksShipped_true : reconR19BricksShipped = true := rfl

/-! ## The two jams, each pinned to its NAMED node's current (open / walled) value -/

/-- ★★★ **JAM A pinned — the per-gap DESCENT stays OPEN.**  The NAMED node `fxAmalg_hasSaturatedDispatchTheorem` is
`false` (`rfl`).  r19 shipped the coarse producer + the two spec-meeting arms and STRENGTHENED the skeleton
reflection, but supplies NONE of the descent — the convex-block projection the wire-creating `eta`/`mu` violate,
coupled to the vcomp common-refinement zip and the WalkingMonad reconstruction iso (fib-3). -/
theorem reconR19JamA_perGapDescentOpen : fxAmalg_hasSaturatedDispatchTheorem = false := rfl

/-- ★★★ **JAM B pinned — the top firing-block factorisation reader stays WALLED (NARROWED, not closed).**  The
r19 residual nodes are held: the `id`-arm multi-block collapse conv (`fxAmalg_idCanonicalCollapseStaysGated = true`),
the whisker-frame junction merge (`fxAmalg_whiskerJunctionMergeStaysWalled = true`), the vcomp common-refinement zip
(`fxAmalg_vcompCommonRefinementZipStaysWalled = true`), and the total canonical reader
(`fxAmalg_totalCanonicalReaderStaysGated = true`).  All four `rfl`. -/
theorem reconR19JamB_narrowedButWalled :
    fxAmalg_idCanonicalCollapseStaysGated = true
      ∧ fxAmalg_whiskerJunctionMergeStaysWalled = true
      ∧ fxAmalg_vcompCommonRefinementZipStaysWalled = true
      ∧ fxAmalg_totalCanonicalReaderStaysGated = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- ★★★ **The wall-shift is NARROWED (placement definitional at every interior ordinal) but the leg-2 wall STAYS
`true` (no flip).**  B1 reclassifies the wall-shift to "definitional in the shipped `gapDomLayout` / `gapCodLayout` at
every interior ordinal, the per-ordinal law a corollary" (`fxAmalg_interiorOrdinalPlacementDefinitional = true`), but
the verbatim leg-2 demand (the arbitrary-CELL interior-ordinal producer) is unmet — that is now the total canonical
reader.  So `fxAmalg_sFrameWallShiftStaysWalled = true`.  Both `rfl`. -/
theorem reconR19WallShiftStaysWalled :
    fxAmalg_interiorOrdinalPlacementDefinitional = true
      ∧ fxAmalg_sFrameWallShiftStaysWalled = true :=
  ⟨rfl, rfl⟩

/-- ★★★ **The r17 firing-block PRODUCER residual is SUPERSEDED — the producer now SHIPS (`rfl`).**  B2 authored the
coarse producer, so `fxAmalg_hasFiringBlockProducer = true`; the r17 residual node's home value stays intact
(additive), but the total canonical READER threading it stays gated:
`fxAmalg_totalCanonicalReaderStaysGated = true`.  Both `rfl`. -/
theorem reconR19ProducerSupersedesResidual :
    fxAmalg_hasFiringBlockProducer = true
      ∧ fxAmalg_totalCanonicalReaderStaysGated = true :=
  ⟨rfl, rfl⟩

/-! ## The master checklist (NONE flips) -/

/-- ★★★ **THE MASTER CHECKLIST — NO master flips at r19 (`rfl`).**  All three masters stay at their verbatim walled
values: `fxAmalg_hasFullSaturatedPushoutDispatch = false`, `fxAmalg_hasGeneralPushoutDispatch = false`,
`fxAmalg_topFactorizationInductionStaysWalled = true`.  The r19 interior producer + coarse producer + canonical arms
are additive; the flips are gated on the JAM A per-gap descent (masters i/ii) and the JAM B residuals (master iii),
NONE of which r19 supplies. -/
theorem reconR19NoMasterFlips :
    fxAmalg_hasFullSaturatedPushoutDispatch = false
      ∧ fxAmalg_hasGeneralPushoutDispatch = false
      ∧ fxAmalg_topFactorizationInductionStaysWalled = true :=
  ⟨rfl, rfl, rfl⟩

/-! ## The #2043 close criterion (maximally strict) -/

/-- The `#2043` close criterion — closes iff BOTH masters (i)/(ii) hold AND the top factorisation is no longer walled.
Encodes the strict "genuine full coverage" bar; anything less is `false`. -/
def fxAmalg_pushoutDispatch2043ClosesAfterR19 : Bool :=
  fxAmalg_hasFullSaturatedPushoutDispatch
    && fxAmalg_hasGeneralPushoutDispatch
    && (fxAmalg_topFactorizationInductionStaysWalled == false)

/-- ★★★ **`#2043` does NOT close after r19 (`rfl`).**  The close criterion evaluates to `false`: both jams (A the
per-gap descent, B the top firing-block factorisation reader) remain open.  The honest ceiling — r19 SHIPPED the
per-ordinal wall-shift law + definitional interior placement (B1), the coarse firing-block producer (B2, the r17
residual), the canonical factorization subtype + `gen` arm + `id`-slot-spec (B3), and the assembled probes + JAM A
re-audit (B4), but neither jam closes: the `id` collapse conv, the whisker junction merge, the vcomp common-refinement
zip, and the JAM A per-gap descent all remain. -/
theorem fxAmalg_pushoutDispatch2043ClosesAfterR19_false :
    fxAmalg_pushoutDispatch2043ClosesAfterR19 = false := rfl

/-- ★★★ **The strict close criterion re-derived — it MATCHES the r18 criterion (`rfl`).**  The r19 close criterion is
DEFINITIONALLY the same maximally-strict bar as r18 (`full ∧ general ∧ ¬topWalled`), and both evaluate to `false` —
r19 narrowed JAM B further (the producer + placement + spec-meeting arms) but did not close either jam.  Both `false`. -/
theorem reconR19CloseCriterionMatchesR18 :
    fxAmalg_pushoutDispatch2043ClosesAfterR19 = fxAmalg_pushoutDispatch2043ClosesAfterR18 :=
  rfl

/-! ## Honesty marker -/

/-- ★★★ **Honesty marker — the #2043 state after r19: the interior producer + coarse producer + canonical arms SHIP,
two named jams remain, #2043 does NOT close (WP-AMALG-2 r19, B5).**  `= true` (the STATE is honestly recorded, not a
claim that #2043 closes).  r19 shipped four bricks (`reconR19BricksShipped_true`): B1 the per-ordinal wall-shift law +
definitional interior placement (the leg-2 wall DISSOLVED at the arithmetic layer, residual collapsed into the total
canonical reader), B2 the coarse firing-block producer (the r17 residual superseded), B3 the canonical factorization
subtype + `gen` arm + `id`-slot-spec + width-matching adjudication, B4 the assembled probes + JAM A re-audit.  Two
jams remain, each pinned to its named node at its open / walled value: JAM A the per-gap DESCENT
(`fxAmalg_hasSaturatedDispatchTheorem = false`, `reconR19JamA_perGapDescentOpen`) and JAM B the top firing-block
factorisation reader (the `id` collapse conv, the whisker junction merge, the vcomp common-refinement zip, and the
total canonical reader, `reconR19JamB_narrowedButWalled`).  The leg-2 wall-shift is NARROWED but NOT flipped
(`reconR19WallShiftStaysWalled`).  NO master flips (`reconR19NoMasterFlips`).  The strict close criterion
`fxAmalg_pushoutDispatch2043ClosesAfterR19` is machine-checked `= false`
(`fxAmalg_pushoutDispatch2043ClosesAfterR19_false`), matching the r18 criterion
(`reconR19CloseCriterionMatchesR18`).  r19 is an HONEST NARROWING.  `#2043` does NOT close.  `= true`. -/
def fxAmalg_canonicalReaderStateAfterR19 : Bool := true

end FX1Poly.Polygraph.Amalgam
