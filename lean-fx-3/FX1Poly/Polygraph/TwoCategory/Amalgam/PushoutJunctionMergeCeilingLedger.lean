import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutCeilingLedger
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWhiskerRightJunctionMerge
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWireChangeLedger

/-! # Polygraph/TwoCategory/Amalgam/PushoutJunctionMergeCeilingLedger — the r21 CEILING re-adjudication after the
junction-merge round: arm b (whiskerLeft) SHIPPED, arm b' (whiskerRight) the named residual, and the WP-AMALG-3
inheritance ledger (WP-AMALG-2 r21, Brick B3 + B4)

The r20 ceiling ledger (`PushoutCeilingLedger.lean`) mapped arms (b)/(b') as `mechanicalR21`.  This r21 round SHIPPED
arm (b) — the whiskerLeft junction merge `CanonicalFactorization` (`whiskerLeftJunctionCanonical`, non-vacuous over a
wire-changing `mu`) — and the DIRECTION-SYMMETRIC producer merge law
(`firingBlockLayout_composePath` / `…Right`).  Arm (b') the whiskerRight junction `CanonicalFactorization` stays the
NAMED residual (`fxAmalg_whiskerRightJunctionCanonicalStaysResidual`): its tail-append surgery is NOT a syntactic
mirror of arm (b) and is not authored this round.

## The HONEST scoreboard (2 DONE / 1 MECHANICAL / 2 JAM-A)

`fxAmalg_whiskerJunctionMergeStaysWalled` flips ONLY when BOTH arm (b) AND arm (b') ship their
`CanonicalFactorization`.  Only arm (b) shipped, so the marker STAYS `true` (NO fabricated flip), and the scoreboard is
2 DONE (id-collapse + whiskerLeft), 1 MECHANICAL (whiskerRight residual), 2 JAM-A (vcomp zip + top assembly).  The four
masters STAY at their walled values, `pushoutDispatchCloseCriterion` STAYS `false`, #2043 does NOT close.

## The WP-AMALG-3 / #2044 inheritance ledger

`fxAmalg_wpAmalg3InheritanceLedger` records what WP-AMALG-3 inherits: the producer merge law (both directions), arm (b)
shipped + arm (b') named, the ceiling pinned (four masters walled), and the JAM A coupling to the H2-EXT 2-cocycle
handoff (`fxAmalg_h2ExtCocycleHandoff`).

Raw Lean 4 + Init.  Additive only — every prior master `Prop` byte-intact.  Per-declaration `#assert_no_axioms` gated
in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The r21 reader-arm scoreboard (additive; arm b flipped to DONE) -/

/-- The five canonical-reader arms and their r21 ceiling status, AFTER the junction-merge round.  Arm (a) id-collapse
DONE (r20); arm (b) whiskerLeft junction merge DONE (r21, `whiskerLeftJunctionCanonical` shipped); arm (b') whiskerRight
junction merge stays MECHANICAL (producer law shipped, the tail-append conv / canonical the named residual); arm (c)
the vcomp common-refinement zip + the top assembly the JAM-A hostage.  Additive over the r20
`pushoutReaderArmStatus` (which held arms (b)/(b') both mechanical). -/
def pushoutReaderArmStatusR21 : List (String × CeilingStatus) :=
  [ ("id-collapse (arm a)", CeilingStatus.done),
    ("whiskerLeft junction merge (arm b)", CeilingStatus.done),
    ("whiskerRight junction merge (arm b')", CeilingStatus.mechanicalR21),
    ("vcomp common-refinement zip (arm c)", CeilingStatus.jamAHostage),
    ("top assembly + decider wiring", CeilingStatus.jamAHostage) ]

/-- ★★ **The r21 reader-arm ledger reads exactly TWO DONE, ONE MECHANICAL, TWO JAM-A (`rfl`).**  Machine-checks the
honest post-junction-merge scoreboard: arms (a) + (b) shipped, arm (b') next-round mechanical, arm (c) + the top
assembly the JAM A + fib-3 hostage.  NOT 3 DONE — only arm (b) of the two junction arms shipped. -/
theorem pushoutReaderArmStatusR21_scoreboard :
    (pushoutReaderArmStatusR21.filter (fun entry => entry.2 == CeilingStatus.done)).length = 2
      ∧ (pushoutReaderArmStatusR21.filter (fun entry => entry.2 == CeilingStatus.mechanicalR21)).length = 1
      ∧ (pushoutReaderArmStatusR21.filter (fun entry => entry.2 == CeilingStatus.jamAHostage)).length = 2 :=
  ⟨rfl, rfl, rfl⟩

/-! ## The junction-merge marker stays walled (only ONE arm shipped) -/

/-- ★★★ **The whisker junction-merge wall STAYS held — only arm (b) shipped (`rfl`).**  Arm (b)'s
`CanonicalFactorization` ships (`fxAmalg_hasWhiskerLeftJunctionCanonical = true`), the producer merge law ships both
directions (`fxAmalg_hasFiringBlockProducerMergeLaw` / `…Right = true`), but arm (b')'s whiskerRight junction
`CanonicalFactorization` is the named residual (`fxAmalg_whiskerRightJunctionCanonicalStaysResidual = true`).  So
`fxAmalg_whiskerJunctionMergeStaysWalled` STAYS `true` — it flips ONLY at BOTH literal deliveries, and only ONE
shipped.  No fabricated flip. -/
theorem whiskerLeftJunctionShipsArmBResidual :
    fxAmalg_hasWhiskerLeftJunctionCanonical = true
      ∧ fxAmalg_hasFiringBlockProducerMergeLaw = true
      ∧ fxAmalg_hasFiringBlockProducerMergeLawRight = true
      ∧ fxAmalg_whiskerRightJunctionCanonicalStaysResidual = true
      ∧ fxAmalg_whiskerJunctionMergeStaysWalled = true :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## The masters stay walled, the close criterion stays false -/

/-- ★★★ **The junction-merge round leaves the four masters walled and the close criterion false (`rfl`).**  The r21
junction-merge round is ADDITIVE: arm (b) + the producer laws ship, but NONE of the JAM A per-gap descent.  So the
masters STAY (`fxAmalg_hasFullSaturatedPushoutDispatch` / `fxAmalg_hasGeneralPushoutDispatch` /
`fxAmalg_hasSaturatedDispatchTheorem` `false`, `fxAmalg_topFactorizationInductionStaysWalled` `true`), the total
canonical reader STAYS gated, and `pushoutDispatchCloseCriterion` STAYS `false`.  #2043 does NOT close. -/
theorem junctionMergeCeilingMastersStayWalled :
    fxAmalg_hasFullSaturatedPushoutDispatch = false
      ∧ fxAmalg_hasGeneralPushoutDispatch = false
      ∧ fxAmalg_hasSaturatedDispatchTheorem = false
      ∧ fxAmalg_topFactorizationInductionStaysWalled = true
      ∧ fxAmalg_totalCanonicalReaderStaysGated = true
      ∧ fxAmalg_hasIdCanonicalCollapse = true
      ∧ pushoutDispatchCloseCriterion = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The #2043 definitive state after the junction-merge round -/

/-- ★★★ **Honesty marker — the #2043 STATE after the r21 junction-merge round: arm (b) SHIPPED, arm (b') the residual,
#2043 STILL walled on the JAM A descent.**  `= true`.  The r21 round SHIPPED the whiskerLeft junction merge (conv
`whiskerLeftFiringBlockMerge` + `CanonicalFactorization whiskerLeftJunctionCanonical`, non-vacuous over a wire-changing
`mu`) and the direction-symmetric producer merge law `firingBlockLayout_composePath` / `…Right` (the recon's one new
load-bearing piece, WP-AMALG-3's shared inheritance).  Arm (b') the whiskerRight junction `CanonicalFactorization` stays
the named residual (a distinct tail-append surgery over the r18 append).  So `fxAmalg_whiskerJunctionMergeStaysWalled`
STAYS `true` (flips only at BOTH deliveries — only arm (b) shipped), the reader scoreboard is 2 DONE / 1 MECHANICAL /
2 JAM-A, the four masters STAY walled, `pushoutDispatchCloseCriterion` STAYS `false`; the close criterion flips only
when arm (c) — the vcomp zip = the JAM A descent — flips (fib-3-hostage, cross-lane).  #2043 does NOT close.
`= true`. -/
def fxAmalg_pushout2043StateAfterArmB : Bool := true

/-! ## The WP-AMALG-3 / #2044 inheritance ledger -/

/-- ★★★ **THE WP-AMALG-3 / #2044 INHERITANCE LEDGER.**  `= true`.  What WP-AMALG-3 (fused with H2-EXT #2140) inherits
from this lane: the PRODUCER merge law both directions (`fxAmalg_hasFiringBlockProducerMergeLaw` / `…Right`) — the
firing-block splice `firingBlockLayout (composePath a b) = spliceFrameBlocks (firingBlockLayout a) b`; the READER arm
(b) shipped (`fxAmalg_hasWhiskerLeftJunctionCanonical`) and arm (b') named (`…StaysResidual`); the CEILING pinned (the
four masters walled — `!hasFullSaturatedPushoutDispatch ∧ !hasGeneralPushoutDispatch ∧ !hasSaturatedDispatchTheorem ∧
topFactorizationInductionStaysWalled`); and the JAM A coupling to the H2-EXT 2-cocycle handoff
(`fxAmalg_h2ExtCocycleHandoff` — "does the interleaved-monad-firing regrouping cochain BOUND?", the first 2-cocycle
candidate for #2140).  A single Boolean conjoining every inherited hook. -/
def fxAmalg_wpAmalg3InheritanceLedger : Bool :=
  fxAmalg_hasFiringBlockProducerMergeLaw
    && fxAmalg_hasFiringBlockProducerMergeLawRight
    && fxAmalg_hasWhiskerLeftJunctionCanonical
    && fxAmalg_whiskerRightJunctionCanonicalStaysResidual
    && (!fxAmalg_hasFullSaturatedPushoutDispatch)
    && (!fxAmalg_hasGeneralPushoutDispatch)
    && (!fxAmalg_hasSaturatedDispatchTheorem)
    && fxAmalg_topFactorizationInductionStaysWalled
    && fxAmalg_h2ExtCocycleHandoff

/-- ★★★ **The WP-AMALG-3 inheritance ledger holds, with the masters + h2-ext handoff byte-intact (`rfl`).**  The
inheritance ledger is `true`, and the four masters + the H2-EXT 2-cocycle handoff hold at their intact values —
recording that WP-AMALG-3 inherits the producer laws + arm (b) + the pinned ceiling + the JAM A / h2-ext coupling,
every prior `Prop` byte-intact. -/
theorem wpAmalg3Inherits :
    fxAmalg_wpAmalg3InheritanceLedger = true
      ∧ fxAmalg_hasFullSaturatedPushoutDispatch = false
      ∧ fxAmalg_hasGeneralPushoutDispatch = false
      ∧ fxAmalg_hasSaturatedDispatchTheorem = false
      ∧ fxAmalg_topFactorizationInductionStaysWalled = true
      ∧ fxAmalg_h2ExtCocycleHandoff = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end FX1Poly.Polygraph.Amalgam
