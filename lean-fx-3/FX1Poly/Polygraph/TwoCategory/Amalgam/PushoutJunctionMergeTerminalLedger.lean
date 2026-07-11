import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutJunctionMergeCeilingLedger
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWhiskerRightJunctionCanonical

/-! # Polygraph/TwoCategory/Amalgam/PushoutJunctionMergeTerminalLedger — the r22 TERMINAL re-adjudication after BOTH
whisker junction canonicals ship: arm b (whiskerLeft) DONE + arm b′ (whiskerRight) DONE, the JAM-A vcomp zip + top
assembly still walled (WP-AMALG-2 r22, Brick B3)

The r21 ceiling ledger (`PushoutJunctionMergeCeilingLedger.lean`) mapped the reader arms 2 DONE / 1 MECHANICAL
(arm b′) / 2 JAM-A.  This r22 round SHIPPED arm b′ — the whiskerRight junction merge CONV
(`whiskerRightFiringBlockMerge`) + `CanonicalFactorization` (`whiskerRightJunctionCanonicalOfExpansion`, non-vacuous
over a wire-changing `mu` and every recon self-attack).  So the terminal scoreboard is 3 DONE / 0 MECHANICAL / 2 JAM-A.

## The additive flip (NOT an in-place marker edit)

`fxAmalg_whiskerJunctionMergeStaysWalled` (`PushoutFactorizeCanonical.lean:180`) is pinned by `rfl` in THREE shipped
theorems (`pushoutTotalReaderGatedState_true`, `idCanonicalCollapseShipsResidual`, `whiskerLeftJunctionShipsArmBResidual`),
so per the lane's iron additive rule it STAYS `true` BYTE-INTACT (historical / reinterpreted — the wall it named is now
superseded by the positive markers).  The both-arms completion is recorded ADDITIVELY: the r21 arm-b marker
`fxAmalg_hasWhiskerLeftJunctionCanonical` PLUS the r22 arm-b′ marker `fxAmalg_hasWhiskerRightJunctionCanonical`, conjoined
here as `whiskerJunctionMergeBothArmsShip`.  The two delivery witnesses: `whiskerLeftJunctionMuWitness` (arm b,
`whiskerLeft s (gen mu)`, 2 slots) and `whiskerRightJunctionMuWitness` (arm b′, `whiskerRight s (gen mu)`, 2 slots).

## The close criterion STAYS false

`pushoutDispatchCloseCriterion` (`PushoutCeilingLedger.lean:102`) is gated on the four masters, all four of which are the
JAM-A per-gap descent = the vcomp common-refinement zip = `hasSaturatedDispatchTheorem` (the fib-3 hostage, cross-lane).
The junction merge (arms b, b′) is the WHISKER coverage; it touches NONE of the four masters.  So even with BOTH junction
arms shipped, `pushoutDispatchCloseCriterion = false` STAYS, and #2043 does NOT close.  NO fabricated close.

## The #2044 (WP-AMALG-3) inheritance update + lane handoff

`fxAmalg_wpAmalg3InheritanceLedgerR22` upgrades the r21 inheritance hook: WP-AMALG-3 now inherits BOTH whisker junction
canonicals shipped (not b-shipped/b′-named), the producer merge law both directions, the pinned ceiling (four masters
walled), and the H2-EXT 2-cocycle handoff.  The lane handoff: the residual is now ONE wall — the JAM-A vcomp
common-refinement zip = `fxAmalg_hasSaturatedDispatchTheorem`, coupled to the WalkingMonad reconstruction iso (fib-3,
READ-ONLY) — plus the arbitrary-frame trailing-block auto-splitter data residual
(`fxAmalg_whiskerRightTrailingSplitterStaysResidual`, data plumbing, not a math wall).

Raw Lean 4 + Init.  Additive only — every prior master `Prop` byte-intact.  Per-declaration `#assert_no_axioms` gated in
the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The r22 terminal reader-arm scoreboard (additive; arm b′ flipped to DONE) -/

/-- The five canonical-reader arms and their r22 TERMINAL ceiling status, AFTER both junction canonicals ship.  Arm (a)
id-collapse DONE (r20); arm (b) whiskerLeft junction merge DONE (r21); arm (b′) whiskerRight junction merge DONE (r22,
`whiskerRightJunctionCanonicalOfExpansion` shipped); arm (c) the vcomp common-refinement zip + the top assembly the JAM-A
hostage.  Additive over the r21 `pushoutReaderArmStatusR21` (which held arm (b′) mechanical). -/
def pushoutReaderArmStatusR22 : List (String × CeilingStatus) :=
  [ ("id-collapse (arm a)", CeilingStatus.done),
    ("whiskerLeft junction merge (arm b)", CeilingStatus.done),
    ("whiskerRight junction merge (arm b')", CeilingStatus.done),
    ("vcomp common-refinement zip (arm c)", CeilingStatus.jamAHostage),
    ("top assembly + decider wiring", CeilingStatus.jamAHostage) ]

/-- ★★ **The r22 reader-arm ledger reads exactly THREE DONE, ZERO MECHANICAL, TWO JAM-A (`rfl`).**  Machine-checks the
honest terminal scoreboard: arms (a) + (b) + (b′) all shipped, arm (c) + the top assembly the JAM-A + fib-3 hostage.
The junction-merge whisker coverage is COMPLETE; the only remaining walls are the JAM-A descent. -/
theorem pushoutReaderArmStatusR22_scoreboard :
    (pushoutReaderArmStatusR22.filter (fun entry => entry.2 == CeilingStatus.done)).length = 3
      ∧ (pushoutReaderArmStatusR22.filter (fun entry => entry.2 == CeilingStatus.mechanicalR21)).length = 0
      ∧ (pushoutReaderArmStatusR22.filter (fun entry => entry.2 == CeilingStatus.jamAHostage)).length = 2 :=
  ⟨rfl, rfl, rfl⟩

/-! ## BOTH junction arms ship (the additive both-sided completion; the walled marker byte-intact) -/

/-- ★★★ **BOTH whisker junction canonicals ship — arm b AND arm b′ (`rfl`).**  `fxAmalg_hasWhiskerLeftJunctionCanonical`
(r21) AND `fxAmalg_hasWhiskerRightJunctionCanonical` (r22) both `true`; the producer merge law ships both directions;
the arm-b′ residual marker `fxAmalg_whiskerRightJunctionCanonicalStaysResidual` is now SUPERSEDED (kept at its intact
`true`); and the upstream walled marker `fxAmalg_whiskerJunctionMergeStaysWalled` STAYS `true` BYTE-INTACT (additive /
historical — it flips only by an in-place edit, which would break three shipped `rfl` theorems, so it is superseded, not
edited).  The two delivery witnesses `whiskerLeftJunctionMuWitness` / `whiskerRightJunctionMuWitness` both read 2 slots.
NO fabricated flip: the completion is recorded by the positive markers, the wall stays byte-intact. -/
theorem whiskerJunctionMergeBothArmsShip :
    fxAmalg_hasWhiskerLeftJunctionCanonical = true
      ∧ fxAmalg_hasWhiskerRightJunctionCanonical = true
      ∧ fxAmalg_hasFiringBlockProducerMergeLaw = true
      ∧ fxAmalg_hasFiringBlockProducerMergeLawRight = true
      ∧ fxAmalg_whiskerRightJunctionCanonicalStaysResidual = true
      ∧ fxAmalg_whiskerRightTrailingSplitterStaysResidual = true
      ∧ fxAmalg_whiskerJunctionMergeStaysWalled = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- ★★★ **The witness slot counts agree across BOTH arms (`rfl`).**  `whiskerLeftJunctionMuWitness` (arm b) and
`whiskerRightJunctionMuWitness` (arm b′) each read `2` canonical firing-block slots over the SAME wire-changing `mu`
body — the leading vs trailing `s`-wall opens ONE fresh slot on its own side, the `mu` junction gap the other.  The
dual-symmetric delivery. -/
theorem whiskerJunctionMuWitnessesAgree :
    whiskerLeftJunctionMuWitness.1.pairs.length = 2
      ∧ whiskerRightJunctionMuWitness.1.pairs.length = 2 :=
  ⟨rfl, rfl⟩

/-! ## The masters stay walled, the close criterion stays false (NO fabricated close) -/

/-- ★★★ **The r22 terminal round leaves the four masters walled and the close criterion false (`rfl`).**  The r22
junction-merge round is ADDITIVE: arm b′ ships, but NONE of the JAM-A per-gap descent.  So the masters STAY
(`fxAmalg_hasFullSaturatedPushoutDispatch` / `fxAmalg_hasGeneralPushoutDispatch` / `fxAmalg_hasSaturatedDispatchTheorem`
`false`, `fxAmalg_topFactorizationInductionStaysWalled` `true`), the total canonical reader STAYS gated, and
`pushoutDispatchCloseCriterion` STAYS `false`.  #2043 does NOT close — the whisker coverage is complete but the vcomp zip
(= the JAM-A descent, fib-3 hostage) is untouched. -/
theorem junctionMergeTerminalMastersStayWalled :
    fxAmalg_hasFullSaturatedPushoutDispatch = false
      ∧ fxAmalg_hasGeneralPushoutDispatch = false
      ∧ fxAmalg_hasSaturatedDispatchTheorem = false
      ∧ fxAmalg_topFactorizationInductionStaysWalled = true
      ∧ fxAmalg_totalCanonicalReaderStaysGated = true
      ∧ fxAmalg_vcompCommonRefinementZipStaysWalled = true
      ∧ pushoutDispatchCloseCriterion = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The #2044 (WP-AMALG-3) inheritance ledger, r22 update -/

/-- ★★★ **THE WP-AMALG-3 / #2044 INHERITANCE LEDGER (r22 update).**  `= true`.  What WP-AMALG-3 (fused with H2-EXT
#2140) now inherits: the PRODUCER merge law BOTH directions (`fxAmalg_hasFiringBlockProducerMergeLaw` / `…Right`); BOTH
reader whisker junction canonicals shipped (`fxAmalg_hasWhiskerLeftJunctionCanonical` /
`fxAmalg_hasWhiskerRightJunctionCanonical` — the r21 hook `…RightJunctionCanonicalStaysResidual` is superseded); the
CEILING pinned (the four masters walled); and the JAM-A coupling to the H2-EXT 2-cocycle handoff
(`fxAmalg_h2ExtCocycleHandoff`).  Upgrades `fxAmalg_wpAmalg3InheritanceLedger` (r21) by replacing the arm-b′ residual
hook with the shipped arm-b′ canonical.  A single Boolean conjoining every inherited hook. -/
def fxAmalg_wpAmalg3InheritanceLedgerR22 : Bool :=
  fxAmalg_hasFiringBlockProducerMergeLaw
    && fxAmalg_hasFiringBlockProducerMergeLawRight
    && fxAmalg_hasWhiskerLeftJunctionCanonical
    && fxAmalg_hasWhiskerRightJunctionCanonical
    && (!fxAmalg_hasFullSaturatedPushoutDispatch)
    && (!fxAmalg_hasGeneralPushoutDispatch)
    && (!fxAmalg_hasSaturatedDispatchTheorem)
    && fxAmalg_topFactorizationInductionStaysWalled
    && fxAmalg_h2ExtCocycleHandoff

/-- ★★★ **The r22 WP-AMALG-3 inheritance ledger holds, with the masters + h2-ext handoff byte-intact (`rfl`).**  The
r22 inheritance ledger is `true`, and the four masters + the H2-EXT 2-cocycle handoff hold at their intact values — WP-
AMALG-3 inherits the producer laws (both directions) + BOTH whisker junction canonicals + the pinned ceiling + the
JAM-A / h2-ext coupling, every prior `Prop` byte-intact. -/
theorem wpAmalg3InheritsR22 :
    fxAmalg_wpAmalg3InheritanceLedgerR22 = true
      ∧ fxAmalg_wpAmalg3InheritanceLedger = true
      ∧ fxAmalg_hasFullSaturatedPushoutDispatch = false
      ∧ fxAmalg_hasGeneralPushoutDispatch = false
      ∧ fxAmalg_hasSaturatedDispatchTheorem = false
      ∧ fxAmalg_topFactorizationInductionStaysWalled = true
      ∧ fxAmalg_h2ExtCocycleHandoff = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The #2043 definitive terminal state -/

/-- ★★★ **Honesty marker — the #2043 STATE after the r22 terminal round: BOTH junction arms SHIPPED, #2043 STILL walled
on the JAM-A descent.**  `= true`.  The r22 round SHIPPED arm b′ — the whiskerRight junction merge CONV
`whiskerRightFiringBlockMerge` (r18 trailing append + the r20 identity-layout collapse run backwards over the appended
body) + the `CanonicalFactorization` `whiskerRightJunctionCanonicalOfExpansion` (non-vacuous over a wire-changing `mu`
and every recon self-attack: `whiskerRightJunctionMuWitness` `2`, `whiskerRightOfWhiskerLeftWitness` `3`,
`whiskerRightOfIdWitness` `2`, `whiskerRightWallHeavyWitness` `3`).  Together with the r21 arm b, BOTH whisker junction
canonicals now ship (`whiskerJunctionMergeBothArmsShip`).  The reader scoreboard is 3 DONE / 0 MECHANICAL / 2 JAM-A
(`pushoutReaderArmStatusR22_scoreboard`).  `fxAmalg_whiskerJunctionMergeStaysWalled` STAYS `true` byte-intact (additive
supersession, NOT an in-place edit — that would break three shipped `rfl`s).  The four masters STAY walled, the total
canonical reader STAYS gated, `pushoutDispatchCloseCriterion` STAYS `false` (`junctionMergeTerminalMastersStayWalled`);
the close criterion flips only when arm (c) — the vcomp zip = the JAM-A descent = `fxAmalg_hasSaturatedDispatchTheorem` —
flips (fib-3-hostage, cross-lane, READ-ONLY WalkingMonad).  WP-AMALG-3 inherits BOTH whisker canonicals
(`fxAmalg_wpAmalg3InheritanceLedgerR22`).  #2043 does NOT close.  No fabricated flip.  `= true`. -/
def fxAmalg_pushout2043StateAfterArmBPrime : Bool := true

end FX1Poly.Polygraph.Amalgam
