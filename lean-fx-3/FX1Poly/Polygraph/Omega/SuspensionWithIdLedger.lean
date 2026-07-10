import FX1Poly.Polygraph.Omega.BridgeDimTwoWithId
import FX1Poly.Polygraph.Omega.EckmannHiltonWithId
import FX1Poly.Polygraph.Omega.SuspensionWithId
import FX1Poly.Polygraph.Omega.Steiner.SuspensionChainShift

/-! # Polygraph/Omega/DesignLockOmega3WithId — the OMEGA-3 r2 ledger + OMEGA-4 handoff (B5)

The honest ledger of the OMEGA-3 r2 idCongr additive sibling and its cascade, plus the OMEGA-4 (Squier
ascent) handoff spec.  Every shipped piece is cited; every surviving wall is named with its exact goal state
and the named node that blocks it.  This file edits NOTHING outside `Omega/`; in particular the shipped
`fxOmega_omega3Complete` (`Suspension.lean`) and `fxOmega_bridgeDimTwoConvLegOpen` (`DesignLock.lean`) keep
their name and meaning and are NOT touched here (the r2 markers are fresh `fxOmega3_*` names).

## What OMEGA-3 r2 SHIPPED (each machine-checked zero-axiom)

  * **B1 — the idCongr additive sibling.**  `SaturatedConvOverWithId` (11 ctors = the 8 shipped shapes +
    `idCongr` + the two whiskering-1-cell congruences), `IsSaturatedCongruenceWithId`, the 11-arm
    `SaturatedConvOverWithId.recInto`, the free embedding `embedSaturatedConvOver`, and the
    `vcompIdLeft_bridgedWithId` jam discharge (concrete `crownJam_dischargedWithId`).  The recInto induction
    with the dimension-bump `idCongr` arm is propext-clean.
  * **B2 — the soundness cascade over the sibling.**  `linearizeAbsorbsWithId` /
    `linearizeFullAbsorbsWithId` (the three new fields: single-vector `rfl`; chain `idCongr` = the
    degenerate-pole extension; chain whisker-1-cell = the `vcompCongrLeft/Right` mirrors), the two soundness
    folds `linearize_eq_of_saturatedConvWithId` / `linearizeFull_eq_of_saturatedConvWithId`, the two
    refuters, and `suspendPreservesStrictConvWithId` (3 free rfl arms).
  * **B3 — the wall harvest.**  Conservativity on atom words (`atomWord_conv_iff_withId`, via the
    arithmetic separator), whiskered chain completeness at a FIXED whisker
    (`whiskeredAtomWord_conv_iff_linearizeFull_eq`, both verdicts), `freeStrictCongruenceWithId`, and the
    re-targeted `bridgeDimTwoHoldsWithId` statement (jam step discharged).
  * **B4 — conv-form Eckmann-Hilton + suspension shift.**  Interchange collapse
    (`godementComp_conv_vcomp_ofIdBoundaries`, `crownGodement_conv_vcomp`) and commutativity on DISTINCT
    cells (`vcomp_comm_conv_ofIdBoundaries`, `ehGenComm`) over the sibling with the fresh whisker-by-id-1-cell
    unit rows; the suspension chain-table shift (`polesOf_suspend`, `linearizeFull_suspend`).

## The surviving walls (each named with its exact goal + blocking node)

  * **JAM — the general varying-whisker map-IN reconstruct.**  Goal: `SaturatedConvOverWithId crownComputad
    (StrictAxiomRel crownComputad) a b` from `linearizeFull a = linearizeFull b` on the fragment where the
    WHISKERING cells (not just the whiskered cell) vary — composite 1-cells in whisker position.  Blocking
    node: a `reconstructWhiskeredWithId` that reads the whisker off the boundary POLES (the chain table is
    faithful there) and re-whiskers with the whisker-1-cell congruences.  The `→` is shipped (chain
    soundness); the `←` reconstruct is the work.  Recorded by `fxOmega3_generalWhiskeredMapInOpenR2`.

  * **JAM — the full bridge conv leg `bridgeDimTwoHoldsWithId`.**  Goal: the `TwoCellConv →
    SaturatedConvOverWithId` induction over the real dim-2 carrier.  The KEY STEP (`vcompIdLeft`) is
    discharged over the sibling (`crownJam_dischargedWithId`); the composite-1-cell whisker steps have the
    whisker-1-cell congruences shipped but still need `realizePathCellSig (composePath ..)` lifted through
    the sibling (only convertible, not defeq, to the `vcomp`).  Blocking node: the full induction, deferred
    to OMEGA-4.  Recorded by `fxOmega_bridgeDimTwoHoldsWithIdConvLegOpenR2` (`BridgeDimTwoWithId.lean`).

  * **JAM — the multi-generator absolute-index bookkeeping.**  The completeness reconstruct
    (`reconstructCrown`) is length-1 (single generator); the ambient-length >= 2 one-hot reconstruction is
    an arithmetic gap orthogonal to the congruence gap (recon).  Recorded by
    `fxOmega3_multiGeneratorBookkeepingOpenR2`.

  * **WALL (cited, stays) — the FORM-A undecidability ceiling.**  Arbitrary presented word problems stay
    undecidable at every suspended dimension (Post-Markov / Burroni, `CeilingLift.lean`,
    `fxOmega_ceilingLiftUndecidableInstanceMechanized = false`).  The idCongr sibling is a
    congruence-completeness tool; it does NOT dissolve this.

## The honest re-assessment of `fxOmega_omega3Complete`

The shipped `fxOmega_omega3Complete` (`Suspension.lean`, `= false`) named THREE r2 owes: (1) the general
whiskered / multi-generator conv reflection, (2) the conv-form Eckmann-Hilton, (3) the iterated n+k FORM-A
ceiling.  r2 SHIPPED (2) (`fxOmega3_convFormEckmannHiltonShippedR2`) and (3) was already met at r1
(`semiThue_iff_encodedTwoCellSuspended`); but (1) is only partially closed (conservativity on atom words +
whiskered completeness at a FIXED whisker; the general VARYING-whisker reconstruct remains the named JAM).
So NOT all r1 walls are gone: `fxOmega_omega3Complete` stays `false`, honestly, and is NOT flipped.

## The OMEGA-4 (Squier ascent) handoff — the interfaces it consumes

OMEGA-4 turns kernel critical pairs into generating 3-cells and certifies confluence.  It consumes:

  * **The sibling congruence `SaturatedConvOverWithId`** as the dim-2 congruence whose classes the 3-cells
    resolve; its map-out `SaturatedConvOverWithId.recInto` folds any 3-cell-respecting invariant.
  * **The chain table `linearizeFull` / `SteinerChainCell`** as the decidable, boundary-faithful invariant
    certifying 3-cell confluence: `linearizeFull_eq_of_saturatedConvWithId` (soundness) +
    `whiskeredAtomWord_conv_iff_linearizeFull_eq` (decision on the whiskered fragment).
  * **The dimension-raising maps** `suspendCell` / `suspendPreservesStrictConvWithId` /
    `polesOf_suspend` / `linearizeFull_suspend` — so a dim-2 critical-pair resolution VIEWS as a dim-3
    generating 3-cell without re-encoding (the chain table shifts by one degenerate bottom pole).
  * **The open interface** `bridgeDimTwoHoldsWithId` — OMEGA-4 must complete the `TwoCellConv → sibling`
    induction to certify the dim-2 presentation is the free one before ascending.

Raw Lean 4 + Init; a docstring record plus `Bool` markers, so every declaration is axiom-free.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

/-! ## The r2 shipped-piece markers (each cites machine-checked code) -/

/-- ★ **B1 SHIPPED — the idCongr additive sibling.**  `SaturatedConvOverWithId` + `recInto` + the free
embedding + the vcompIdLeft jam discharge, all zero-axiom.  `= true`. -/
def fxOmega3_idCongrSiblingShippedR2 : Bool := true

/-- ★ **B2 SHIPPED — the soundness cascade over the sibling.**  Single-vector + chain absorbing instances
(the degenerate-pole extension included), the two soundness folds, the refuters, suspension preservation.
`= true`. -/
def fxOmega3_soundnessCascadeShippedR2 : Bool := true

/-- ★ **B3 SHIPPED — conservativity + fixed-whisker completeness.**  `atomWord_conv_iff_withId` (the
arithmetic separator) and `whiskeredAtomWord_conv_iff_linearizeFull_eq` (fixed whisker, both verdicts).
`= true`. -/
def fxOmega3_conservativeAndFixedWhiskerShippedR2 : Bool := true

/-- ★ **B4 SHIPPED — conv-form Eckmann-Hilton + the suspension chain shift.**  Interchange collapse +
commutativity on distinct cells over the sibling (via the whisker-by-id-1-cell rows), and
`linearizeFull_suspend` (the chain table shifts by one degenerate bottom pole).  `= true`. -/
def fxOmega3_convFormEckmannHiltonAndShiftShippedR2 : Bool := true

/-! ## The surviving-wall markers (each names the exact jam) -/

/-- ★ **JAM — the general VARYING-whisker map-IN reconstruct is OPEN.**  `= true` records the wall is
present: chain completeness at a FIXED whisker is shipped, but the fragment where the WHISKERING cell varies
needs a reconstruct that reads the whisker off the poles.  The `→` (soundness) is shipped; the `←` is the
work. -/
def fxOmega3_generalWhiskeredMapInOpenR2 : Bool := true

/-- ★ **JAM — the multi-generator absolute-index bookkeeping is OPEN.**  `= true`: the shipped
`reconstructCrown` is length-1 (single generator); the ambient-length >= 2 one-hot reconstruction is an
orthogonal arithmetic gap. -/
def fxOmega3_multiGeneratorBookkeepingOpenR2 : Bool := true

/-- ★ **The honest re-assessment: OMEGA-3 is NOT fully complete.**  `= false` — matching the shipped
`fxOmega_omega3Complete` (which is NOT flipped).  r2 shipped conv-form Eckmann-Hilton (r1 owe 2) and the
suspension arithmetic; but the general varying-whisker / multi-generator conv reflection (r1 owe 1) is only
partially closed (conservativity + fixed-whisker), so not all r1 walls are gone.  Set `true` only when the
general map-IN reconstruct lands. -/
def fxOmega3_omega3CompleteReassessedR2 : Bool := false

/-! ## The OMEGA-4 handoff marker -/

/-- ★ **The OMEGA-4 (Squier ascent) handoff is RECORDED.**  The interfaces OMEGA-4 consumes are named in the
file docstring: the sibling congruence `SaturatedConvOverWithId` + its `recInto` (the classes the 3-cells
resolve), the chain table `linearizeFull` + `linearizeFull_eq_of_saturatedConvWithId` +
`whiskeredAtomWord_conv_iff_linearizeFull_eq` (the confluence-certifying decidable invariant), the
dimension-raising maps `suspendCell` / `suspendPreservesStrictConvWithId` / `polesOf_suspend` /
`linearizeFull_suspend`, and the open interface `bridgeDimTwoHoldsWithId`.  `= true` (recorded). -/
def fxOmega3_omegaFourSquierAscentHandoffRecordedR2 : Bool := true

end FX1Poly.Polygraph.Omega
