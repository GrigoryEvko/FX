import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcPeelSignatureCeiling
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcPartitionCommute

/-! # MODE-COMMUTE — the crossing box arm is ACTIVELY WRONG, not merely blind (the deepened arity wall)

`ArcPeelSignatureCeiling` established the arc peel's ARITY CEILING: the cup/cap EVENT stream the peel
dispatches on is BLIND to a `2⇒2` crossing (`crossAtom_stepArcAtom_recordsNoCupEvent` / `_recordsNoCapEvent`,
both `rfl` — the box arm leaves the event lists untouched), and the toy `crossModeSignature` carries a concrete
non-cup/cap generator (`crossAtom_isNotCupOrCap`).  That is a BLINDNESS claim: the crossing produces no arc
event, so the peel's four cup/cap builders never fire on it.

This file DEEPENS that wall from blindness to CORRUPTION.  `stepArcAtom`'s generic box arm (the catch-all for
any arity that is neither `0⇒2` nor `2⇒0`) does not merely forget a `2⇒2` crossing — it returns a STRUCTURALLY
WRONG state:

  ★ **Wire width is corrupted.**  The box arm's dropped-wire fold is
    `Nat.rec state.openWires (fun _ shorter => natListRemoveTwoAt shorter position) numConsumed`, which for
    `numConsumed = 2` removes TWO wires TWICE = FOUR wires, then splices in only `numProduced = 2` fresh ones.
    On the width-4 probe state `[10, 11, 12, 13]` the crossing collapses the open wires to `[20, 21]`
    (`crossAtom_stepArcAtom_openWires_isFreshPair`) — width `4 ⇒ 2`, a deficit of exactly `2`
    (`crossAtom_stepArcAtom_openWires_widthDeficit`).  A FAITHFUL `2⇒2` crossing consumes 2 and produces 2, so
    it PRESERVES width; the box arm loses two wires.
  ★ **The forest is bypassed.**  The box arm sets `links := state.links` unconditionally
    (`crossAtom_stepArcAtom_links_untouched`, general state) — it performs NO `unionFindJoin`.  So the two fresh
    outputs (`nextFresh`, `nextFresh + 1`, via `crossAtom_stepArcAtom_nextFresh_bump`) are DISCONNECTED ids that
    do not appear in any component: a crossing is supposed to PERMUTE its two input strands' connectivity, and
    the box arm connects nothing at all.

So the arity-lock is a SOUNDNESS guard, not a convenience: were the box arm reached at the walking-adjunction
seed it would return a wrong extract, not just a lossy one.  It is not reached only because every adjunction
spine atom is a cup or a cap (`adjunctionAtom_hasCupOrCapArity`, re-exported by the ceiling), so the peel's
four builders `arcSwapCorePackage_{cupCup, cupCap, capCup, capCap}` are exhaustive THERE.  The crossing fails
the very premise the peel's `consCongr` tracking step demands (`AtomHasCupOrCapArity`,
`crossAtom_failsTracksBoundaryPremise`).

## What this file does NOT do

It does NOT extend the peel to crossings and it does NOT flip the general-signature keystone.  A crossing's
correct home is the Brauer `stepWiring` / `WiringDesc` engine (which faithfully models crossings); the arc
engine is INTENTIONALLY cup/cap-locked.  The general-signature peel `ArcGodementSamePartitionFresh signature`
stays the open keystone (`fxMode_hasArcGodementSamePartitionFreshProof` = the #2043 / WP-AMALG amalgam
residual), pinned `false` here, and `fxMode_hasArcPeelGeneralSignature` stays `false`.  This certificate is
ADDITIVE: it sharpens the ceiling's characterization, it does not close the residual.

Raw Lean 4 + Init; the concrete facts are `rfl` on the width-4 probe state and the general-state facts are
`rfl` because the box arm's `links` / `nextFresh` fields do not depend on the state's contents (the match
reduces on `crossAtom`'s concrete `2⇒2` arities).  Per-declaration `#assert_no_axioms` gated in the audit
twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## A concrete width-4 probe state exercising the box arm -/

/-- A concrete arc state: four open wires, one forest edge (`11 -> 10`), fresh slack at `20`, prior cup/cap
events.  `crossAtom` fires at position `leftContext.length = 0`, so its box arm acts at the front. -/
def crossingBoxProbeState : ArcWireState :=
  { openWires := [10, 11, 12, 13],
    links := [(11, 10)],
    nextFresh := 20,
    loops := 0,
    cupEventNodes := [7],
    capEventNodes := [8] }

/-! ## Wire width is corrupted -/

/-- ★ **The crossing collapses four open wires to two fresh disconnected ids.**  On the width-4 probe state the
box arm removes four wires (two `natListRemoveTwoAt` passes, one per `numConsumed`) and splices in the two fresh
outputs `[nextFresh, nextFresh + 1] = [20, 21]` — the original `[10, 11, 12, 13]` are gone, replaced by ids that
enter no component.  `rfl` (the box arm computes on the concrete state). -/
theorem crossAtom_stepArcAtom_openWires_isFreshPair :
    (stepArcAtom crossingBoxProbeState crossAtom).openWires = [20, 21] := rfl

/-- ★ **Width `4 ⇒ 2`: a deficit of exactly two.**  The open-wire count AFTER the crossing plus `2` equals the
count BEFORE — the box arm loses two wires on a `2⇒2` generator.  A faithful crossing consumes two and produces
two, PRESERVING width; the box arm's `numConsumed`-fold removes twice as many as it should.  `rfl`. -/
theorem crossAtom_stepArcAtom_openWires_widthDeficit :
    (stepArcAtom crossingBoxProbeState crossAtom).openWires.length + 2
      = crossingBoxProbeState.openWires.length := rfl

/-! ## The forest is bypassed -/

/-- ★ **The crossing performs NO union-find join** — for EVERY state the box arm copies `links` verbatim, so it
never connects the strands it is meant to permute.  General-state `rfl` (the box-arm `links` field is literally
`state.links`, independent of the state's contents).  Contrast cup/cap, which always `unionFindJoin`. -/
theorem crossAtom_stepArcAtom_links_untouched (state : ArcWireState) :
    (stepArcAtom state crossAtom).links = state.links := rfl

/-- ★ **The two crossing outputs are freshly allocated** — `nextFresh` advances by `numProduced = 2`, so the
outputs are `nextFresh` and `nextFresh + 1`.  Together with `crossAtom_stepArcAtom_links_untouched`, this
witnesses that the outputs are DISCONNECTED: fresh ids absent from the (unchanged) forest.  General-state
`rfl`. -/
theorem crossAtom_stepArcAtom_nextFresh_bump (state : ArcWireState) :
    (stepArcAtom state crossAtom).nextFresh = state.nextFresh + 2 := rfl

/-! ## The crossing fails the peel's tracking-law premise -/

/-- The crossing fails the cup/cap arity premise (`AtomHasCupOrCapArity`) that the peel's `consCongr` boundary-
tracking step requires — restated from the ceiling's `crossAtom_isNotCupOrCap` under the name that ties it to
the exact peel obligation.  This is the SECOND independent hole (beyond the swap dispatcher's missing `2⇒2`
arm): even a non-swap congruence step through a crossing has no tracking instance, because the box arm's width
corruption is exactly what the arity-gated tracking law rules out. -/
theorem crossAtom_failsTracksBoundaryPremise : ¬ AtomHasCupOrCapArity crossAtom :=
  crossAtom_isNotCupOrCap

/-! ## Honesty markers -/

/-- **Honesty marker — the crossing box arm is ACTIVELY WRONG (machine-witnessed).**  On the width-4 probe state
the box arm corrupts wire width (`crossAtom_stepArcAtom_openWires_widthDeficit`, `4 ⇒ 2`) and returns two fresh
disconnected ids (`crossAtom_stepArcAtom_openWires_isFreshPair`), while bypassing the union-find forest for
EVERY state (`crossAtom_stepArcAtom_links_untouched`).  So the arc peel's cup/cap arity-lock is a SOUNDNESS
guard: a `2⇒2` crossing on the box arm would produce a wrong extract, not merely a lossy one — the ceiling's
blindness claim SHARPENED to corruption.  `= true`. -/
def fxMode_hasArcCrossingBoxArmCorruption : Bool := true

/-- **Honesty pin — the general-signature peel stays the open keystone.**  This additive corruption certificate
does NOT extend the adjunction-hardcoded peel to crossings; a crossing's faithful home is the Brauer
`stepWiring` engine, not this cup/cap-locked arc engine.  `fxMode_hasArcPeelGeneralSignature` stays `false`.
`rfl`. -/
theorem arcCrossing_generalSignature_stays_false :
    fxMode_hasArcPeelGeneralSignature = false := rfl

/-- **Honesty pin — the #2043 / WP-AMALG fresh-partition keystone is untouched.**  The general-signature peel is
exactly `ArcGodementSamePartitionFresh signature`, whose crossing content lives in the Brauer engine; deepening
the wall does not advance it.  `fxMode_hasArcGodementSamePartitionFreshProof` stays `false`.  `rfl`. -/
theorem arcCrossing_samePartitionFreshProof_stays_false :
    fxMode_hasArcGodementSamePartitionFreshProof = false := rfl

end FX1Poly.Polygraph
