import FX1Poly.Polygraph.Omega.InvolutionDemonstrator

/-! # Polygraph/Omega/InvolutionSquierBasis — the walking-involution homotopy-basis scope
(OMEGA-4 r2, B2)

★ **The involution coherence at the STRONGEST HONEST scope — and the corrected feasibility call.**
The recon proposed "Route A": push the abstract `FX1Poly.Core.SquierDiamond.coherence`
(convergent-implies-coherent-to-normal-form) through the r2 functor to land a full machine-checked
Squier coherent presentation for the walking involution.  On close reading that route is WALLED, and
this file records the wall precisely, ships the genuine fragment increment it CAN reach, and hands the
full basis to OMEGA-5.

## Why Route A is walled (the corrected feasibility assessment)

`SquierDiamond.coherence` requires a `SquierDiamond dp` — the STRONG single-step diamond: for EVERY pair
of coinitial steps `leftStep : Step source left`, `rightStep : Step source right` it demands an apex and
SINGLE-STEP residuals `joinLeft : Step left apex`, `joinRight : Step right apex`.  For a system with a
REACHABLE normal form (the involution's `s` / `id`, which have no outgoing step) this is impossible: a
coinitial peak whose reducts are already normal forms has no single-step residual out of them, so no
total `SquierDiamond` with reachable normal forms exists.  Hence `coherence` is VACUOUS for the
involution (its hypothesis `isNormalForm` is unsatisfiable for any reachable target under a diamond that
exists).  This is exactly the WF-coherent-Newman wall the `SquierCoherence` docstring itself names: a
non-vacuous coherence-to-normal-form needs PATH residuals (`nil` for reflexive peaks) plus termination,
i.e. `WellFounded.fix`, which leaks `propext` / `Quot.sound` in this Init-only zero-axiom setting.  So
the r2 functor cannot transport an involution coherence-to-NF — there is no `SquierConfluence` DATA for
the involution to feed it.  The recon's Route A prize is NOT in reach this round.

## The genuine fragment increment r2 DOES ship (native, over the involution computad)

  * **`involutionSssLegsIdentifiedInEveryModel`** (★, NEW) — the least-congruence universal property for
    the involution: the single generating 3-cell `involutionSssThreeCell` forces the two `sss` legs to be
    identified in EVERY congruence absorbing the involution base relation (via
    `SaturatedConvOverWithId.recInto`).  So the one 3-cell GENERATES the dim-3 identification of the
    critical pair — the map-out characterization r1 did not state.
  * **`InvolutionCoherentResolution` / `involutionCriticalPairResolved`** (★, NEW) — the r1 pieces
    (peak-join by associativity, the generating 3-cell, valley-join by the two units) ASSEMBLED into one
    coherent-resolution datum: the sole critical pair is joinable-modulo-strict as a SINGLE bundled
    witness (peak convertible, legs convertible, valleys convertible), not three loose facts.

## The scope stays HONEST (r1's walls re-affirmed, refined)

Literal globularity still fails (`involutionLegs_notLiterallyParallel`, r1): the legs are parallel only
modulo the strict congruence, so the resolution is joinable-modulo-strict, never a literally-globular
3-cell — the common valley `s` is reached at the 1-cell boundary (units), and there is no unit 2-cell to
compose the legs down to a literal common valley cell.  The FULL homotopy basis (every parallel
2-path `s^n => s^k` homotopic) still needs a 2-path normalizer one dimension up
(`conv_toParityNF`-analogue at the 2-path level) — the OMEGA-5 handoff, unchanged.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

/-! ## The least-congruence universal property for the involution's single 3-cell -/

/-- ★ **The single 3-cell GENERATES the identification (least-congruence UP).**  For any relation
`targetRel` that absorbs the involution base relation (a congruence containing the strict laws and the
`sss` critical-pair row), the two `sss` legs are `targetRel`-related — so `involutionSssThreeCell` is the
generating datum whose fold through `SaturatedConvOverWithId.recInto` identifies the legs in EVERY model.
The map-out characterization of the involution's dim-3 content. -/
theorem involutionSssLegsIdentifiedInEveryModel {targetRel : CellRelOver involutionOmegaComputad}
    (absorbs : IsSaturatedCongruenceWithId involutionOmegaComputad involutionBaseRel targetRel) :
    targetRel involutionLeftLeg involutionRightLeg :=
  SaturatedConvOverWithId.recInto absorbs involutionSssThreeCell

/-! ## The coherent resolution of the sole critical pair (assembled) -/

/-- ★ A **coherent resolution** of the involution's sole critical pair, joinable MODULO the strict
congruence: the two peak spellings are convertible, the two legs are convertible, and the two valley
spellings are convertible.  The three r1 facts bundled into one datum (a `Prop`, since every field is a
`SaturatedConvOverWithId` convertibility). -/
structure InvolutionCoherentResolution : Prop where
  /-- The two leg SOURCES (`(ss)s` and `s(ss)`) are convertible (associativity). -/
  peakJoined : SaturatedConvOverWithId involutionOmegaComputad involutionBaseRel
    (boundarySource involutionLeftLeg) (boundarySource involutionRightLeg)
  /-- The two legs are convertible (the generating 3-cell). -/
  legsConvertible : SaturatedConvOverWithId involutionOmegaComputad involutionBaseRel
    involutionLeftLeg involutionRightLeg
  /-- The two leg TARGETS (`(id)s` and `s(id)`) are convertible through the common valley `s` (units). -/
  valleyJoined : SaturatedConvOverWithId involutionOmegaComputad involutionBaseRel
    (boundaryTarget involutionLeftLeg) (boundaryTarget involutionRightLeg)

/-- ★ **THE SOLE CRITICAL PAIR IS COHERENTLY RESOLVED (modulo strict).**  The r1 peak-join, generating
3-cell, and valley-join assembled into one `InvolutionCoherentResolution` — the walking involution's
homotopy basis at the honest fragment scope: ONE generating 3-cell, joinable-modulo-strict. -/
theorem involutionCriticalPairResolved : InvolutionCoherentResolution :=
  ⟨involutionPeakJoin, involutionSssThreeCell, involutionValleyJoin⟩

/-! ## The honesty markers -/

/-- ★ **WALL (corrected feasibility) — the recon's Route A is NOT reached.**  `= false` records that the
full Squier coherent presentation for the involution via `SquierDiamond.coherence` is out of reach: the
STRONG single-step `SquierDiamond` (total single-step residuals over all coinitial peaks) is incompatible
with reachable normal forms, so `coherence` is vacuous for the involution and no `SquierConfluence` DATA
exists to feed the r2 functor.  Non-vacuous coherence-to-NF is the WF-coherent-Newman argument, whose
`WellFounded.fix` leaks `propext` / `Quot.sound` in this zero-axiom setting.  Blocking node: a
`SquierDiamond`-with-PATH-residuals + termination (or a strict-quotient carrier making the legs literally
parallel — either changes the presentation). -/
def fxOmega4_involutionRouteAStrongDiamondWallR2 : Bool := false

/-- ★ **B2 FRAGMENT SHIPPED.**  `= true` records the genuine r2 increment over the involution
demonstrator: the least-congruence universal property `involutionSssLegsIdentifiedInEveryModel` (the
single 3-cell generates the identification in every model) and the assembled coherent resolution
`involutionCriticalPairResolved` (peak / legs / valley convertible, joinable-modulo-strict).  The scope
is HONEST: literal globularity fails (r1), the resolution is modulo strict, and the FULL homotopy basis
stays the OMEGA-5 handoff. -/
def fxOmega4_involutionSquierBasisFragmentShippedR2 : Bool := true

end FX1Poly.Polygraph.Omega
