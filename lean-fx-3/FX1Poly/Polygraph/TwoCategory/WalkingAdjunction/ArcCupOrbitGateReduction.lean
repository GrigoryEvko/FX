import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcHeadExtractionArityDispatch
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupCaseOrbitReduction

/-! # ArcCupOrbitGateReduction — the gate reduces to EXACTLY the general orbit witness

The whole walking-adjunction cell reconstruction is already a chain of shipped, green reductions:

  * `adjunctionArcCellReconstruction_ofCupExtraction` (`ArcHeadExtractionArityDispatch.lean:67`) —
    `ArcCellReconstruction adjunctionModeSignature` FOLLOWS from the cup-arity head extraction (the
    matchedRemainder conclusion) at every boundary; the cap branch is discharged (shipped);
  * `spineArcHeadExtractionChained_cupCase_ofOrbitWitness` (`ArcCupCaseOrbitReduction.lean:57`) —
    the cup case's matchedRemainder conclusion FOLLOWS from ONE `ArcCupOrbitWitness`.

This brick COMPOSES the two into a single named reduction: `ArcCellReconstruction
adjunctionModeSignature` follows from producing, for EVERY cup-headed / arc-equal / boundary-chained
configuration, the general `ArcCupOrbitWitness headAtom tailList secondList`.  After this brick the
ENTIRE gate `fxMode_hasArcCellReconstruction` (and hence the parent
`fxMode_hasArcStructureReconstruction`) rests on exactly ONE grep-able proposition — the general
(mixed cup/cap) orbit witness — with nothing else in between.

The general orbit witness is the genuine Joyal-Street planar residual.  It is DISCHARGED on the
pure-cup base fragment (`arcCupOrbitWitness_ofFrontHead_pureCup`, cap-count `0`) but NOT on the
mixed cup/cap tail — the irreducible geometric core `arcCupReselection_exists` (the leg-aligned
re-selection, an `AtomicTraceEquiv` for a tail carrying caps).  The soundness direction is
shipped (`extractArc_eq_of_atomicTraceEquiv`: any atomic trace-equivalence gives equal arc
structure); the completeness direction (equal arc structure gives an atomic trace-equivalence) is
the open leaf, proven only pure-cup.  This brick does NOT claim the general witness — it names it.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The gate reduces to the general orbit witness.**  Granted, for every cup-headed spine with a
boundary-chained arc-equal second spine, the located-cup orbit witness `ArcCupOrbitWitness headAtom
tailList secondList`, the full `ArcCellReconstruction adjunctionModeSignature` follows: each cup case
is discharged by `spineArcHeadExtractionChained_cupCase_ofOrbitWitness` (the orbit witness carries
all five pins), and `adjunctionArcCellReconstruction_ofCupExtraction` fills the cap branch (shipped)
and lands the reconstruction.  This is the tightest reduction target: the whole walking-adjunction
cell reconstruction rests on exactly the general orbit witness — the Joyal-Street cup orbit, and
nothing else.  The mixed cup/cap instance of that witness is the sole open leaf. -/
theorem adjunctionArcCellReconstruction_ofOrbitWitness
    (orbitWitness :
      ∀ {sourceMode targetMode : adjunctionGraph.Mode} (bottomCount : Nat)
        (headAtom : SpineAtom adjunctionModeSignature sourceMode targetMode),
        headAtom.generatorDom.length = 0 → headAtom.generatorCod.length = 2 →
        ∀ (tailList secondList :
            List (SpineAtom adjunctionModeSignature sourceMode targetMode)),
          SpineBoundaryChained bottomCount (headAtom :: tailList) →
          SpineBoundaryChained bottomCount secondList →
          arcStructureOfSpineList bottomCount (headAtom :: tailList)
              = arcStructureOfSpineList bottomCount secondList →
          ArcCupOrbitWitness headAtom tailList secondList) :
    ArcCellReconstruction adjunctionModeSignature :=
  adjunctionArcCellReconstruction_ofCupExtraction
    (fun {_sourceMode _targetMode} bottomCount headAtom domPin codPin
        tailList secondList firstChained secondChained arcEqual =>
      spineArcHeadExtractionChained_cupCase_ofOrbitWitness bottomCount headAtom domPin codPin
        tailList secondList firstChained secondChained
        (orbitWitness bottomCount headAtom domPin codPin tailList secondList
          firstChained secondChained arcEqual))

/-! ## Honesty marker -/

/-- **Honesty marker — the gate rests on EXACTLY the general orbit witness.**
`adjunctionArcCellReconstruction_ofOrbitWitness` composes the shipped
`adjunctionArcCellReconstruction_ofCupExtraction` (cap branch discharged) with
`spineArcHeadExtractionChained_cupCase_ofOrbitWitness` (cup case from one witness), collapsing the
whole reduction chain: `ArcCellReconstruction adjunctionModeSignature` FOLLOWS from producing the
general `ArcCupOrbitWitness` for every cup-headed / arc-equal / boundary-chained configuration.  So
the entire `fxMode_hasArcCellReconstruction` residual is now ONE grep-able proposition.  What this
marker does NOT claim: the general witness itself (the mixed cup/cap leg-aligned re-selection
`arcCupReselection_exists` — DISCHARGED only on the pure-cup base fragment
`arcCupOrbitWitness_ofFrontHead_pureCup`, cap-count `0`; the mixed case is the irreducible open
geometric core) nor any gate flip.  `= true`. -/
def fxMode_hasArcCupOrbitGateReduction : Bool := true

end FX1Poly.Polygraph
