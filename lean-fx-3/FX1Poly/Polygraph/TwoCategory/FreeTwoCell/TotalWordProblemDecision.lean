import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.AtomUniverse
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.BoundedListEnumeration
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.FrontExtraction
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SaturationFuelBound
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.TwoCellWordProblemDecision

/-! # TotalWordProblemDecision — the fuel gate falls (FREE-7 capstone)

The BOUNDED-ATOM-UNIVERSE route assembles: a boundary-chained seed's whole
equivalence class lives inside a COMPUTABLE list — all lists of the seed's length
(`FrontExtraction.AtomicTraceEquiv.lengthEq`) over the seed's finite atom universe
(`memberAtom_mem_atomUniverse`) — and a complete class list un-gates the saturation
decider (`decideAtomicTraceEquivOfCompleteClassList`).  Every free cell's spine IS
chained at its source boundary (`spineBoundaryChained_spineDiff` at empty whisker
accumulators), so the free 2-cell word problem is decided TOTALLY: no fuel
hypothesis, no `Option`, no exhaustion gate.

  * `chainedSeedClassList` — the computable candidate class list of a seed;
  * `chainedSeedClassList_isComplete` — every class member is in it (legs B–E4
    composed with the length invariance);
  * ★ `decideAtomicTraceEquivOfChainedSeed` — unconditional `Decidable` trace
    equivalence for boundary-chained seeds;
  * `RawTwoCellExpr.spine_isBoundaryChained` — every cell's spine is chained;
  * ★★ `decideTwoCellConvFull` — **the total front door**: `Decidable
    (TwoCellConvFull signature cellFirst cellSecond)` over ANY mode signature with
    decidable-equality data, outright.

HONESTY: this is the FREE case (no presentation relations) — the already-true
`fxMode_hasDecidableFreeTwoCellEquality` marker's fuel-gate caveat is hereby
discharged; the general `fxMode_hasDecidableTwoCellEquality` (relations, ungated)
stays `false` for the saturated walking-adjunction arc.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The computable class list of a chained seed -/

/-- The candidate class list: all traces of the seed's length over the seed's finite
atom universe. -/
def chainedSeedClassList {signature : ModeSignature}
    (modeDecEq : DecidableEq signature.graph.Mode)
    {overallSource overallTarget : signature.graph.Mode}
    (boundaryLength : Nat)
    (seedTrace : List (SpineAtom signature overallSource overallTarget)) :
    List (List (SpineAtom signature overallSource overallTarget)) :=
  allListsOfLength seedTrace.length
    (atomUniverse modeDecEq (traceLetterInventory seedTrace)
      (boundaryLength + traceGrowthBudget seedTrace) overallSource overallTarget
      (spinePackedGenerators seedTrace))

/-- ★ **The candidate class list is complete**: every class member's atoms live in the
seed's universe and its length is the seed's, so it is enumerated. -/
theorem chainedSeedClassList_isComplete {signature : ModeSignature}
    (modeDecEq : DecidableEq signature.graph.Mode)
    {overallSource overallTarget : signature.graph.Mode}
    {boundaryLength : Nat}
    {seedTrace : List (SpineAtom signature overallSource overallTarget)}
    (seedChained : SpineBoundaryChained boundaryLength seedTrace) :
    ∀ member, AtomicTraceEquiv signature seedTrace member →
      member ∈ chainedSeedClassList modeDecEq boundaryLength seedTrace :=
  fun member traceEquiv =>
    allListsOfLength_containsList member
      (fun _atom atomMem =>
        memberAtom_mem_atomUniverse modeDecEq traceEquiv seedChained atomMem)
      seedTrace.length traceEquiv.lengthEq.symm

/-! ## ★ The un-gated trace decision -/

/-- ★ **Trace equivalence at a chained seed is decidable outright** — the complete
class list computes the saturation fuel, no exhaustion hypothesis. -/
def decideAtomicTraceEquivOfChainedSeed {signature : ModeSignature}
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    (twoCellDecEq : {sourceMode targetMode : signature.graph.Mode} →
      (sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode) →
      DecidableEq (signature.twoCell sourcePath targetPath))
    {overallSource overallTarget : signature.graph.Mode}
    (seedTrace target : List (SpineAtom signature overallSource overallTarget))
    {boundaryLength : Nat}
    (seedChained : SpineBoundaryChained boundaryLength seedTrace) :
    Decidable (AtomicTraceEquiv signature seedTrace target) :=
  decideAtomicTraceEquivOfCompleteClassList modeDecEq modalityDecEq twoCellDecEq
    seedTrace target (chainedSeedClassList modeDecEq boundaryLength seedTrace)
    (chainedSeedClassList_isComplete modeDecEq seedChained)

/-! ## Every cell's spine is chained -/

/-- A free cell's spine is boundary-chained at its source 1-cell's length (the
difference-list chain lemma at empty whisker accumulators). -/
theorem RawTwoCellExpr.spine_isBoundaryChained {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (cell : RawTwoCellExpr signature sourcePath targetPath) :
    SpineBoundaryChained sourcePath.length cell.spine := by
  have chainedPadded : SpineBoundaryChained (0 + sourcePath.length + 0) cell.spine :=
    spineBoundaryChained_spineDiff (identityPath sourceMode)
      (identityPath targetMode) cell [] (SpineBoundaryChained.nil _)
  rw [Nat.add_zero, Nat.zero_add] at chainedPadded
  exact chainedPadded

/-! ## ★★ The total front door -/

/-- ★★ **The FREE 2-cell word problem is decided TOTALLY**: equality of parallel free
2-cells modulo the Godement/whisker congruence, over ANY mode signature with
decidable-equality data — no fuel, no `Option`, no gate.  The first cell's spine is
chained, its class list is complete, the saturation terminates inside it. -/
def decideTwoCellConvFull {signature : ModeSignature}
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    (twoCellDecEq : {sourceMode targetMode : signature.graph.Mode} →
      (sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode) →
      DecidableEq (signature.twoCell sourcePath targetPath))
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (cellFirst cellSecond : RawTwoCellExpr signature sourcePath targetPath) :
    Decidable (TwoCellConvFull signature cellFirst cellSecond) :=
  match decideAtomicTraceEquivOfChainedSeed modeDecEq modalityDecEq twoCellDecEq
      cellFirst.spine cellSecond.spine cellFirst.spine_isBoundaryChained with
  | Decidable.isTrue atomicEquiv =>
      Decidable.isTrue
        ((twoCellConvFull_iff_atomicTraceEquiv cellFirst cellSecond).mpr atomicEquiv)
  | Decidable.isFalse atomicRefuted =>
      Decidable.isFalse (fun cellsConv =>
        atomicRefuted
          ((twoCellConvFull_iff_atomicTraceEquiv cellFirst cellSecond).mp cellsConv))

/-! ## Honesty marker — the fuel gate falls -/

/-- **★ ESTABLISHED (FREE-7 capstone) — the FREE 2-cell decision is UN-GATED.**  The
class-size fuel the ledger docstring once owed is DISCHARGED, not by the hypothesized
`length!` permutation pigeonhole, but by the equivalent-and-total bounded-atom-universe
route: a chained seed's whole `AtomicTraceEquiv` class lives inside the computable list
`chainedSeedClassList` (`chainedSeedClassList_isComplete`), and a complete class list
makes the saturation frontier provably exhaust within the computed fuel
`classSaturationFuel` (the stabilization theorem `didExhaustFrontier_ofCompleteClassList`,
itself the strict-potential-descent argument `saturationPotentialStep`).  Assembled, this
un-gates the decider: `decideTwoCellConvFull` is total `Decidable (TwoCellConvFull …)`
over ANY mode signature with decidable-equality data — no fuel hypothesis, no `Option`,
no exhaustion gate.  Backs the ledger's now-`false` `isFreeDecisionFuelGated`.  `= true`.
(The GENERAL `fxMode_hasDecidableTwoCellEquality` — presentation relations, cross-signature
— stays `false`: that is the saturated walking-adjunction arc and the rung-3 wall, not the
free fuel.) -/
def fxMode_hasUngatedFreeTwoCellDecision : Bool := true

end FX1Poly.Polygraph
