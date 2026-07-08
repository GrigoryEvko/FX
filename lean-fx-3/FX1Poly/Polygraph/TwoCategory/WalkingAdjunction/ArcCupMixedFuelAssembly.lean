import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupMixedReselectionReduction
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupOrbitGateReduction

/-! # ArcCupMixedFuelAssembly — the mixed peel-and-recurse LANDS `MixedTailArcCompleteness`

Round 3 of the flag-B census-inversion campaign closes the fuel assembly `(b)` and resolves the
misframed `(a)` the honest way.  The FM (Forest–Mimram, arXiv:2109.05369, §4.2) peel-and-recurse is a
STRUCTURAL recursion over the first spine list: at each step locate the head event in the second spine,
peel it (a realized trace-equivalence bubble), and recurse on the strictly shorter tail at the head's
moved target boundary.  That recursion is already shipped as `spineTraceMatched_of_chainedHeadExtraction`
(`ArcChainedExtraction.lean`) — plain `induction firstList`, the width measure implicit in the list's
length, no `WellFounded.fix`.  This brick re-targets that assembly at the unified list-level completeness
`MixedTailArcCompleteness` (the target both shipped pure fronts and the open mixed interior factor through,
`ArcCupMixedReselectionReduction.lean`):

  * ★ `mixedTailArcCompleteness_ofChainedExtraction` — `MixedTailArcCompleteness` FOLLOWS from the
    per-boundary chained head extraction (`SpineArcHeadExtractionChained` at every boundary).  This IS the
    fuel peel-and-recurse `(b)`, stated as completeness of the arc invariant: the shipped structural
    recursion peels the head, `spineArcNilInversion_adjunction` closes the empty base, and
    `spineTraceEquiv_of_traceMatched` crosses the assembled matching to a `SpineTraceEquiv`.  The positive
    seed hypothesis of `MixedTailArcCompleteness` is not even consumed — the arc invariant is complete on
    any boundary-chained pair.

  * ★ `mixedTailArcCompleteness_ofOrbitWitness` — `MixedTailArcCompleteness` FOLLOWS from the general
    (mixed cup/cap) cup orbit witness `ArcCupOrbitWitness`.  The arity dispatch
    (`spineArcHeadExtractionChained_ofArityDispatch`) splits each head by its cup/cap arity: the CAP branch
    is the shipped HEAD-FIRST discharge `spineArcHeadExtractionChained_ofCapArity` (mixed-general, needs
    nothing new), the CUP branch is the orbit witness via
    `spineArcHeadExtractionChained_cupCase_ofOrbitWitness`.  So the mixed list-level completeness rests on
    EXACTLY the general cup orbit witness — the SAME single residual as the cell reconstruction
    (`adjunctionArcCellReconstruction_ofOrbitWitness`).

## Why there is no `dropLastCap_arc_injective` (the `(a)` correction)

The round-3 framing asked for a `dropLastCap_arc_injective` dual of `dropLastCup_arc_injective`
(`ArcCupStepDrop.lean`), peeling the LAST cap.  That mirror is genuinely blocked and, more importantly,
OFF-PATH.  Blocked: the cup lemma inverts each `extractArc` field through an INSERT splice
(`internalCupCounts_stepCupArc` splices a fresh `[1,1]`, `natListInsertAt` is left-injective); a cap
INSTEAD reads two existing adjacent ports, unions them, and REMOVES them (`natListRemoveTwoAt`), which is
not left-invertible without the removed content, and no cap arc-splice suite (`internalCupCounts_stepCapArc`
&c.) exists — a cap leaves no fresh `[1,1]` census window, so it is not last-locatable by census.  Off-path:
the peel-and-recurse fires from the FRONT (head of the first list), and the cap head is already discharged
HEAD-FIRST by the shipped mixed-general `spineArcHeadExtractionChained_ofCapArity` (locate by a HEAD-anchored
cap window, bubble to front, cancel).  So the cap side of the fuel assembly needs NOTHING — that is exactly
why `mixedTailArcCompleteness_ofOrbitWitness` bottoms out on the cup orbit witness ALONE.  The honest cap
peel is head-first, not peel-last; `dropLastCap_arc_injective` is not built.

## The exact remaining residual (round 4)

Neither brick flips the gate.  The sole open leaf is the GENERAL (mixed cup/cap) `ArcCupOrbitWitness
headAtom tailList secondList` for an ARBITRARY second spine — equivalently `arcCupReselection_exists`.
Its front-head instance is shipped (`arcCupOrbitWitness_ofFrontHead`); the gap general-vs-front is the
locate-and-bubble of the head's cup across a mixed prefix, with two sub-cruxes:

  1. the mixed `locateAux` — bubbling the census-located cup (r2 locator
     `generalStateCupInternalCupCount_atLeftLeg`/`_atRightLeg`) to the front across a mixed cup/cap prefix,
     driven by the shipped cross-swap arc simulations (`ArcCupCupSwapSimulation` /
     `ArcCupCapSwapSimulation` / `ArcCapCupSwapSimulation`);
  2. the interacting gap-0/1 zigzag — a cap touching the located cup's legs cancels via the snake
     (FM Lemma 4.2.1 `N`/`N̄`, the two triangle identities), a DIFFERENT mechanism from the census read-off,
     with the FM Prop 4.2.4 offset case-split: gap `>= 2` interchange, gap `= 1` snake-cancel, gap `= 0`
     impossible by the `f * g != g * f` parity obstruction.

`fxMode_hasArcStructureReconstruction` stays `false` until that witness discharges.

Raw Lean 4 + Init; STRUCTURAL (the shipped list recursion), zero-axiom; per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The fuel peel-and-recurse, landing the unified completeness -/

/-- ★ **The mixed peel-and-recurse lands `MixedTailArcCompleteness`.**  Granted the per-boundary chained
head extraction (`SpineArcHeadExtractionChained` at every running boundary), the completeness of the arc
invariant follows: the shipped structural recursion `spineTraceMatched_of_chainedHeadExtraction` peels the
head of the first list, recurses on the strictly shorter tail at the head's moved target boundary, closes
the empty base by `spineArcNilInversion_adjunction`, and `spineTraceEquiv_of_traceMatched` crosses the
assembled head-extraction matching to a genuine `SpineTraceEquiv`.  This is the fuel assembly `(b)` — the
FM width recursion, with the width implicit in the list length (a structural `induction`, no
`WellFounded.fix`).  The positive-seed hypothesis of `MixedTailArcCompleteness` is discarded: the arc
invariant is complete on ANY boundary-chained pair. -/
theorem mixedTailArcCompleteness_ofChainedExtraction
    (chainedExtraction : ∀ {sourceMode targetMode : adjunctionGraph.Mode} (bottomCount : Nat),
      SpineArcHeadExtractionChained adjunctionModeSignature
        (overallSource := sourceMode) (overallTarget := targetMode) bottomCount) :
    MixedTailArcCompleteness := by
  intro overallSource overallTarget bottomCount firstList secondList
    firstChained secondChained _positiveWidth arcEqual
  exact spineTraceEquiv_of_traceMatched
    (spineTraceMatched_of_chainedHeadExtraction
      (fun boundaryCount => chainedExtraction boundaryCount)
      (fun boundaryCount => spineArcNilInversion_adjunction boundaryCount)
      firstChained secondChained arcEqual)

/-! ## The completeness from the general cup orbit witness -/

/-- ★ **`MixedTailArcCompleteness` from the general cup orbit witness.**  Granted, for every cup-headed /
arc-equal / boundary-chained configuration, the general `ArcCupOrbitWitness headAtom tailList secondList`
(arbitrary second spine), the unified list-level completeness follows: the arity dispatch
(`spineArcHeadExtractionChained_ofArityDispatch`) routes the cap branch to the shipped HEAD-FIRST
`spineArcHeadExtractionChained_ofCapArity` (mixed-general — the cap side needs nothing, no
`dropLastCap_arc_injective`) and the cup branch to `spineArcHeadExtractionChained_cupCase_ofOrbitWitness`
fed by the orbit witness, then `mixedTailArcCompleteness_ofChainedExtraction` runs the peel-and-recurse.

So the mixed list-level completeness rests on EXACTLY the general cup orbit witness — the same single
residual as the cell reconstruction (`adjunctionArcCellReconstruction_ofOrbitWitness`).  Combined with the
shipped converse `arcCupOrbitWitness_ofFrontHead_ofCompleteness` (completeness gives the FRONT-head witness),
this pins the open leaf precisely: the gap between the general and the front-head orbit witness — the
locate-and-bubble of the head's cup across a mixed prefix (`arcCupReselection_exists`). -/
theorem mixedTailArcCompleteness_ofOrbitWitness
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
    MixedTailArcCompleteness :=
  mixedTailArcCompleteness_ofChainedExtraction
    (fun {_sourceMode _targetMode} bottomCount =>
      spineArcHeadExtractionChained_ofArityDispatch bottomCount
        (fun headAtom domPin codPin tailList secondList firstChained secondChained arcEqual =>
          spineArcHeadExtractionChained_cupCase_ofOrbitWitness bottomCount headAtom domPin codPin
            tailList secondList firstChained secondChained
            (orbitWitness bottomCount headAtom domPin codPin tailList secondList
              firstChained secondChained arcEqual)))

/-! ## Honesty marker -/

/-- **Honesty marker — the mixed fuel assembly LANDS `MixedTailArcCompleteness` on one residual.**
`mixedTailArcCompleteness_ofChainedExtraction` runs the shipped STRUCTURAL peel-and-recurse
(`spineTraceMatched_of_chainedHeadExtraction`, `induction firstList`, no `WellFounded.fix`) to land the
unified completeness from the per-boundary chained head extraction — the fuel assembly `(b)`.
`mixedTailArcCompleteness_ofOrbitWitness` composes the arity dispatch (CAP branch = shipped HEAD-FIRST
`spineArcHeadExtractionChained_ofCapArity`, mixed-general; CUP branch = the orbit witness), so the mixed
list-level completeness rests on EXACTLY the general cup orbit witness — the same single residual as the
cell reconstruction.

The `(a)` correction: there is NO `dropLastCap_arc_injective`.  The cup lemma inverts each `extractArc`
field through an INSERT splice (`natListInsertAt` left-injective); a cap REMOVES ports
(`natListRemoveTwoAt`, not left-invertible) and no cap arc-splice suite exists, so a last cap is not
census-locatable.  It is also off-path: the peel fires from the FRONT and the cap head is already
discharged head-first, so the cap side needs nothing.

What this marker does NOT claim: the general (mixed cup/cap) `ArcCupOrbitWitness` for an arbitrary second
spine (`arcCupReselection_exists`) — the sole open leaf.  Its front-head instance is shipped
(`arcCupOrbitWitness_ofFrontHead`); round 4 owns the general-vs-front gap: the mixed `locateAux`
(bubble the census-located cup to front across a mixed prefix via the shipped cross-swap simulations) and
the interacting gap-0/1 zigzag (FM Lemma 4.2.1 snake / Prop 4.2.4 offset case-split).  No gate flip;
`fxMode_hasArcStructureReconstruction` stays as is.  `= true`. -/
def fxMode_hasArcCupMixedFuelAssembly : Bool := true

end FX1Poly.Polygraph
