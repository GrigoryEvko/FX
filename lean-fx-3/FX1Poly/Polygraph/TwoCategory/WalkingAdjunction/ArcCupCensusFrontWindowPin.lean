import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupHeadFrontedReselection
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupMixedBubbleFront

/-! # ArcCupCensusFrontWindowPin — the fixed-length HEAD fronting from the census front + `windowPin`

Flag-B round 9 closes the fixed-length interchange fronting `(a)` to its honest residual.  R8
(`equalArcSpine_length_eq`) proved that equal arc structure FORCES equal spine length, so — with
`AtomicTraceEquiv` length-preserving (`SpineTraceEquiv.length_eq`) — the length-changing snake is FORMALLY
EXCLUDED from every re-selection instance.  Bringing the head cup to the front of `secondList` is therefore a
FIXED-LENGTH interchange insertion-sort, and it is ALREADY SHIPPED at the census-located granularity: the
mixed bubble `arcCupMixedFrontsCup_ofCupCountPos` (`ArcCupMixedBubbleFront.lean`) fronts a census-located cup
as a plain `AtomicTraceEquiv secondList (movedTarget :: movedRest)` — the interchanger sort of a located cup
to the front — over an arbitrary mixed cup/cap prefix, terminating by the cup's Nat position, no
`WellFounded.fix`.  The literature backs this exactly (Delpeuch–Vicary, arXiv:1804.07832, Theorem 3): two
morphism expressions denote the same morphism iff related by a series of EXCHANGES, and the exchanges only
swap heights (length-preserving); an interacting cup/cap sharing a wire simply does not exchange past its
partner (the "share no common edge" side-condition), so the fixed diagram forces exactly a Godement-reachable
permutation of the INDEPENDENT generators — no snake, no length change.

What the census front does NOT decide is WHICH cup it lands.  `arcCupMixedFrontsCup_ofCupCountPos` fronts SOME
cup; the cup-case conclusion (`cupHeadExtractionConclusion_ofFrontedHeadReselection`) needs the fronted cup to
BE the HEAD cup — i.e. `windowPin` (`movedTarget.leftContext.length = headAtom.leftContext.length`).  That is
the one datum the arc structure does NOT carry: `headCupWindowReadoff_isFalse` exhibits two boundary-chained,
cup-headed spines at boundary `2` whose head cups sit at DIFFERENT windows (`0` vs `2`) yet share the WHOLE
`FullArcStructure` (diagram, totals, AND `internalCupCounts`).  So the head-cup window is genuine trace-orbit
content, not an arc-field readoff.

This brick assembles the two shipped halves — the census front (the fixed-length interchange sort) and the
seed rigidity `frontCupToucher_eq_head_ofWindowPin` (a matched window forces the fronted cup to BE the head
atom) — into the fronting of the GENUINE head, and threads it into the swap-NF discharge:

  * ★ `cupHeadFronting_ofCensusFrontWindowPin` — the fixed-length fronting `(a)`: given a census front of a
    cup to the front of `secondList` and `windowPin`, the fronted cup IS the head atom, so `secondList` is
    `AtomicTraceEquiv` to `headAtom :: movedRest` — literally the fronting the swap-NF discharge consumes.
  * ★ `cupHeadExtractionConclusion_ofCensusFrontWindowPin` — the full cup-case head-extraction conclusion from
    the census front + `windowPin` + the tail reselection, via
    `cupHeadExtractionConclusion_ofFrontedHeadReselection`.  This collapses the entire fronting bookkeeping to
    TWO named residuals: `windowPin` (the fronted cup is the head — machine-refuted as a universal arc readoff,
    `headCupWindowReadoff_isFalse`) and the tail reselection (`AtomicTraceEquiv tailList movedRest`).

So round 9 lands `(a)` up to its single genuine wall: the fronting is CONSTRUCTED from the shipped
fixed-length interchange sort the moment `windowPin` is granted; the interacting cup/cap case is handled by
the interchange at fixed length (no snake); and the sole surviving datum is `windowPin` — genuine trace-orbit
content the census cannot read — plus the recursive tail reselection.  No gate flip:
`fxMode_hasArcStructureReconstruction` stays `false` until `windowPin` (equivalently the peel-LAST short-chord
route `mixedSpine_lastCup_isShortChord`, where the last cup's window IS arc-readable) discharges.

Raw Lean 4 + Init; STRUCTURAL (rides the shipped census bubble + seed rigidity — no recursion, pure
rewriting), zero-axiom; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The fixed-length HEAD fronting from the census front + `windowPin` -/

/-- ★ **The fixed-length fronting `(a)`: the census-fronted cup IS the head under `windowPin`.**  Given a
census front `AtomicTraceEquiv secondList (movedTarget :: movedRest)` (the shipped fixed-length interchange
sort of a located cup to the front, `arcCupMixedFrontsCup_ofCupCountPos`), where both the head atom and the
fronted cup fire at the running boundary `bottomCount` and are cups (dom arity `0`), a matched window
(`windowPin`) forces the fronted cup to BE the head atom (`frontCupToucher_eq_head_ofWindowPin`, seed
rigidity).  Rewriting through that atom equality turns the census front into the fronting of the GENUINE head:
`AtomicTraceEquiv secondList (headAtom :: movedRest)` — exactly the fronting the swap-NF cup-case discharge
consumes.  No bubble bookkeeping, no split; the length-changing snake never appears (`AtomicTraceEquiv` is
length-preserving, and R8 `equalArcSpine_length_eq` excludes it from the instance). -/
theorem cupHeadFronting_ofCensusFrontWindowPin (bottomCount : Nat)
    {overallSource overallTarget : adjunctionGraph.Mode}
    (headAtom movedTarget : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (secondList movedRest :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (censusFront : AtomicTraceEquiv adjunctionModeSignature secondList (movedTarget :: movedRest))
    (headFires : headAtom.domBoundaryLength = bottomCount)
    (movedFires : movedTarget.domBoundaryLength = bottomCount)
    (headCupDom : headAtom.generatorDom.length = 0)
    (movedCupDom : movedTarget.generatorDom.length = 0)
    (windowPin : movedTarget.leftContext.length = headAtom.leftContext.length) :
    AtomicTraceEquiv adjunctionModeSignature secondList (headAtom :: movedRest) := by
  have movedEqHead : movedTarget = headAtom :=
    frontCupToucher_eq_head_ofWindowPin bottomCount headAtom movedTarget
      headFires movedFires headCupDom movedCupDom windowPin
  rw [movedEqHead] at censusFront
  exact censusFront

/-! ## The full cup-case conclusion from the census front + `windowPin` + tail reselection -/

/-- ★ **The cup-case head extraction from the census front + `windowPin` + tail reselection.**  Assembles the
fixed-length fronting `(a)` (`cupHeadFronting_ofCensusFrontWindowPin`) with the shipped swap-NF discharge
`cupHeadExtractionConclusion_ofFrontedHeadReselection`.  The census front's chain
(`SpineBoundaryChained bottomCount (movedTarget :: movedRest)`, shipped alongside the bubble) pins
`movedTarget.domBoundaryLength = bottomCount` (so the fronted cup fires at the head's boundary) and, once the
fronted cup is rewritten to the head, is exactly the `headAtom.domBoundaryLength`-chained fronted list the
discharge needs.  `tailsCancel` is FREE (arc structure is trace-invariant).

So the entire cup-case conclusion follows from the shipped fixed-length interchange sort plus EXACTLY two
residual data: `windowPin` — the fronted cup is the head, genuine trace-orbit content the census CANNOT read
(`headCupWindowReadoff_isFalse`) — and the tail reselection `AtomicTraceEquiv tailList movedRest`.  This is the
honest maximal reduction of the round-9 fronting: `(a)` is built modulo `windowPin`, the interacting case is a
fixed-length interchange (no snake), and no arc-field readoff supplies `windowPin`. -/
theorem cupHeadExtractionConclusion_ofCensusFrontWindowPin (bottomCount : Nat)
    {overallSource overallTarget : adjunctionGraph.Mode}
    (headAtom movedTarget : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (headCupDom : headAtom.generatorDom.length = 0)
    (headCupCod : headAtom.generatorCod.length = 2)
    (secondList movedRest tailList :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (censusFront : AtomicTraceEquiv adjunctionModeSignature secondList (movedTarget :: movedRest))
    (frontedChained : SpineBoundaryChained bottomCount (movedTarget :: movedRest))
    (movedCupDom : movedTarget.generatorDom.length = 0)
    (headFires : headAtom.domBoundaryLength = bottomCount)
    (windowPin : movedTarget.leftContext.length = headAtom.leftContext.length)
    (tailChained : SpineBoundaryChained headAtom.codBoundaryLength tailList)
    (reselection : AtomicTraceEquiv adjunctionModeSignature tailList movedRest) :
    ∃ matchedRemainder,
      SpineTraceEquiv adjunctionModeSignature secondList (headAtom :: matchedRemainder)
        ∧ SpineBoundaryChained headAtom.codBoundaryLength matchedRemainder
        ∧ arcStructureOfSpineList headAtom.codBoundaryLength tailList
            = arcStructureOfSpineList headAtom.codBoundaryLength matchedRemainder := by
  have movedFires : movedTarget.domBoundaryLength = bottomCount :=
    (spineBoundaryChained_tail frontedChained).1
  have movedEqHead : movedTarget = headAtom :=
    frontCupToucher_eq_head_ofWindowPin bottomCount headAtom movedTarget
      headFires movedFires headCupDom movedCupDom windowPin
  have fronting : AtomicTraceEquiv adjunctionModeSignature secondList (headAtom :: movedRest) :=
    cupHeadFronting_ofCensusFrontWindowPin bottomCount headAtom movedTarget secondList movedRest
      censusFront headFires movedFires headCupDom movedCupDom windowPin
  have frontedChainedHead :
      SpineBoundaryChained headAtom.domBoundaryLength (headAtom :: movedRest) := by
    rw [movedEqHead] at frontedChained
    rw [headFires]
    exact frontedChained
  exact cupHeadExtractionConclusion_ofFrontedHeadReselection headAtom headCupCod
    tailList secondList movedRest fronting frontedChainedHead tailChained reselection

/-! ## Honesty marker -/

/-- **Honesty marker — the fixed-length fronting `(a)` is BUILT from the shipped census front, modulo
`windowPin` (flag-B R9).**  `cupHeadFronting_ofCensusFrontWindowPin`: a census front of a located cup to the
front of `secondList` (the shipped fixed-length interchange sort `arcCupMixedFrontsCup_ofCupCountPos`,
terminating by the cup's Nat position, no `WellFounded.fix`) PLUS `windowPin` yields the fronting of the
GENUINE head `AtomicTraceEquiv secondList (headAtom :: movedRest)`, because a matched window forces the
fronted cup to BE the head (`frontCupToucher_eq_head_ofWindowPin`, seed rigidity).
`cupHeadExtractionConclusion_ofCensusFrontWindowPin` threads that fronting into the swap-NF discharge
(`cupHeadExtractionConclusion_ofFrontedHeadReselection`) to land the full cup-case head extraction.

The length-changing snake NEVER appears: `AtomicTraceEquiv` is length-preserving and R8
`equalArcSpine_length_eq` excludes it from the instance, so the interacting cup/cap case is a fixed-length
interchange (Delpeuch–Vicary Theorem 3: exchanges swap heights only; a cup and a cap sharing a wire simply do
not exchange past each other — the fixed diagram forces a Godement-reachable permutation of the INDEPENDENT
generators, no snake).

What this marker does NOT claim: `windowPin` itself (the fronted cup IS the head — machine-refuted as a
universal arc readoff by `headCupWindowReadoff_isFalse`; genuine trace-orbit content) nor the tail reselection
(`AtomicTraceEquiv tailList movedRest`, the recursive completeness).  Those two are the sole surviving
residual of `arcCupReselection_exists` / `MixedTailArcCompleteness`.  The live discharge route is NOT the head
fronting but the peel-LAST short chord (`mixedSpine_lastCup_isShortChord`), where the last cup's window IS
arc-readable.  No gate flip; `fxMode_hasArcStructureReconstruction` stays `false`.  `= true`. -/
def fxMode_hasArcCupCensusFrontWindowPin : Bool := true

end FX1Poly.Polygraph
