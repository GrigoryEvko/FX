import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingComponentAlgebra
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcDisciplineFold
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPureCapSpine
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSeed

/-! # WalkingString/StringArcCapHeadLoops — the pure-cap cap-head fold never closes a loop (FC-3 r21)

The loops leg of the ADJOINT-TRIPLE cap-head extract correspondence, derived by the PARITY-FREE
distinctness route (route B).  The walking-adjunction lane closes loops-freedom through a typed-ends
`ArcOpenEndsDiscipline` whose refutation reads a cap's window as `tip`-parity against a discipline
pin — but the adjoint triple's two counits fire at BOTH parities (`counitLower : G·F ⇒ id_tip` at
`tip`, `counitUpper : H·G ⇒ id_base` at `base`), so the `tip = base` noConfusion is unavailable and
the parity route cannot be cloned.

The observation that dissolves the wall: the ONLY consumer is the PURE-CAP regime, and a cap never
merges two SURVIVING open wires — it consumes its window pair into a closed strand and hangs a fresh
event node.  So the mode-free invariant

  `ArcOpenEndsDistinct state := ∀ lo < hi < openWires.length,
      isSameComponent state.links (getAt openWires lo) (getAt openWires hi) = false`

("every two open wires sit in distinct components") is PRESERVED by a cap and holds at the fresh seed
and the post-cap seed — with parity NEVER mentioned, so `counitUpper` folds exactly like `counitLower`.
At every window pair the invariant gives `isSameComponent = false` directly, so the loop counter never
increments: every pure-cap boundary-chained spine folds from the (post-cap) seed with `loops = 0`.

The distinctness invariant, its initial truth, its cap-step preservation, the window-pair loop
constancy, the fold constancy over a pure-cap chained spine, and the post-cap-seed capstone
`stringArcCapHeadFolded_loops_zero` are all here.  `AllCapArity` is load-bearing (a cup would join two
adjacent open wires) and `SpineBoundaryChained` is load-bearing (it bounds the window in range) — both
are exercised by the anti-vacuity probes.

Raw Lean 4 + Init; structural recursion only; per-declaration `#assert_no_axioms` gated in the audit
twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private range plumbing (per-file copy, following the codebase pattern) -/

private theorem rangeLoopLength : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := rangeLoopLength count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length
        = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1,
        Nat.add_right_comm count accumulated.length 1]

private theorem rangeLength (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [rangeLoopLength count []]
  exact Nat.add_zero count

private theorem rangeLoopGetAt_past : (count : Nat) → (accumulated : List Nat) →
    (offset : Nat) →
    natListGetAt (List.range.loop count accumulated) (offset + count)
      = natListGetAt accumulated offset
  | 0, _, _ => rfl
  | count + 1, accumulated, offset => by
      have inner := rangeLoopGetAt_past count (count :: accumulated) (offset + 1)
      rw [Nat.add_assoc offset 1 count, Nat.add_comm 1 count] at inner
      exact inner

private theorem rangeLoopGetAt_below : (count : Nat) → (accumulated : List Nat) →
    (index : Nat) → index < count →
    natListGetAt (List.range.loop count accumulated) index = index
  | 0, _, _, indexBelow => absurd indexBelow (Nat.not_succ_le_zero _)
  | count + 1, accumulated, index, indexBelow => by
      cases Nat.lt_or_ge index count with
      | inl below => exact rangeLoopGetAt_below count (count :: accumulated) index below
      | inr atLeast =>
          have indexEq : index = count :=
            Nat.le_antisymm (Nat.le_of_succ_le_succ indexBelow) atLeast
          have pastRead := rangeLoopGetAt_past count (count :: accumulated) 0
          rw [Nat.zero_add count] at pastRead
          rw [indexEq]
          exact pastRead

private theorem rangeGetAt_below (count index : Nat) (indexBelow : index < count) :
    natListGetAt (List.range count) index = index :=
  rangeLoopGetAt_below count [] index indexBelow

/-- A strict inequality separates its endpoints, smaller side first. -/
private theorem neOfLtLeft {smaller larger : Nat} (isSmaller : smaller < larger) :
    smaller ≠ larger :=
  fun valuesEqual =>
    Nat.lt_irrefl smaller (Nat.lt_of_lt_of_le isSmaller (Nat.le_of_eq valuesEqual.symm))

/-! ## D1 — the parity-free distinctness invariant -/

/-- ★ **The mode-free open-ends distinctness invariant.**  Any two DISTINCT open positions of the arc
state read wires that sit in DIFFERENT union-find components.  Where the walking-adjunction discipline
typed a same-component pair by parity, this simply forbids same-component open pairs outright — so it
never mentions modes, and `counitUpper` (a `base`-parity cap) folds exactly like `counitLower` (a
`tip`-parity cap).  A cap merges only its consumed window pair, never two surviving wires, so this is
preserved; a cup would join an adjacent pair, so the pure-cap regime is required. -/
def ArcOpenEndsDistinct (state : ArcWireState) : Prop :=
  ∀ lowPosition highPosition : Nat,
    lowPosition < highPosition →
    highPosition < state.openWires.length →
    isSameComponent state.links (natListGetAt state.openWires lowPosition)
        (natListGetAt state.openWires highPosition) = false

/-! ## D2 — the fresh seed is distinct -/

/-- The canonical fresh seed satisfies the distinctness invariant: with no links every node is its own
root, and distinct range positions read distinct wires — no same-component open pair exists. -/
theorem arcOpenEndsDistinct_initial (bottomCount : Nat) :
    ArcOpenEndsDistinct (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) := by
  intro lowPosition highPosition lowBelowHigh highInRange
  have highBelowLength : highPosition < (List.range bottomCount).length := highInRange
  rw [rangeLength bottomCount] at highBelowLength
  rw [rangeGetAt_below bottomCount lowPosition (Nat.lt_trans lowBelowHigh highBelowLength),
    rangeGetAt_below bottomCount highPosition highBelowLength]
  exact decide_eq_false (neOfLtLeft lowBelowHigh)

/-! ## D3 — a cap step preserves distinctness -/

/-- After a cap's merge `unionFindJoin links leftWire rightWire`, two probes SEPARATE from both
consumed wires (and from each other) stay in distinct components: the flat-disjunction characterization
collapses on the two window-wire misses. -/
private theorem capMergedSurvivingSeparate (links : List (Nat × Nat))
    (forest : isUnionFindForest links) (leftWire rightWire probeOne probeTwo : Nat)
    (baseProbes : isSameComponent links probeOne probeTwo = false)
    (baseLeftOne : isSameComponent links leftWire probeOne = false)
    (baseLeftTwo : isSameComponent links leftWire probeTwo = false) :
    isSameComponent (unionFindJoin links leftWire rightWire) probeOne probeTwo = false := by
  rw [isSameComponent_unionFindJoin links forest leftWire rightWire probeOne probeTwo,
    baseProbes, baseLeftOne, baseLeftTwo]
  exact rfl

/-- The window wire is separate from any SURVIVING wire (one below the window, or two above the window
pair): the distinctness invariant reads it off with the positions in order (symmetrising when the
survivor sits left). -/
private theorem windowWireSurvivingSeparate (state : ArcWireState) (position : Nat)
    (distinct : ArcOpenEndsDistinct state)
    (windowBelowLength : position < state.openWires.length)
    (survivorIndex : Nat) (survivorBelowLength : survivorIndex < state.openWires.length)
    (survivorOffWindow : survivorIndex < position ∨ position + 2 ≤ survivorIndex) :
    isSameComponent state.links (natListGetAt state.openWires position)
        (natListGetAt state.openWires survivorIndex) = false := by
  cases survivorOffWindow with
  | inl survivorBelow =>
      have separated := distinct survivorIndex position survivorBelow windowBelowLength
      exact (isSameComponent_symm state.links (natListGetAt state.openWires position)
        (natListGetAt state.openWires survivorIndex)).trans separated
  | inr survivorPast =>
      have positionLtSurvivor : position < survivorIndex :=
        Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide)) survivorPast
      exact distinct position survivorIndex positionLtSurvivor survivorBelowLength

/-- The whole per-leaf fact: two SURVIVING wires (read at old indices off the consumed window pair)
stay in distinct components after the cap.  The cap's event join is transparent to old-node queries
(`isSameComponent_stepCapArc_oldNodes`), reducing to the merged-links separation
(`capMergedSurvivingSeparate`) fed by the invariant. -/
private theorem stepCapArc_survivingPairSeparate (state : ArcWireState) (position : Nat)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (nfPos : 0 < state.nextFresh) (distinct : ArcOpenEndsDistinct state)
    (windowBelowLength : position < state.openWires.length)
    (oldLo oldHi : Nat)
    (oldLoBelowLength : oldLo < state.openWires.length)
    (oldHiBelowLength : oldHi < state.openWires.length)
    (oldLoLtOldHi : oldLo < oldHi)
    (oldLoOffWindow : oldLo < position ∨ position + 2 ≤ oldLo)
    (oldHiOffWindow : oldHi < position ∨ position + 2 ≤ oldHi) :
    isSameComponent (stepCapArc state position).links
        (natListGetAt state.openWires oldLo) (natListGetAt state.openWires oldHi) = false := by
  have oldLoBelow : natListGetAt state.openWires oldLo < state.nextFresh :=
    natListGetAt_lt_ofInRange state.nextFresh state.openWires oldLo oldLoBelowLength fresh.1
  have oldHiBelow : natListGetAt state.openWires oldHi < state.nextFresh :=
    natListGetAt_lt_ofInRange state.nextFresh state.openWires oldHi oldHiBelowLength fresh.1
  rw [isSameComponent_stepCapArc_oldNodes state position fresh forest nfPos
      (natListGetAt state.openWires oldLo) (natListGetAt state.openWires oldHi)
      oldLoBelow oldHiBelow]
  exact capMergedSurvivingSeparate state.links forest
    (natListGetAt state.openWires position) (natListGetAt state.openWires (position + 1))
    (natListGetAt state.openWires oldLo) (natListGetAt state.openWires oldHi)
    (distinct oldLo oldHi oldLoLtOldHi oldHiBelowLength)
    (windowWireSurvivingSeparate state position distinct windowBelowLength oldLo
      oldLoBelowLength oldLoOffWindow)
    (windowWireSurvivingSeparate state position distinct windowBelowLength oldHi
      oldHiBelowLength oldHiOffWindow)

/-- ★ **A cap step preserves the distinctness invariant** (for ANY signature, no parity).  Two
surviving positions of the trimmed open-wire list read old positions off the consumed window pair
(below-window reads its own index, at-or-past reads two above); both survive distinct because a cap
never merges two surviving wires. -/
theorem arcOpenEndsDistinct_stepCapArc (state : ArcWireState) (position : Nat)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (windowInRange : position + 2 ≤ state.openWires.length)
    (distinct : ArcOpenEndsDistinct state) :
    ArcOpenEndsDistinct (stepCapArc state position) := by
  intro lowPosition highPosition lowBelowHigh highInRange
  have windowBelowLength : position < state.openWires.length :=
    Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide)) windowInRange
  have zeroBelowLength : 0 < state.openWires.length :=
    Nat.lt_of_lt_of_le (Nat.succ_pos (position + 1)) windowInRange
  have nfPos : 0 < state.nextFresh :=
    Nat.lt_of_le_of_lt (Nat.zero_le _)
      (natListGetAt_lt_ofInRange state.nextFresh state.openWires 0 zeroBelowLength fresh.1)
  have highBelowTrimmed :
      highPosition < (natListRemoveTwoAt state.openWires position).length := highInRange
  have trimmedLengthPlusTwo :
      (natListRemoveTwoAt state.openWires position).length + 2 = state.openWires.length :=
    natListRemoveTwoAt_length state.openWires position windowInRange
  cases Nat.lt_or_ge lowPosition position with
  | inl lowBelowPosition =>
      have lowRead :
          natListGetAt (stepCapArc state position).openWires lowPosition
            = natListGetAt state.openWires lowPosition :=
        natListGetAt_natListRemoveTwoAt_below state.openWires position lowPosition lowBelowPosition
      have lowBelowLength : lowPosition < state.openWires.length :=
        Nat.lt_trans lowBelowPosition windowBelowLength
      cases Nat.lt_or_ge highPosition position with
      | inl highBelowPosition =>
          have highRead :
              natListGetAt (stepCapArc state position).openWires highPosition
                = natListGetAt state.openWires highPosition :=
            natListGetAt_natListRemoveTwoAt_below state.openWires position highPosition
              highBelowPosition
          have highBelowLength : highPosition < state.openWires.length :=
            Nat.lt_trans highBelowPosition windowBelowLength
          rw [lowRead, highRead]
          exact stepCapArc_survivingPairSeparate state position fresh forest nfPos distinct
            windowBelowLength lowPosition highPosition lowBelowLength highBelowLength
            lowBelowHigh (Or.inl lowBelowPosition) (Or.inl highBelowPosition)
      | inr positionLeHigh =>
          obtain ⟨highOffset, highOffsetEq⟩ := Nat.le.dest positionLeHigh
          subst highOffsetEq
          have highOldBelowLength : position + highOffset + 2 < state.openWires.length := by
            rw [← trimmedLengthPlusTwo]
            exact Nat.add_lt_add_right highBelowTrimmed 2
          have highRead :
              natListGetAt (stepCapArc state position).openWires (position + highOffset)
                = natListGetAt state.openWires (position + highOffset + 2) :=
            natListGetAt_natListRemoveTwoAt_pastPair state.openWires position highOffset
              windowInRange
          have lowLtHighOld : lowPosition < position + highOffset + 2 :=
            Nat.lt_trans lowBelowPosition
              (Nat.lt_of_le_of_lt (Nat.le_add_right position highOffset)
                (Nat.lt_add_of_pos_right (by decide)))
          rw [lowRead, highRead]
          exact stepCapArc_survivingPairSeparate state position fresh forest nfPos distinct
            windowBelowLength lowPosition (position + highOffset + 2) lowBelowLength
            highOldBelowLength lowLtHighOld (Or.inl lowBelowPosition)
            (Or.inr (Nat.add_le_add_right (Nat.le_add_right position highOffset) 2))
  | inr positionLeLow =>
      obtain ⟨lowOffset, lowOffsetEq⟩ := Nat.le.dest positionLeLow
      subst lowOffsetEq
      have positionLeHigh : position ≤ highPosition :=
        Nat.le_trans (Nat.le_add_right position lowOffset) (Nat.le_of_lt lowBelowHigh)
      obtain ⟨highOffset, highOffsetEq⟩ := Nat.le.dest positionLeHigh
      subst highOffsetEq
      have highOldBelowLength : position + highOffset + 2 < state.openWires.length := by
        rw [← trimmedLengthPlusTwo]
        exact Nat.add_lt_add_right highBelowTrimmed 2
      have lowOldBelowHighOld : position + lowOffset + 2 < position + highOffset + 2 :=
        Nat.add_lt_add_right lowBelowHigh 2
      have lowOldBelowLength : position + lowOffset + 2 < state.openWires.length :=
        Nat.lt_trans lowOldBelowHighOld highOldBelowLength
      have lowRead :
          natListGetAt (stepCapArc state position).openWires (position + lowOffset)
            = natListGetAt state.openWires (position + lowOffset + 2) :=
        natListGetAt_natListRemoveTwoAt_pastPair state.openWires position lowOffset windowInRange
      have highRead :
          natListGetAt (stepCapArc state position).openWires (position + highOffset)
            = natListGetAt state.openWires (position + highOffset + 2) :=
        natListGetAt_natListRemoveTwoAt_pastPair state.openWires position highOffset windowInRange
      rw [lowRead, highRead]
      exact stepCapArc_survivingPairSeparate state position fresh forest nfPos distinct
        windowBelowLength (position + lowOffset + 2) (position + highOffset + 2)
        lowOldBelowLength highOldBelowLength lowOldBelowHighOld
        (Or.inr (Nat.add_le_add_right (Nat.le_add_right position lowOffset) 2))
        (Or.inr (Nat.add_le_add_right (Nat.le_add_right position highOffset) 2))

/-! ## D4 — a distinct window pair keeps the loop count -/

/-- ★ **A cap at a distinct state keeps the loop count.**  The window pair `(position, position + 1)`
is a distinct open pair by the invariant, so the cap's `wasSameComponent` guard is `false` and the
counter stands.  This is the parity-free replacement for `stepCapArc_loops_ofDisciplined`. -/
theorem stepCapArc_loops_ofDistinct (state : ArcWireState) (position : Nat)
    (windowInRange : position + 2 ≤ state.openWires.length)
    (distinct : ArcOpenEndsDistinct state) :
    (stepCapArc state position).loops = state.loops := by
  have windowSuccBelowLength : position + 1 < state.openWires.length :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self (position + 1)) windowInRange
  have windowSeparate : isSameComponent state.links (natListGetAt state.openWires position)
      (natListGetAt state.openWires (position + 1)) = false :=
    distinct position (position + 1) (Nat.lt_succ_self position) windowSuccBelowLength
  show (if isSameComponent state.links (natListGetAt state.openWires position)
          (natListGetAt state.openWires (position + 1))
        then state.loops + 1 else state.loops)
     = state.loops
  rw [windowSeparate]
  exact if_neg (fun falseEqTrue => Bool.noConfusion falseEqTrue)

/-! ## D5 — the fold over a pure-cap chained spine keeps the loop count -/

/-- ★ **A pure-cap boundary-chained spine's arc fold keeps the loop count end-to-end.**  Structural
recursion on the `AllCapArity` witness: each head is a cap, its step is `stepCapArc` at the window,
the chained boundary bounds the window in range, and distinctness (with freshness / forestness /
tracking) threads alongside — so each cap keeps the count (`stepCapArc_loops_ofDistinct`) and the fold
carries it.  Generic over signature (parity never enters). -/
theorem processArcSpine_loops_ofPureCapDistinct {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (atoms : List (SpineAtom signature sourceMode targetMode))
    (allCap : AllCapArity atoms) :
    (state : ArcWireState) → (boundaryLength : Nat) →
    ArcStateFresh state → isUnionFindForest state.links →
    state.openWires.length = boundaryLength →
    SpineBoundaryChained boundaryLength atoms →
    ArcOpenEndsDistinct state →
    (processArcSpine state atoms).loops = state.loops := by
  induction allCap with
  | nil => intro state _ _ _ _ _ _; exact rfl
  | cons hasCapDomArity hasCapCodArity restAllCap restKeepsLoops =>
      rename_i headAtom restAtoms
      intro state _boundaryLength fresh forest tracks chained distinct
      obtain ⟨headFires, tailChained⟩ := spineBoundaryChained_tail chained
      have capArity : AtomHasCupOrCapArity headAtom := Or.inr ⟨hasCapDomArity, hasCapCodArity⟩
      have tracksEntry : state.openWires.length = headAtom.domBoundaryLength :=
        tracks.trans headFires.symm
      have entryShape : state.openWires.length
          = headAtom.leftContext.length + headAtom.generatorDom.length
            + headAtom.rightContext.length := tracksEntry
      have windowInRange : headAtom.leftContext.length + 2 ≤ state.openWires.length := by
        rw [entryShape, hasCapDomArity]
        exact Nat.le_add_right (headAtom.leftContext.length + 2) headAtom.rightContext.length
      have headStepEq : stepArcAtom state headAtom = stepCapArc state headAtom.leftContext.length :=
        stepArcAtom_eq_stepCapArc state headAtom hasCapDomArity hasCapCodArity
      show (processArcSpine (stepArcAtom state headAtom) restAtoms).loops = state.loops
      have headLoopsKept : (stepArcAtom state headAtom).loops = state.loops := by
        rw [headStepEq]
        exact stepCapArc_loops_ofDistinct state headAtom.leftContext.length windowInRange distinct
      have distinctNext : ArcOpenEndsDistinct (stepArcAtom state headAtom) := by
        rw [headStepEq]
        exact arcOpenEndsDistinct_stepCapArc state headAtom.leftContext.length fresh forest
          windowInRange distinct
      have restKept := restKeepsLoops (stepArcAtom state headAtom) headAtom.codBoundaryLength
        (arcStateFresh_stepArcAtom state headAtom fresh)
        (isUnionFindForest_stepArcAtom_ofCupOrCap state headAtom capArity forest)
        (stepArcAtom_openWires_tracksBoundary state headAtom capArity tracksEntry)
        tailChained distinctNext
      exact restKept.trans headLoopsKept

/-! ## D6a — the fresh-seed pure-cap capstone -/

/-- ★ **Every pure-cap boundary-chained spine folds from the fresh seed with `loops = 0`** — the
parity-free analog of `arcFoldLoops_zero_ofChainedSpineList`, generic over signature. -/
theorem arcFoldLoops_zero_ofPureCapChained {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (bottomCount : Nat)
    (atoms : List (SpineAtom signature sourceMode targetMode))
    (allCap : AllCapArity atoms)
    (chained : SpineBoundaryChained bottomCount atoms) :
    (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
      atoms).loops = 0 :=
  processArcSpine_loops_ofPureCapDistinct atoms allCap
    (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) bottomCount
    (arcStateFresh_initial bottomCount) isUnionFindForest_nil (rangeLength bottomCount)
    chained (arcOpenEndsDistinct_initial bottomCount)

/-! ## D6b — the post-cap-seed capstone (the #15 cap-head target, adjoint-triple) -/

/-- ★ **The pure-cap cap-head fold never closes a loop** (adjoint-triple seed).  The peeled head cap
consumes the window pair into a closed strand and the counter stands at zero
(`stepCapArc_loops_ofDistinct` at the fresh seed), the post-cap seed inherits distinctness
(`arcOpenEndsDistinct_stepCapArc`) alongside freshness / forest / tracking, and the pure-cap chained
fold carries the zero to the end — with parity NEVER mentioned, so a `counitUpper` head folds exactly
like a `counitLower` head.  This is the loops leg #15 the parity route could not clone. -/
theorem stringArcCapHeadFolded_loops_zero
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (bottomCount windowPosition tailBoundary : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount)
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (allCap : AllCapArity atoms)
    (chained : SpineBoundaryChained tailBoundary atoms) :
    (processArcSpine
      (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        windowPosition) atoms).loops = 0 := by
  have windowFitsRange : windowPosition + 2 ≤ (List.range bottomCount).length := by
    rw [rangeLength]
    exact windowFits
  have seedDistinct : ArcOpenEndsDistinct
      (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        windowPosition) :=
    arcOpenEndsDistinct_stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
      windowPosition (arcStateFresh_initial bottomCount) isUnionFindForest_nil windowFitsRange
      (arcOpenEndsDistinct_initial bottomCount)
  have seedTracks : (stepCapArc
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
      windowPosition).openWires.length = tailBoundary := by
    show (natListRemoveTwoAt (List.range bottomCount) windowPosition).length = tailBoundary
    have removedShift : (natListRemoveTwoAt (List.range bottomCount)
          windowPosition).length + 2
        = tailBoundary + 2 :=
      ((natListRemoveTwoAt_length (List.range bottomCount) windowPosition
          windowFitsRange).trans (rangeLength bottomCount)).trans tailBoundaryFits.symm
    exact Nat.succ.inj (Nat.succ.inj removedShift)
  have foldKept := processArcSpine_loops_ofPureCapDistinct atoms allCap
    (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
      windowPosition)
    tailBoundary
    (stepCapArc_arcStateFresh
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition
      (arcStateFresh_initial bottomCount))
    (isUnionFindForest_stepCapArc
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition
      isUnionFindForest_nil)
    seedTracks chained seedDistinct
  have seedLoops : (stepCapArc
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
      windowPosition).loops = 0 :=
    stepCapArc_loops_ofDistinct
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition
      windowFitsRange (arcOpenEndsDistinct_initial bottomCount)
  exact foldKept.trans seedLoops

/-! ## Anti-vacuity probes — the parity-killer shape holds; the hypotheses are load-bearing -/

/-- A concrete `counitUpper` cap atom (`H·G ⇒ id_base`, a `base`-parity cap) at the empty left context
of the bottom `base` boundary — the exact shape the walking-adjunction parity route could NOT refute. -/
def probeCounitUpperAtom :
    SpineAtom adjointTripleModeSignature AdjointTripleMode.base AdjointTripleMode.base where
  leftMidMode := AdjointTripleMode.base
  rightMidMode := AdjointTripleMode.base
  leftContext := ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base
  generatorDom := stringHG
  generatorCod := ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base
  generator := StringTwoCell.counitUpper
  rightContext := ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base

/-- ★ **Anti-vacuity (positive): `stringArcCapHeadFolded_loops_zero` accepts a `counitUpper`-headed
pure-cap spine and returns `loops = 0`.**  The peeled head cap consumes window `[0,1]` of `range 4`,
the tail `counitUpper` cap fires at the post-cap boundary `2` — a `base`-parity cap the parity route
could never touch — and the fold reports zero.  This exercises the whole derivation on the exact
parity-killer shape. -/
theorem probeCounitUpperLoopsZero :
    (processArcSpine
      (stepCapArc (ArcWireState.mk (List.range 4) [] 4 0 [] []) 0)
      [probeCounitUpperAtom]).loops = 0 :=
  stringArcCapHeadFolded_loops_zero 4 0 2 (by decide) (by decide) [probeCounitUpperAtom]
    (AllCapArity.cons rfl rfl AllCapArity.nil)
    (SpineBoundaryChained.cons probeCounitUpperAtom rfl (SpineBoundaryChained.nil _))

/-- ★ **Anti-vacuity (negative — `AllCapArity` is load-bearing): a CUP followed by a CAP on its own
legs DOES close a loop.**  A cup joins its two fresh legs; the immediately following cap on the same
window finds them already same-component and increments the loop counter to `1`.  So dropping the
pure-cap hypothesis breaks loops-freedom — the fold is not vacuously zero. -/
theorem probeCupThenCapClosesLoop :
    (stepCapArc (stepCupArc (ArcWireState.mk [] [] 0 0 [] []) 0) 0).loops = 1 := by decide

/-- ★ **Anti-vacuity (negative — chainedness is load-bearing): an OUT-OF-RANGE cap closes a spurious
loop.**  A cap fired at a window beyond the open-wire list reads the default wire `0` for both legs;
they are trivially same-component and the counter increments to `1`.  So the `SpineBoundaryChained`
window bound is load-bearing — without it the fold is not zero. -/
theorem probeOutOfRangeCapClosesLoop :
    (stepCapArc (ArcWireState.mk [5] [] 6 0 [] []) 3).loops = 1 := by decide

/-! ## Honesty marker -/

/-- **Honesty marker — the PURE-CAP cap-head fold never closes a loop (FC-3 r21, route B).**
`stringArcCapHeadFolded_loops_zero`: on the adjoint-triple seed, the peeled head cap keeps the counter
at zero, the post-cap seed carries the mode-free distinctness invariant (`ArcOpenEndsDistinct`) via its
initial truth (`arcOpenEndsDistinct_initial`) and cap-step preservation
(`arcOpenEndsDistinct_stepCapArc`), the window pair keeps the loop count
(`stepCapArc_loops_ofDistinct`), and the pure-cap chained fold
(`processArcSpine_loops_ofPureCapDistinct` / `arcFoldLoops_zero_ofPureCapChained`) carries the zero to
the end.  Parity is NEVER mentioned, so a `counitUpper` (`base`) head folds exactly like a
`counitLower` (`tip`) head — dissolving the parity wall the walking-adjunction discipline hit.  The
probes confirm the derivation fires on the `counitUpper` parity-killer shape and that both `AllCapArity`
and `SpineBoundaryChained` are load-bearing.  What this marker does NOT claim: the assembled cap-head
`FullArcStructure` / cancellation extract equalities (which CONSUME this loops leg).  `= true`. -/
def fxString_hasArcCapHeadLoopLeg : Bool := true

end FX1Poly.Polygraph
