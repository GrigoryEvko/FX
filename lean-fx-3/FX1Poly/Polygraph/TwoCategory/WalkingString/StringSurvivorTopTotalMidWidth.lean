import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyTopCountTotal
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSpineValleyWidthTelescope

/-! # WalkingString/StringSurvivorTopTotalMidWidth — the survivor-top total is the mid-width over the
walking ADJOINT-TRIPLE (`F ⊣ G ⊣ H`) signature (FC-3 r29, M2a: the mid-width-from-matching leg)

The string clone of the walking-adjunction `survivorTopTotal_eq_midWidth` (`ValleyTopCountTotal`).  This is the
M2a leg the mid-zero producer needs: for a valley `capBlock ++ cupBlock` at bottom count `bc` (pure cap block,
pure cup block, boundary-chained cup), the survivor-top total of the whole valley's `matchingOf` equals the cap
block's own open-wire count `midWidth`.  The producer consumes it at both valleys to rewrite `survivorTopTotal V`
back to `midWidth = 0`.

The survivor re-ranking is signature-BLIND: the survivor-top count reads only wire ORDER and the fresh floor, never
the `F ≠ H` species distinction.  So every brick below is a byte-identical token-swap of the walking-adjunction
original over `{signature}`-generic seed facts (`countBelow_atStrictMonoImage_full_eq_sourceLength`,
`survivorTop_iff_cupImage`, the union-find floor duals, the per-atom fresh/order lemmas), with the signature token
alone rerouted `adjunctionModeSignature → adjointTripleModeSignature`.  No new mathematics, no unproven residual.

  * `stringAtomsFreshTotal_ofAllCapArity` … `stringProcessSpine_openWires_below_ofAllCapArity_seed` — the pure-cap
    seed facts: a cap block allocates no fresh id, so from the canonical seed every link endpoint and every surviving
    open wire sits in the bottom range `< bc`.
  * `stringProcessSpine_edgesFloorHomogeneous_ofAllCupArity` — the cup-block fold of floor-homogeneity (no valley
    edge crosses the floor `bc`).
  * `stringProcessSpine_wireOrderImageCover_ofAllCupArity` — the value-surjectivity leg: a pure-cup block order-embeds
    the mid-state open wires so the image covers every below-floor final position.
  * ★ `stringSurvivorTopTotal_eq_midWidth` — the keystone: `survivorTopTotal (matchingOf bc (capBlock ++ cupBlock))
    = midWidth`.  The bottom segment `[0, bc)` never survives; over the top offsets the survivor-top predicate marks
    EXACTLY the cup-embedding images (`survivorTop_iff_cupImage`), so
    `countBelow_atStrictMonoImage_full_eq_sourceLength` collapses the count to `midWidth`.

A concrete truth-probe fires the whole machinery on a genuine mixed string valley `[ε] ++ [η']` at `tip`
(`bottomCount = 2`, cap consumes both bottom wires → `midWidth = 0`), so the keystone is not vacuous on a real
string valley.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; structural recursion, no
`WellFounded.fix`; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Local plumbing -/

/-- An in-range positional read is a member (local copy; the origin's `getAt_mem_of_lt` is `private`, so a distinct
private clone keeps the umbrella build's global table duplicate-free). -/
private theorem stringGetAtMemOfLt : (wires : List Nat) → (index : Nat) →
    index < wires.length → natListGetAt wires index ∈ wires
  | [], _, indexInRange => absurd indexInRange (Nat.not_lt_zero _)
  | _ :: _, 0, _ => List.Mem.head _
  | _ :: rest, index + 1, indexInRange =>
      List.Mem.tail _ (stringGetAtMemOfLt rest index (Nat.lt_of_succ_lt_succ indexInRange))

/-! ## The pure-cap fresh-id seed -/

/-- A pure-cap block's total fresh count is zero — every cap has empty codomain, so each `atomsFreshTotal` summand
vanishes.  Induction on the `AllCapArity` witness. -/
theorem stringAtomsFreshTotal_ofAllCapArity
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (pureCap : AllCapArity atoms) : atomsFreshTotal atoms = 0 := by
  induction pureCap with
  | nil => rfl
  | cons _hasCapDomArity hasCapCodArity _restAllCap restFreshZero =>
      rename_i headAtom rest
      show headAtom.generatorCod.length + atomsFreshTotal rest = 0
      rw [hasCapCodArity, restFreshZero]

/-- ★ **A pure-cap block leaves `nextFresh` untouched.**  Its total fresh count is zero
(`stringAtomsFreshTotal_ofAllCapArity`), and the fold raises `nextFresh` by exactly that count
(`processSpine_nextFresh`).  Caps never allocate — every node the block touches was already present. -/
theorem stringProcessSpine_nextFresh_ofAllCapArity
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (pureCap : AllCapArity atoms) (state : WireState) :
    (processSpine state atoms).nextFresh = state.nextFresh := by
  rw [processSpine_nextFresh atoms state, stringAtomsFreshTotal_ofAllCapArity atoms pureCap, Nat.add_zero]

/-- ★ **From the canonical seed, a pure-cap block's final `nextFresh` is the bottom count.**  The seed's
`nextFresh` is `bottomCount` and the cap block leaves it fixed — the whole pure-cap matching lives in the bottom
range. -/
theorem stringProcessSpine_nextFresh_ofAllCapArity_seed
    {overallSource overallTarget : adjointTripleGraph.Mode} (bottomCount : Nat)
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (pureCap : AllCapArity atoms) :
    (processSpine { openWires := List.range bottomCount, links := [], nextFresh := bottomCount, loops := 0 }
        atoms).nextFresh = bottomCount :=
  stringProcessSpine_nextFresh_ofAllCapArity atoms pureCap
    { openWires := List.range bottomCount, links := [], nextFresh := bottomCount, loops := 0 }

/-- ★ **Every link endpoint of a pure-cap matching sits in the bottom range.**  The shipped `WireStateFresh` fold
keeps every edge endpoint `< nextFresh`, and the cap block pins `nextFresh = bottomCount`.  No cap ever joins a
fresh id — the connectivity seed of the survivor re-ranking. -/
theorem stringProcessSpine_links_below_ofAllCapArity_seed
    {overallSource overallTarget : adjointTripleGraph.Mode} (bottomCount : Nat)
    (bottomPositive : 0 < bottomCount)
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (pureCap : AllCapArity atoms) :
    ∀ edge ∈ (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ atoms).links,
      edge.1 < bottomCount ∧ edge.2 < bottomCount := by
  intro edge edgeInLinks
  have conditions := matchingSwapStateConditions_processSpine bottomCount atoms
    { openWires := List.range bottomCount, links := [], nextFresh := bottomCount, loops := 0 }
    (matchingSwapStateConditions_initial bottomCount bottomPositive)
  have freshEdges := conditions.fresh.2 edge edgeInLinks
  rw [stringProcessSpine_nextFresh_ofAllCapArity_seed bottomCount atoms pureCap] at freshEdges
  exact freshEdges

/-- ★ **Every surviving open wire of a pure-cap matching is a bottom node.**  Same `WireStateFresh` +
`nextFresh = bottomCount` argument as the link bound: the survivors are a sub-collection of the original bottom
ports.  The open-wire half of the survivor seed. -/
theorem stringProcessSpine_openWires_below_ofAllCapArity_seed
    {overallSource overallTarget : adjointTripleGraph.Mode} (bottomCount : Nat)
    (bottomPositive : 0 < bottomCount)
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (pureCap : AllCapArity atoms) :
    ∀ wire ∈ (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ atoms).openWires,
      wire < bottomCount := by
  intro wire wireInOpen
  have conditions := matchingSwapStateConditions_processSpine bottomCount atoms
    { openWires := List.range bottomCount, links := [], nextFresh := bottomCount, loops := 0 }
    (matchingSwapStateConditions_initial bottomCount bottomPositive)
  have freshWire := conditions.fresh.1 wire wireInOpen
  rw [stringProcessSpine_nextFresh_ofAllCapArity_seed bottomCount atoms pureCap] at freshWire
  exact freshWire

/-! ## The cup-block fold of floor-homogeneity -/

/-- ★ **A pure-cup block preserves floor-homogeneity of every edge.**  Run from floor-homogeneous links whose
fresh counter sits at or above the floor and which are `WireStateFresh`, every cup prepends only the
at-or-above-floor edge `(nextFresh, nextFresh + 1)` (`stepCup_edgesFloorHomogeneous`).  `AllCupArity` induction,
threading `WireStateFresh` and the monotone floor bound. -/
theorem stringProcessSpine_edgesFloorHomogeneous_ofAllCupArity
    {overallSource overallTarget : adjointTripleGraph.Mode} (floor : Nat)
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (pureCup : AllCupArity atoms) :
    (state : WireState) → WireStateFresh state → floor ≤ state.nextFresh →
    (∀ edge ∈ state.links, edgeFloorHomogeneous floor edge) →
    ∀ edge ∈ (processSpine state atoms).links, edgeFloorHomogeneous floor edge := by
  induction pureCup with
  | nil => intro state _ _ baseHomog; exact baseHomog
  | cons hasCupDomArity hasCupCodArity _restAllCup restHomog =>
      rename_i headAtom rest
      intro state fresh floorLe baseHomog
      show ∀ edge ∈ (processSpine (stepAtom state headAtom) rest).links, edgeFloorHomogeneous floor edge
      rw [stepAtom_ofCupArity state headAtom hasCupDomArity hasCupCodArity]
      refine restHomog (stepCup state headAtom.leftContext.length)
        (stepCup_wireStateFresh state headAtom.leftContext.length fresh) ?_
        (stepCup_edgesFloorHomogeneous state headAtom.leftContext.length floor fresh floorLe baseHomog)
      rw [stepCup_nextFresh]
      exact Nat.le_trans floorLe (Nat.le_add_right state.nextFresh 2)

/-! ## The value-surjectivity leg -/

/-- ★ **Value-surjectivity — a pure-cup block order-embeds the mid-state open wires so the image COVERS every
below-floor final position.**  The `phi` is the same strictly-monotone, value-preserving, in-range order embedding,
and additionally its image covers the survivors: every final position either is `phi sourcePos` for an in-range
source position, or holds an at-or-above-floor value (a cup leg).  `AllCupArity` induction; each cup at
`leftContext.length` splices `[nextFresh, nextFresh + 1]` (both `≥ freshFloor`), and the tail's cover pulls back
through `shiftPastPosition` (`shiftPastPosition_surjOffBlock`).  A pure open-wire-list fact. -/
theorem stringProcessSpine_wireOrderImageCover_ofAllCupArity
    {overallSource overallTarget : adjointTripleGraph.Mode} (freshFloor : Nat)
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (pureCup : AllCupArity atoms) :
    (state : WireState) → (boundaryLength : Nat) →
    state.openWires.length = boundaryLength → freshFloor ≤ state.nextFresh →
    SpineBoundaryChained boundaryLength atoms →
    ∃ phi, WireOrderEmbedding phi state.openWires (processSpine state atoms).openWires ∧
      ∀ targetPos, targetPos < (processSpine state atoms).openWires.length →
        (∃ sourcePos, sourcePos < state.openWires.length ∧ phi sourcePos = targetPos)
          ∨ freshFloor ≤ natListGetAt (processSpine state atoms).openWires targetPos := by
  induction pureCup with
  | nil =>
      intro state _ _ _ _
      refine ⟨fun index => index, wireOrderEmbedding_id state.openWires, ?_⟩
      intro targetPos targetInRange
      exact Or.inl ⟨targetPos, targetInRange, rfl⟩
  | cons hasCupDomArity hasCupCodArity _restAllCup restCover =>
      rename_i headAtom rest
      intro state boundaryLength tracks freshLe chained
      obtain ⟨headFires, tailChained⟩ := spineBoundaryChained_tail chained
      have posLeBoundary : headAtom.leftContext.length ≤ boundaryLength := by
        rw [← headFires]
        show headAtom.leftContext.length
          ≤ headAtom.leftContext.length + headAtom.generatorDom.length + headAtom.rightContext.length
        rw [hasCupDomArity, Nat.add_zero]
        exact Nat.le_add_right headAtom.leftContext.length headAtom.rightContext.length
      have posInRange : headAtom.leftContext.length ≤ state.openWires.length := by
        rw [tracks]; exact posLeBoundary
      have newTracks : (stepCup state headAtom.leftContext.length).openWires.length
          = headAtom.codBoundaryLength := by
        rw [stepCup_openWires, natListInsertAt_length]
        show state.openWires.length + 2 = headAtom.codBoundaryLength
        rw [tracks, ← headFires]
        show headAtom.leftContext.length + headAtom.generatorDom.length + headAtom.rightContext.length + 2
          = headAtom.leftContext.length + headAtom.generatorCod.length + headAtom.rightContext.length
        rw [hasCupDomArity, hasCupCodArity, Nat.add_zero]
        exact Nat.add_right_comm headAtom.leftContext.length headAtom.rightContext.length 2
      have newFresh : freshFloor ≤ (stepCup state headAtom.leftContext.length).nextFresh := by
        rw [stepCup_nextFresh]
        exact Nat.le_trans freshLe (Nat.le_add_right state.nextFresh 2)
      obtain ⟨phiRest, embRest, coverRest⟩ :=
        restCover (stepCup state headAtom.leftContext.length) headAtom.codBoundaryLength newTracks
          newFresh tailChained
      have headEmbed := stepCup_wireOrderEmbedding state headAtom.leftContext.length posInRange
      have legValueLeft : natListGetAt (stepCup state headAtom.leftContext.length).openWires
          headAtom.leftContext.length = state.nextFresh := by
        rw [stepCup_openWires]
        have inside := natListGetAt_natListInsertAt_inside state.openWires headAtom.leftContext.length
          [state.nextFresh, state.nextFresh + 1] 0 (Nat.succ_pos 1) posInRange
        rw [Nat.add_zero] at inside
        exact inside
      have legValueRight : natListGetAt (stepCup state headAtom.leftContext.length).openWires
          (headAtom.leftContext.length + 1) = state.nextFresh + 1 := by
        rw [stepCup_openWires]
        exact natListGetAt_natListInsertAt_inside state.openWires headAtom.leftContext.length
          [state.nextFresh, state.nextFresh + 1] 1 (Nat.lt_succ_self 1) posInRange
      have stepLen : (stepCup state headAtom.leftContext.length).openWires.length
          = state.openWires.length + 2 := by
        rw [stepCup_openWires]
        exact natListInsertAt_length state.openWires headAtom.leftContext.length
          [state.nextFresh, state.nextFresh + 1]
      show ∃ phi, WireOrderEmbedding phi state.openWires
          (processSpine (stepAtom state headAtom) rest).openWires ∧
        ∀ targetPos, targetPos < (processSpine (stepAtom state headAtom) rest).openWires.length →
          (∃ sourcePos, sourcePos < state.openWires.length ∧ phi sourcePos = targetPos)
            ∨ freshFloor ≤ natListGetAt (processSpine (stepAtom state headAtom) rest).openWires targetPos
      rw [stepAtom_ofCupArity state headAtom hasCupDomArity hasCupCodArity]
      refine ⟨fun index => phiRest (shiftPastPosition headAtom.leftContext.length 2 index),
        wireOrderEmbedding_comp headEmbed embRest, ?_⟩
      intro targetPos targetInRange
      rcases coverRest targetPos targetInRange with ⟨midPos, midInRange, phiRestEq⟩ | freshVal
      · have midInRange' : midPos < state.openWires.length + 2 := stepLen ▸ midInRange
        match Nat.decEq midPos headAtom.leftContext.length with
        | isTrue midIsLeft =>
            have readEq := embRest.reads midPos midInRange
            rw [phiRestEq, midIsLeft, legValueLeft] at readEq
            exact Or.inr (by rw [readEq]; exact freshLe)
        | isFalse midNeLeft =>
            match Nat.decEq midPos (headAtom.leftContext.length + 1) with
            | isTrue midIsRight =>
                have readEq := embRest.reads midPos midInRange
                rw [phiRestEq, midIsRight, legValueRight] at readEq
                exact Or.inr (by rw [readEq]; exact Nat.le_trans freshLe (Nat.le_succ state.nextFresh))
            | isFalse midNeRight =>
                obtain ⟨sourcePos, sourceLt, shiftEq⟩ :=
                  shiftPastPosition_surjOffBlock headAtom.leftContext.length state.openWires.length
                    midPos posInRange midInRange' midNeLeft midNeRight
                refine Or.inl ⟨sourcePos, sourceLt, ?_⟩
                show phiRest (shiftPastPosition headAtom.leftContext.length 2 sourcePos) = targetPos
                rw [shiftEq]; exact phiRestEq
      · exact Or.inr freshVal

/-! ## The keystone: the survivor-top total is the mid-width -/

/-- ★ **The survivor-top total is the mid-width (string, M2a).**  For a valley `capBlock ++ cupBlock` over the
walking adjoint-triple signature (pure cap block, pure cup block, boundary-chained cup), the survivor-top total of
the whole valley's `matchingOf` equals the cap block's own open-wire count `midWidth`.  The count over the whole
boundary splits (`countBelow_add_eq`) into the bottom segment (never a survivor-top — all-false) and the top
offsets `[0, finalLen)`; over those the survivor-top predicate marks EXACTLY the cup-embedding images
(`survivorTop_iff_cupImage`, both directions), so `countBelow_atStrictMonoImage_full_eq_sourceLength` collapses the
count to `midWidth`.  Every hypothesis is discharged from the SAME shipped seed-fact block, token-swapped to the
three-colour signature. -/
theorem stringSurvivorTopTotal_eq_midWidth
    {overallSource overallTarget : adjointTripleGraph.Mode} (bottomCount : Nat)
    (bottomPositive : 0 < bottomCount)
    (capBlock cupBlock : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (capPure : AllCapArity capBlock) (cupPure : AllCupArity cupBlock)
    (cupChained : SpineBoundaryChained
        (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length cupBlock) :
    survivorTopTotal (matchingOfSpineList bottomCount (capBlock ++ cupBlock))
      = (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length := by
  let capState := processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock
  let wholeState := processSpine capState cupBlock
  have wholeSplit : matchingOfSpineList bottomCount (capBlock ++ cupBlock)
      = extractDiagram bottomCount wholeState := by
    show extractDiagram bottomCount (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩
        (capBlock ++ cupBlock)) = extractDiagram bottomCount wholeState
    rw [processSpine_append capBlock cupBlock ⟨List.range bottomCount, [], bottomCount, 0⟩]
  rw [wholeSplit]
  show survivorTopCount (extractDiagram bottomCount wholeState)
      (bottomCount + wholeState.openWires.length) = capState.openWires.length
  rw [survivorTopCount_eq_countBelow,
    countBelow_add_eq (isSurvivorTop (extractDiagram bottomCount wholeState)) bottomCount
      wholeState.openWires.length]
  have bottomZero :
      countBelow (isSurvivorTop (extractDiagram bottomCount wholeState)) bottomCount = 0 := by
    apply countBelow_eq_zero_of_allFalse
    intro index indexLt
    show (Nat.ble (extractDiagram bottomCount wholeState).bottomCount index
        && Nat.blt (natListGetAt (extractDiagram bottomCount wholeState).partner index)
            (extractDiagram bottomCount wholeState).bottomCount) = false
    have bleFalse : Nat.ble (extractDiagram bottomCount wholeState).bottomCount index = false := by
      cases hble : Nat.ble (extractDiagram bottomCount wholeState).bottomCount index with
      | false => rfl
      | true => exact absurd (Nat.le_of_ble_eq_true hble) (Nat.not_le.mpr indexLt)
    rw [bleFalse, Bool.false_and]
  rw [bottomZero, Nat.zero_add]
  have capNextFresh : capState.nextFresh = bottomCount :=
    stringProcessSpine_nextFresh_ofAllCapArity_seed bottomCount capBlock capPure
  obtain ⟨phi, embedding, cover⟩ := stringProcessSpine_wireOrderImageCover_ofAllCupArity bottomCount cupBlock cupPure
    capState capState.openWires.length rfl (Nat.le_of_eq capNextFresh.symm) cupChained
  have capFresh : WireStateFresh capState :=
    processSpine_wireStateFresh capBlock ⟨List.range bottomCount, [], bottomCount, 0⟩
      (wireStateFresh_initial bottomCount) bottomPositive
  have capEdgesBelow : ∀ edge ∈ capState.links, edge.1 < bottomCount ∧ edge.2 < bottomCount :=
    stringProcessSpine_links_below_ofAllCapArity_seed bottomCount bottomPositive capBlock capPure
  have capEdgesHomog : ∀ edge ∈ capState.links, edgeFloorHomogeneous bottomCount edge :=
    fun edge edgeIn =>
      ⟨fun floorLe => absurd floorLe (Nat.not_le.mpr (capEdgesBelow edge edgeIn).1),
       fun _ => (capEdgesBelow edge edgeIn).2⟩
  have wholeEdgesHomog : ∀ edge ∈ wholeState.links, edgeFloorHomogeneous bottomCount edge :=
    stringProcessSpine_edgesFloorHomogeneous_ofAllCupArity bottomCount cupBlock cupPure capState
      capFresh (Nat.le_of_eq capNextFresh.symm) capEdgesHomog
  have rootBelowFloor : ∀ node, node < bottomCount →
      unionFindRootOf wholeState.links node < bottomCount :=
    fun node nodeBelow =>
      unionFindRootOf_lt_of_edgesBelowFloor wholeState.links bottomCount
        (fun edge edgeIn => (wholeEdgesHomog edge edgeIn).2) node nodeBelow
  have rootAboveFloor : ∀ node, bottomCount ≤ node →
      bottomCount ≤ unionFindRootOf wholeState.links node :=
    fun node nodeAbove =>
      unionFindRootOf_ge_of_edgesPreserveFloor wholeState.links bottomCount
        (fun edge edgeIn => (wholeEdgesHomog edge edgeIn).1) node nodeAbove
  have survivorBelow : ∀ index, index < capState.openWires.length →
      natListGetAt capState.openWires index < bottomCount :=
    fun index indexLt =>
      stringProcessSpine_openWires_below_ofAllCapArity_seed bottomCount bottomPositive capBlock capPure
        (natListGetAt capState.openWires index) (stringGetAtMemOfLt capState.openWires index indexLt)
  exact countBelow_atStrictMonoImage_full_eq_sourceLength
    (sourceLength := capState.openWires.length) (finalLength := wholeState.openWires.length)
    embedding.strictMono
    (fun sourcePos sourceLt =>
      (survivorTop_iff_cupImage bottomCount wholeState capState.openWires (phi sourcePos)
        (embedding.inRange sourcePos sourceLt) rootBelowFloor rootAboveFloor embedding cover
        survivorBelow).mpr ⟨sourcePos, sourceLt, rfl⟩)
    (fun sourcePos sourceLt => embedding.inRange sourcePos sourceLt)
    (fun offset offsetLt noSrc => by
      cases hval : isSurvivorTop (extractDiagram bottomCount wholeState) (bottomCount + offset) with
      | false => rfl
      | true =>
          obtain ⟨sourcePos, sourceLt, phiEq⟩ :=
            (survivorTop_iff_cupImage bottomCount wholeState capState.openWires offset offsetLt
              rootBelowFloor rootAboveFloor embedding cover survivorBelow).mp hval
          exact absurd phiEq (noSrc sourcePos sourceLt))

/-! ## Concrete truth-probe (anti-vacuity) — the genuine mixed string valley `[ε] ++ [η']` at `tip` -/

/-- ★ **The survivor-top-total keystone FIRES on a genuine mixed string valley.**  On the concrete valley
`[ε] ++ [η']` at `tip` from `bottomCount = 2`, the cap `ε` consumes both bottom wires (`midWidth = 0`) and the cup
`η'` adds a fresh top arc, so the whole valley has NO through-strand: the survivor-top total is `0 = midWidth`,
driven end-to-end through the full machinery (`countBelow_add_eq` split, bottom-segment vanish, image cover with
empty image, `countBelow_atStrictMonoImage_full_eq_sourceLength` collapse).  Not vacuous on a real string valley. -/
theorem stringSurvivorTopTotal_eq_midWidth_firesOnMixedValley :
    survivorTopTotal (matchingOfSpineList 2
        ([stringWidthTelescopeProbeCapAtom] ++ [stringWidthTelescopeProbeCupAtom]))
      = (processSpine ⟨List.range 2, [], 2, 0⟩ [stringWidthTelescopeProbeCapAtom]).openWires.length :=
  stringSurvivorTopTotal_eq_midWidth 2 (by decide)
    [stringWidthTelescopeProbeCapAtom] [stringWidthTelescopeProbeCupAtom]
    (AllCapArity.cons rfl rfl AllCapArity.nil) (AllCupArity.cons rfl rfl AllCupArity.nil)
    (SpineBoundaryChained.cons stringWidthTelescopeProbeCupAtom rfl (SpineBoundaryChained.nil 2))

/-- ★ **The mixed-valley survivor-top total is the concrete `0`.**  A machine-checked (`decide`) cross-check that
both sides of the keystone probe compute to `0` — the cap consumes both bottom wires, leaving no survivor-top —
confirming the equation is a genuine numeric fact, not a vacuously-true shape. -/
theorem stringSurvivorTopTotal_mixedValley_isZero :
    survivorTopTotal (matchingOfSpineList 2
        ([stringWidthTelescopeProbeCapAtom] ++ [stringWidthTelescopeProbeCupAtom])) = 0 := by
  decide

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the string survivor-top-total-is-mid-width keystone (M2a) is SHIPPED, zero-axiom.**  Landed
here over the walking ADJOINT-TRIPLE signature:

  * `stringSurvivorTopTotal_eq_midWidth` — for a valley `capBlock ++ cupBlock` (pure cap, pure cup, boundary-chained
    cup) the survivor-top total of the whole valley's `matchingOf` equals the cap block's own open-wire count
    `midWidth`.  The bottom segment `[0, bc)` never survives; over the top offsets the survivor-top predicate marks
    EXACTLY the cup-embedding images (`survivorTop_iff_cupImage`), so
    `countBelow_atStrictMonoImage_full_eq_sourceLength` collapses the count to `midWidth`.  All hypotheses discharged
    from the token-swapped pure-cap seed facts + cup floor-homogeneity + value-cover — no residual.

  * The seed subtree (`stringAtomsFreshTotal_ofAllCapArity` … `stringProcessSpine_openWires_below_ofAllCapArity_seed`,
    `stringProcessSpine_edgesFloorHomogeneous_ofAllCupArity`, `stringProcessSpine_wireOrderImageCover_ofAllCupArity`)
    is the byte-identical token-swap of the walking-adjunction original — the survivor re-ranking reads only wire
    order and the fresh floor, never the `F ≠ H` species distinction.

  The truth-probe fires the whole keystone on a genuine mixed string valley `[ε] ++ [η']` at `tip`
  (`bottomCount = 2`, `midWidth = 0`), and the `decide` cross-check pins both sides to the concrete `0`, so the
  port is not vacuous.

  What this marker does NOT close (honestly), and what `StringMidZeroValleyTraceEquiv`
  (`StringValleyDegenerateSplit`) still needs to inhabit:
    * the two whole-matching-to-block splitters `stringSameWholeMatching_{cap,cup}BlockMatchingEq` (M2c; the cap half
      rides the ~1556-line colour-blind `capRestrict_reconstructs` subtree, still un-cloned);
    * the floor-`0` cup-block reconstruct `StringMidZeroCupBlockReconstruct` (the ~560-line shift-simulation port, M3).

  So `StringMidZeroValleyTraceEquiv` stays UNINHABITED, and `fxString_hasAdjointTripleCompleteness`
  (`StringMatchingCompleteness`) and `fxString_hasConvOfMapEqPortFlip` (`StringConvOfMapEqPort`) stay `false`.  This
  round flips ONLY this NEW marker: M2a is shipped as one brick beneath the mid-zero producer's residuals.  `= true`. -/
def fxString_hasSurvivorTopTotalMidWidth : Bool := true

end FX1Poly.Polygraph
