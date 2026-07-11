import FX1Poly.Polygraph.TwoCategory.WalkingString.StringMatchingPartnerInvolution
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSurvivorTopTotalMidWidth
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyCapTopPartner

/-! # WalkingString/StringValleyCapReconstruct — the cap-side restriction `capRestrict` reconstructs the cap block's
own diagram, over the walking ADJOINT-TRIPLE (`F ⊣ G ⊣ H`) signature (FC-3 r32, B4: the cap-side `DiagramType.ext`
+ the cap-block half of the valley-append split)

The string clone of the walking-adjunction cap-side restriction subtree (`ValleyCapRestrict` /
`ValleyCapConsumedFront` / `ValleyCapTopPartner`).  The B3 involution floor (`stringMatchingOf_partner_isInvolution`
/ `_neSelf`) shipped in r31 and the survivor-top-total leg (`stringSurvivorTopTotal_eq_midWidth`) shipped in r29;
this file lands the four partner legs that CONSUME them and assembles the full `DiagramType.ext`:

  `matchingOf bc capBlock = capRestrict (matchingOf bc (capBlock ++ cupBlock))`

and the cap-block splitter it powers (equal wholes force equal cap blocks).

The reconstruction function `capRestrict`, the `survivorTopTotal` / `nthSurvivorTop` machinery, the front-confinement
helpers (`partnerIndexOf_eq_frontScan_ofFrontNe` / `frontScan_ne_ofPartnerBelow`), the `nthSurvivorTop_correct`
scan-correctness, the partner-in-range plumbing (`matchingOf_partner_below`), and the whole read-off substrate
(`survivorTop_iff_cupImage`, `survivorTop_rankReadoff_ofStrictMono`, `partnerIndexOf_survivor{Unlinked}_eq_rank`,
the union-find floor duals, `diagramType_eq_of_fields`, `natListEqOfPointwiseGetAt`) are signature-BLIND (stated
over bare `WireState` / `DiagramType` or `{signature}`-generic), so they are REUSED verbatim by import.  The seed
facts `processSpine_openWires_unlinked_ofAllCapArity_seed`, `processSpine_fromSeed_wireListDistinct`,
`processSpine_wireStateFresh`, `matchingSwapStateConditions_processSpine`, `spineBoundaryChained_prefix_ofAppend`,
and the generic cup-arity classifier `spineHasCupCapAtoms_ofAllCupArity` are `{signature}`-generic — REUSED too.
So every brick below is a byte-identical token-swap of the walking-adjunction original, rerouting the signature
token alone `adjunctionModeSignature → adjointTripleModeSignature` and the keyed substrate lemmas to their string
ports.  No new mathematics, no unproven residual.

  * `stringProcessSpine_loops_ofAllCupArity` / `stringMatchingOf_loops_split` — the loop leg: a pure-cup block
    never closes a loop, so the whole valley's loop count equals the cap block's own.
  * `stringProcessSpine_preservesArcNodeUnlinked_ofAllCupArity` — a cup block keeps every below-fresh node
    unlinked (the survivor stays unlinked through the cup insertions).
  * `stringProcessSpine_isSameComponent_bottom_ofAllCupArity` — the bottom-bottom component frame: a cup block
    leaves the cap block's bottom-bottom arcs invariant.
  * `stringSpineHasCupCapAtoms_ofAllCapArity` / `stringSpineHasCupCapAtoms_append` — the append arity discipline.
  * `stringCapRestrict_bottomCount_eq` / `stringCapRestrict_loops_eq` — the two COPIED fields agree.
  * `stringCapRestrict_partner_survivorBottom` — the SURVIVOR-BOTTOM partner keystone (cup-shift re-ranking).
  * `stringCapConsumed_partner_agree` — the CAP-CONSUMED partner leg (front-confined bottom-bottom transparency).
  * `stringBottomSurvivor_of_partnerAbove` / `stringCapRestrict_partner_capTop` — the CAP-TOP partner leg via the
    B3 `matchingOf` involution.
  * ★ `stringCapRestrict_reconstructs` — the full `DiagramType.ext`: `matchingOf bc capBlock = capRestrict
    (matchingOf bc (capBlock ++ cupBlock))`.
  * ★ `stringSameWholeMatching_capBlockMatchingEq` — the cap-block half of the valley-append split.

Two truth-probes fire the ext + splitter on the shipped r30 probe valleys: the genuine NON-DEGENERATE WIDE valley
`[ε] ++ [η']` at `bottomCount = 4` (mid-width `2`, cross-checked by the shipped `stringWideProbe_midWidth_isTwo`
`by decide`), and the mid-zero valley at `bottomCount = 2` as the instantiation smoke test.
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; structural recursion on the atom list,
no `WellFounded.fix`; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## New keyed substrate clones (byte-identical token-swap of the walking-adjunction originals) -/

/-- ★ **A pure-cup block preserves the loop count of any processing state.**  Every atom is a cup, so each
`stepAtom` reduces to a `stepCup` (`stepAtom_ofCupArity`), and a cup never closes a loop (`stepCup_loops`).  Folded
over the whole cup block, the loop count is untouched. -/
theorem stringProcessSpine_loops_ofAllCupArity
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (pureCup : AllCupArity atoms) :
    (state : WireState) → (processSpine state atoms).loops = state.loops := by
  induction pureCup with
  | nil => intro state; rfl
  | cons hasCupDomArity hasCupCodArity _restAllCup restLoops =>
      rename_i headAtom rest
      intro state
      show (processSpine (stepAtom state headAtom) rest).loops = state.loops
      rw [restLoops (stepAtom state headAtom),
        stepAtom_ofCupArity state headAtom hasCupDomArity hasCupCodArity, stepCup_loops]

/-- ★ **The LOOP leg of the valley-append split.**  For a valley `capBlock ++ cupBlock` at bottom count `bc` whose
cup block is pure, the whole valley's loop count equals the cap block's loop count.  The fold splits over the append
(`processSpine_append`), and the cup block preserves the loop count
(`stringProcessSpine_loops_ofAllCupArity`). -/
theorem stringMatchingOf_loops_split
    {overallSource overallTarget : adjointTripleGraph.Mode} (bottomCount : Nat)
    (capBlock cupBlock : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (cupPure : AllCupArity cupBlock) :
    (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).loops
      = (matchingOfSpineList bottomCount capBlock).loops := by
  show (processSpine { openWires := List.range bottomCount, links := [], nextFresh := bottomCount, loops := 0 }
        (capBlock ++ cupBlock)).loops
      = (processSpine { openWires := List.range bottomCount, links := [], nextFresh := bottomCount, loops := 0 }
        capBlock).loops
  rw [processSpine_append capBlock cupBlock
    { openWires := List.range bottomCount, links := [], nextFresh := bottomCount, loops := 0 }]
  exact stringProcessSpine_loops_ofAllCupArity cupBlock cupPure
    (processSpine { openWires := List.range bottomCount, links := [], nextFresh := bottomCount, loops := 0 }
      capBlock)

/-- ★ **A pure-cup block keeps every below-fresh node unlinked.**  Each cup step is a `stepCup`
(`stepAtom_ofCupArity`) that preserves unlinkedness of a below-fresh node (`stepCup_preservesArcNodeUnlinked`), and
the node stays below the (only ever raised) `nextFresh`.  So a survivor bottom node, unlinked at the cap-block
mid-state, remains unlinked through the whole cup block. -/
theorem stringProcessSpine_preservesArcNodeUnlinked_ofAllCupArity
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (pureCup : AllCupArity atoms) :
    (state : WireState) → (node : Nat) → node < state.nextFresh →
    ArcNodeUnlinked state.links node →
    ArcNodeUnlinked (processSpine state atoms).links node := by
  induction pureCup with
  | nil => intro _ _ _ unlinked; exact unlinked
  | cons hasCupDomArity hasCupCodArity _restAllCup restIH =>
      rename_i headAtom rest
      intro state node nodeBelowFresh unlinked
      show ArcNodeUnlinked (processSpine (stepAtom state headAtom) rest).links node
      rw [stepAtom_ofCupArity state headAtom hasCupDomArity hasCupCodArity]
      have newUnlinked : ArcNodeUnlinked (stepCup state headAtom.leftContext.length).links node :=
        stepCup_preservesArcNodeUnlinked state headAtom.leftContext.length node nodeBelowFresh unlinked
      have newBelowFresh : node < (stepCup state headAtom.leftContext.length).nextFresh := by
        rw [stepCup_nextFresh]
        exact Nat.lt_of_lt_of_le nodeBelowFresh (Nat.le_add_right state.nextFresh 2)
      exact restIH (stepCup state headAtom.leftContext.length) node newBelowFresh newUnlinked

/-- ★ **The bottom-bottom component frame.**  Run from any conditioned mid-state, a pure-cup block preserves the
same-component relation between any two bottom nodes `< bottomCount`.  Each cup step is a `stepCup`
(`stepAtom_ofCupArity`) that leaves bottom-node connectivity fixed (`stepCup_isSameComponent_bottom`), and the
conditions package is preserved along the fold (`matchingSwapStateConditions_stepAtom`). -/
theorem stringProcessSpine_isSameComponent_bottom_ofAllCupArity
    {overallSource overallTarget : adjointTripleGraph.Mode} (bottomCount : Nat)
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (pureCup : AllCupArity atoms) :
    (state : WireState) → MatchingSwapStateConditions bottomCount state →
    ∀ indexA indexB, indexA < bottomCount → indexB < bottomCount →
      isSameComponent (processSpine state atoms).links indexA indexB
        = isSameComponent state.links indexA indexB := by
  induction pureCup with
  | nil => intro _ _ _ _ _ _; rfl
  | cons hasCupDomArity hasCupCodArity _restAllCup restFrame =>
      rename_i headAtom rest
      intro state conditions indexA indexB aBelow bBelow
      show isSameComponent (processSpine (stepAtom state headAtom) rest).links indexA indexB
        = isSameComponent state.links indexA indexB
      rw [restFrame (stepAtom state headAtom)
          (matchingSwapStateConditions_stepAtom bottomCount state headAtom conditions)
          indexA indexB aBelow bBelow,
        stepAtom_ofCupArity state headAtom hasCupDomArity hasCupCodArity,
        stepCup_isSameComponent_bottom bottomCount state conditions
          headAtom.leftContext.length indexA indexB aBelow bBelow]

/-- A pure-cap block satisfies the generic cup/cap arity discipline (every atom is a cap, the right disjunct). -/
theorem stringSpineHasCupCapAtoms_ofAllCapArity
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (pureCap : AllCapArity atoms) : SpineHasCupCapAtoms atoms := by
  induction pureCap with
  | nil => intro probeAtom probeMem; nomatch probeMem
  | cons hasCapDomArity hasCapCodArity _restAllCap restHas =>
      exact spineHasCupCapAtoms_cons (Or.inr ⟨hasCapDomArity, hasCapCodArity⟩) restHas

/-- A concatenation of two cup/cap-disciplined blocks is cup/cap-disciplined (`SpineHasCupCapAtoms` is a
`∀`-`Mem` predicate; `List.mem_append` split, structural on the prefix). -/
theorem stringSpineHasCupCapAtoms_append
    {overallSource overallTarget : adjointTripleGraph.Mode} :
    (first second : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)) →
    SpineHasCupCapAtoms first → SpineHasCupCapAtoms second →
    SpineHasCupCapAtoms (first ++ second)
  | [], _, _, secondArity => secondArity
  | head :: rest, second, firstArity, secondArity =>
      spineHasCupCapAtoms_cons (firstArity head (List.Mem.head rest))
        (stringSpineHasCupCapAtoms_append rest second
          (fun atom atomMem => firstArity atom (List.Mem.tail head atomMem)) secondArity)

/-! ## The two copied-field agreements -/

/-- ★ **The `bottomCount` field agrees.**  Both the cap block's own diagram and `capRestrict` of the whole valley
carry `bottomCount = bc` — a definitional read of `extractDiagram`'s literal bottom-count field. -/
theorem stringCapRestrict_bottomCount_eq
    {overallSource overallTarget : adjointTripleGraph.Mode} (bottomCount : Nat)
    (capBlock cupBlock : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)) :
    (matchingOfSpineList bottomCount capBlock).bottomCount
      = (capRestrict (matchingOfSpineList bottomCount (capBlock ++ cupBlock))).bottomCount :=
  rfl

/-- ★ **The `loops` field agrees.**  `capRestrict` copies the whole valley's loop count, and cups add no loops
(`stringMatchingOf_loops_split`), so it equals the cap block's own loop count. -/
theorem stringCapRestrict_loops_eq
    {overallSource overallTarget : adjointTripleGraph.Mode} (bottomCount : Nat)
    (capBlock cupBlock : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (cupPure : AllCupArity cupBlock) :
    (matchingOfSpineList bottomCount capBlock).loops
      = (capRestrict (matchingOfSpineList bottomCount (capBlock ++ cupBlock))).loops :=
  (stringMatchingOf_loops_split bottomCount capBlock cupBlock cupPure).symm

/-! ## Private membership plumbing (distinct `SVCR` suffix, keeping the umbrella build's global table duplicate-free
against the walking-adjunction `Local` copies and the r31 `SMPI` copies) -/

/-- An in-range positional read is a member (local copy). -/
private theorem getAtMemOfLtSVCR : (wires : List Nat) → (index : Nat) →
    index < wires.length → natListGetAt wires index ∈ wires
  | [], _, indexInRange => absurd indexInRange (Nat.not_lt_zero _)
  | _ :: _, 0, _ => List.Mem.head _
  | _ :: rest, index + 1, indexInRange =>
      List.Mem.tail _ (getAtMemOfLtSVCR rest index (Nat.lt_of_succ_lt_succ indexInRange))

/-! ## The survivor-bottom partner-field agreement — the arithmetic keystone (prereq #1) -/

/-- ★ **The SURVIVOR-BOTTOM partner-field agreement.**  For a survivor bottom port `survivor` of a valley
`capBlock ++ cupBlock` (a bottom node that survives the cap block, hence a cap-block through-strand), the cap
block's OWN partner of `survivor` equals `capRestrict`'s reconstructed value
`bottomCount + survivorTopRank V (V.partner[survivor])`, where `V = matchingOf bc (capBlock ++ cupBlock)`.  All
three shipped endpoints are routed through ONE cup-embedding `phi` (from
`stringProcessSpine_wireOrderImageCover_ofAllCupArity`), so no coupling residue remains: the cap-alone partner is
`bottomCount + rankCap` (`partnerIndexOf_survivor_eq_rank`), the whole-valley partner is `bottomCount + phi rankCap`
(`partnerIndexOf_survivorUnlinked_eq_rank`), and `survivorTopRank V (bottomCount + phi rankCap) = rankCap`
(`survivorTop_rankReadoff_ofStrictMono`). -/
theorem stringCapRestrict_partner_survivorBottom
    {overallSource overallTarget : adjointTripleGraph.Mode} (bottomCount : Nat)
    (bottomPositive : 0 < bottomCount)
    (capBlock cupBlock : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (capPure : AllCapArity capBlock) (cupPure : AllCupArity cupBlock)
    (capChained : SpineBoundaryChained bottomCount capBlock)
    (cupChained : SpineBoundaryChained
        (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length cupBlock)
    {survivor : Nat}
    (survivorMem : survivor ∈ (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires) :
    natListGetAt (matchingOfSpineList bottomCount capBlock).partner survivor
      = bottomCount + survivorTopRank (matchingOfSpineList bottomCount (capBlock ++ cupBlock))
          (natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner survivor) := by
  let capState := processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock
  let wholeState := processSpine capState cupBlock
  have wholeSplit : matchingOfSpineList bottomCount (capBlock ++ cupBlock)
      = extractDiagram bottomCount wholeState := by
    show extractDiagram bottomCount (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩
        (capBlock ++ cupBlock)) = extractDiagram bottomCount wholeState
    rw [processSpine_append capBlock cupBlock ⟨List.range bottomCount, [], bottomCount, 0⟩]
  have survivorBelow : survivor < bottomCount :=
    stringProcessSpine_openWires_below_ofAllCapArity_seed bottomCount bottomPositive capBlock capPure
      survivor survivorMem
  obtain ⟨rankCap, rankCapLt, survivorAtRankCap⟩ := mem_imp_getAt capState.openWires survivorMem
  have survivorUnlinkedMid : ArcNodeUnlinked capState.links survivor :=
    processSpine_openWires_unlinked_ofAllCapArity_seed bottomCount capBlock capPure capChained
      survivor survivorMem
  have capDistinct : WireListDistinct capState.openWires :=
    processSpine_fromSeed_wireListDistinct bottomCount bottomPositive capBlock
  have capAllUnlinked : ∀ wire ∈ capState.openWires, ArcNodeUnlinked capState.links wire :=
    processSpine_openWires_unlinked_ofAllCapArity_seed bottomCount capBlock capPure capChained
  have capNextFresh : capState.nextFresh = bottomCount :=
    stringProcessSpine_nextFresh_ofAllCapArity_seed bottomCount capBlock capPure
  obtain ⟨phi, embedding, cover⟩ := stringProcessSpine_wireOrderImageCover_ofAllCupArity bottomCount cupBlock cupPure
    capState capState.openWires.length rfl (Nat.le_of_eq capNextFresh.symm) cupChained
  have survivorUnlinkedWhole : ArcNodeUnlinked wholeState.links survivor :=
    stringProcessSpine_preservesArcNodeUnlinked_ofAllCupArity cupBlock cupPure capState survivor
      (by rw [capNextFresh]; exact survivorBelow) survivorUnlinkedMid
  have wholeDistinct : WireListDistinct wholeState.openWires := by
    have base : WireListDistinct
        (processSpine (canonicalMatchingSeed bottomCount) (capBlock ++ cupBlock)).openWires :=
      processSpine_fromSeed_wireListDistinct bottomCount bottomPositive (capBlock ++ cupBlock)
    rw [show canonicalMatchingSeed bottomCount
          = (⟨List.range bottomCount, [], bottomCount, 0⟩ : WireState) from rfl,
      processSpine_append capBlock cupBlock ⟨List.range bottomCount, [], bottomCount, 0⟩] at base
    exact base
  have rankWholeLt : phi rankCap < wholeState.openWires.length := embedding.inRange rankCap rankCapLt
  have survivorAtRankWhole : natListGetAt wholeState.openWires (phi rankCap) = survivor := by
    rw [embedding.reads rankCap rankCapLt, survivorAtRankCap]
  have wholePartnerEq :
      natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner survivor
        = bottomCount + phi rankCap := by
    rw [wholeSplit, extractDiagram_partner_getAt bottomCount wholeState survivor
      (Nat.lt_of_lt_of_le survivorBelow (Nat.le_add_right bottomCount wholeState.openWires.length))]
    exact partnerIndexOf_survivorUnlinked_eq_rank wholeState.links bottomCount wholeState
      survivorBelow survivorUnlinkedWhole wholeDistinct rankWholeLt survivorAtRankWhole
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
  have rankReadoff :
      survivorTopRank (matchingOfSpineList bottomCount (capBlock ++ cupBlock)) (bottomCount + phi rankCap)
        = rankCap := by
    rw [wholeSplit]
    exact survivorTop_rankReadoff_ofStrictMono bottomCount wholeState capState.openWires
      (fun node nodeBelow =>
        unionFindRootOf_lt_of_edgesBelowFloor wholeState.links bottomCount
          (fun edge edgeIn => (wholeEdgesHomog edge edgeIn).2) node nodeBelow)
      (fun node nodeAbove =>
        unionFindRootOf_ge_of_edgesPreserveFloor wholeState.links bottomCount
          (fun edge edgeIn => (wholeEdgesHomog edge edgeIn).1) node nodeAbove)
      embedding cover
      (fun index indexLt =>
        stringProcessSpine_openWires_below_ofAllCapArity_seed bottomCount bottomPositive capBlock capPure
          (natListGetAt capState.openWires index) (getAtMemOfLtSVCR capState.openWires index indexLt))
      rankCapLt
  have capPartnerEq :
      natListGetAt (matchingOfSpineList bottomCount capBlock).partner survivor
        = bottomCount + rankCap := by
    show natListGetAt (extractDiagram bottomCount capState).partner survivor = bottomCount + rankCap
    rw [extractDiagram_partner_getAt bottomCount capState survivor
      (Nat.lt_of_lt_of_le survivorBelow (Nat.le_add_right bottomCount capState.openWires.length))]
    exact partnerIndexOf_survivor_eq_rank capState.links bottomCount capState
      survivorBelow survivorUnlinkedMid capDistinct capAllUnlinked rankCapLt survivorAtRankCap
  rw [capPartnerEq, wholePartnerEq, rankReadoff]

/-! ## The cap-consumed partner agreement (prereq #3) -/

/-- ★ **The cap-consumed partner agreement.**  For a valley `capBlock ++ cupBlock` (pure cup block) and a bottom
port `k < bc` whose whole-valley partner is another bottom (`V.partner[k] < bc`, `≠ k` — a bottom-bottom cap arc),
the cap block's OWN partner of `k` equals the whole valley's partner of `k`.  Both partner reads confine to the
bottom prefix (`partnerIndexOf_eq_frontScan_ofFrontNe` via `frontScan_ne_ofPartnerBelow`), where the whole run and
the cap-alone run agree candidate by candidate — the bottom-bottom connectivity frame
`stringProcessSpine_isSameComponent_bottom_ofAllCupArity` fed through `findPartnerScan_congr_ofTestAgree`. -/
theorem stringCapConsumed_partner_agree
    {overallSource overallTarget : adjointTripleGraph.Mode} (bottomCount : Nat)
    (bottomPositive : 0 < bottomCount)
    (capBlock cupBlock : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (cupPure : AllCupArity cupBlock)
    {consumedPort : Nat} (portBelow : consumedPort < bottomCount)
    (wholePartnerBelow :
      natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner consumedPort < bottomCount)
    (wholePartnerNe :
      natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner consumedPort
        ≠ consumedPort) :
    natListGetAt (matchingOfSpineList bottomCount capBlock).partner consumedPort
      = natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner consumedPort := by
  let capState := processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock
  let wholeState := processSpine capState cupBlock
  have wholeSplit : matchingOfSpineList bottomCount (capBlock ++ cupBlock)
      = extractDiagram bottomCount wholeState := by
    show extractDiagram bottomCount (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩
        (capBlock ++ cupBlock)) = extractDiagram bottomCount wholeState
    rw [processSpine_append capBlock cupBlock ⟨List.range bottomCount, [], bottomCount, 0⟩]
  have capConditions : MatchingSwapStateConditions bottomCount capState :=
    matchingSwapStateConditions_processSpine bottomCount capBlock ⟨List.range bottomCount, [], bottomCount, 0⟩
      (matchingSwapStateConditions_initial bottomCount bottomPositive)
  have capRead : natListGetAt (matchingOfSpineList bottomCount capBlock).partner consumedPort
      = partnerIndexOf capState.links (matchingBoundaryNodes bottomCount capState)
          (bottomCount + capState.openWires.length) consumedPort :=
    extractDiagram_partner_getAt bottomCount capState consumedPort
      (Nat.lt_of_lt_of_le portBelow (Nat.le_add_right bottomCount capState.openWires.length))
  have wholeRead : natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner consumedPort
      = partnerIndexOf wholeState.links (matchingBoundaryNodes bottomCount wholeState)
          (bottomCount + wholeState.openWires.length) consumedPort := by
    rw [wholeSplit]
    exact extractDiagram_partner_getAt bottomCount wholeState consumedPort
      (Nat.lt_of_lt_of_le portBelow (Nat.le_add_right bottomCount wholeState.openWires.length))
  rw [capRead, wholeRead]
  rw [wholeRead] at wholePartnerBelow wholePartnerNe
  have frontWholeNe := frontScan_ne_ofPartnerBelow wholeState.links bottomCount
    wholeState.openWires.length wholeState wholePartnerBelow wholePartnerNe
  have wholeEqFront := partnerIndexOf_eq_frontScan_ofFrontNe wholeState.links bottomCount
    wholeState.openWires.length wholeState frontWholeNe
  have frontsAgree :
      findPartnerScan wholeState.links (matchingBoundaryNodes bottomCount wholeState)
          (unionFindRootOf wholeState.links
            (natListGetAt (matchingBoundaryNodes bottomCount wholeState) consumedPort))
          consumedPort (List.range bottomCount)
        = findPartnerScan capState.links (matchingBoundaryNodes bottomCount capState)
          (unionFindRootOf capState.links
            (natListGetAt (matchingBoundaryNodes bottomCount capState) consumedPort))
          consumedPort (List.range bottomCount) :=
    findPartnerScan_congr_ofTestAgree wholeState.links capState.links
      (matchingBoundaryNodes bottomCount wholeState) (matchingBoundaryNodes bottomCount capState)
      (unionFindRootOf wholeState.links
        (natListGetAt (matchingBoundaryNodes bottomCount wholeState) consumedPort))
      (unionFindRootOf capState.links
        (natListGetAt (matchingBoundaryNodes bottomCount capState) consumedPort))
      consumedPort (List.range bottomCount)
      (fun candidate candidateMem => by
        have candidateBelow : candidate < bottomCount := mem_range_imp_lt candidateMem
        rw [matchingBoundaryNodes_getAt_bottom bottomCount wholeState candidate candidateBelow,
          matchingBoundaryNodes_getAt_bottom bottomCount capState candidate candidateBelow,
          matchingBoundaryNodes_getAt_bottom bottomCount wholeState consumedPort portBelow,
          matchingBoundaryNodes_getAt_bottom bottomCount capState consumedPort portBelow]
        exact congrArg (fun rootMatch => candidate != consumedPort && rootMatch)
          (stringProcessSpine_isSameComponent_bottom_ofAllCupArity bottomCount cupBlock cupPure capState
            capConditions candidate consumedPort candidateBelow portBelow))
  have frontCapNe : findPartnerScan capState.links (matchingBoundaryNodes bottomCount capState)
      (unionFindRootOf capState.links
        (natListGetAt (matchingBoundaryNodes bottomCount capState) consumedPort))
      consumedPort (List.range bottomCount) ≠ consumedPort := by
    rw [← frontsAgree, ← wholeEqFront]
    exact wholePartnerNe
  have capEqFront := partnerIndexOf_eq_frontScan_ofFrontNe capState.links bottomCount
    capState.openWires.length capState frontCapNe
  rw [capEqFront, ← frontsAgree, ← wholeEqFront]

/-! ## Survivor-membership routing (partner-above ⟹ survivor bottom) (prereq #4a) -/

/-- ★ **Survivor-membership routing.**  For a whole valley `capBlock ++ cupBlock` and a bottom port `index < bc`
whose whole-valley partner is a TOP (`bc ≤ V.partner[index]`), `index` is a SURVIVOR — an open wire of the
cap-block mid-state.  Proof via the shipped INVOLUTION (`stringMatchingOf_partner_isInvolution`) and surjectivity:
the partner top port `t = V.partner[index]` is a survivor-top; `survivorTop_iff_cupImage` gives `t = bc + phi s`
for a survivor rank `s`; the survivor `survivor_s` has whole-valley partner `t`
(`partnerIndexOf_survivorUnlinked_eq_rank`), so the involution reflects `V.partner[t] = survivor_s = index`. -/
theorem stringBottomSurvivor_of_partnerAbove
    {overallSource overallTarget : adjointTripleGraph.Mode} (bottomCount : Nat)
    (bottomPositive : 0 < bottomCount)
    (capBlock cupBlock : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (capPure : AllCapArity capBlock) (cupPure : AllCupArity cupBlock)
    (cupChained : SpineBoundaryChained
        (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length cupBlock)
    (wholeChained : SpineBoundaryChained bottomCount (capBlock ++ cupBlock))
    {index : Nat} (indexBelow : index < bottomCount)
    (partnerAbove :
      bottomCount ≤ natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner index) :
    index ∈ (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires := by
  let capState := processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock
  let wholeState := processSpine capState cupBlock
  have capChained : SpineBoundaryChained bottomCount capBlock :=
    spineBoundaryChained_prefix_ofAppend capBlock cupBlock bottomCount wholeChained
  have wholeSplit : matchingOfSpineList bottomCount (capBlock ++ cupBlock)
      = extractDiagram bottomCount wholeState := by
    show extractDiagram bottomCount (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩
        (capBlock ++ cupBlock)) = extractDiagram bottomCount wholeState
    rw [processSpine_append capBlock cupBlock ⟨List.range bottomCount, [], bottomCount, 0⟩]
  have wholeArity : SpineHasCupCapAtoms (capBlock ++ cupBlock) :=
    stringSpineHasCupCapAtoms_append capBlock cupBlock
      (stringSpineHasCupCapAtoms_ofAllCapArity capBlock capPure)
      (spineHasCupCapAtoms_ofAllCupArity cupBlock cupPure)
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
  have rootBelowFloor : ∀ node, node < bottomCount → unionFindRootOf wholeState.links node < bottomCount :=
    fun node nodeBelow =>
      unionFindRootOf_lt_of_edgesBelowFloor wholeState.links bottomCount
        (fun edge edgeIn => (wholeEdgesHomog edge edgeIn).2) node nodeBelow
  have rootAboveFloor : ∀ node, bottomCount ≤ node → bottomCount ≤ unionFindRootOf wholeState.links node :=
    fun node nodeAbove =>
      unionFindRootOf_ge_of_edgesPreserveFloor wholeState.links bottomCount
        (fun edge edgeIn => (wholeEdgesHomog edge edgeIn).1) node nodeAbove
  have survivorBelowAll : ∀ pos, pos < capState.openWires.length →
      natListGetAt capState.openWires pos < bottomCount :=
    fun pos posLt =>
      stringProcessSpine_openWires_below_ofAllCapArity_seed bottomCount bottomPositive capBlock capPure
        (natListGetAt capState.openWires pos) (getAtMemOfLtSVCR capState.openWires pos posLt)
  have wholeDistinct : WireListDistinct wholeState.openWires := by
    have base : WireListDistinct
        (processSpine (canonicalMatchingSeed bottomCount) (capBlock ++ cupBlock)).openWires :=
      processSpine_fromSeed_wireListDistinct bottomCount bottomPositive (capBlock ++ cupBlock)
    rw [show canonicalMatchingSeed bottomCount
          = (⟨List.range bottomCount, [], bottomCount, 0⟩ : WireState) from rfl,
      processSpine_append capBlock cupBlock ⟨List.range bottomCount, [], bottomCount, 0⟩] at base
    exact base
  have partnerInRange : natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner index
      < bottomCount + wholeState.openWires.length := by
    rw [wholeSplit]
    exact matchingOf_partner_below bottomCount wholeState index
      (Nat.lt_of_lt_of_le indexBelow (Nat.le_add_right bottomCount wholeState.openWires.length))
  have notFixedIndex : natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner index
      ≠ index := by
    intro eq
    exact Nat.lt_irrefl bottomCount (Nat.lt_of_le_of_lt (eq ▸ partnerAbove) indexBelow)
  have involIndex := stringMatchingOf_partner_isInvolution bottomCount bottomPositive (capBlock ++ cupBlock)
    wholeArity wholeChained index
    (Nat.lt_of_lt_of_le indexBelow (Nat.le_add_right bottomCount
      (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).topCount))
    notFixedIndex
  obtain ⟨topOffset, topOffsetEq⟩ := Nat.le.dest partnerAbove
  have topOffsetLt : topOffset < wholeState.openWires.length := by
    have := partnerInRange
    rw [← topOffsetEq] at this
    exact Nat.lt_of_add_lt_add_left this
  have partnerAtTop : natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner
      (bottomCount + topOffset) = index := by
    rw [topOffsetEq]; exact involIndex
  have isSurvivorTopValue :
      isSurvivorTop (extractDiagram bottomCount wholeState) (bottomCount + topOffset) = true := by
    show (Nat.ble bottomCount (bottomCount + topOffset)
        && Nat.blt (natListGetAt (extractDiagram bottomCount wholeState).partner (bottomCount + topOffset))
            bottomCount) = true
    have partnerAtTopWhole :
        natListGetAt (extractDiagram bottomCount wholeState).partner (bottomCount + topOffset) = index := by
      rw [← wholeSplit]; exact partnerAtTop
    rw [Nat.ble_eq_true_of_le (Nat.le_add_right bottomCount topOffset), Bool.true_and, partnerAtTopWhole]
    show Nat.blt index bottomCount = true
    exact Nat.ble_eq_true_of_le indexBelow
  obtain ⟨survivorRank, survivorRankLt, phiEq⟩ :=
    (survivorTop_iff_cupImage bottomCount wholeState capState.openWires topOffset topOffsetLt
      rootBelowFloor rootAboveFloor embedding cover survivorBelowAll).mp isSurvivorTopValue
  have survivorMemS : natListGetAt capState.openWires survivorRank ∈ capState.openWires :=
    getAtMemOfLtSVCR capState.openWires survivorRank survivorRankLt
  have survivorBelowS : natListGetAt capState.openWires survivorRank < bottomCount :=
    survivorBelowAll survivorRank survivorRankLt
  have survivorUnlinkedMidS :
      ArcNodeUnlinked capState.links (natListGetAt capState.openWires survivorRank) :=
    processSpine_openWires_unlinked_ofAllCapArity_seed bottomCount capBlock capPure capChained
      (natListGetAt capState.openWires survivorRank) survivorMemS
  have survivorUnlinkedWholeS :
      ArcNodeUnlinked wholeState.links (natListGetAt capState.openWires survivorRank) :=
    stringProcessSpine_preservesArcNodeUnlinked_ofAllCupArity cupBlock cupPure capState
      (natListGetAt capState.openWires survivorRank) (by rw [capNextFresh]; exact survivorBelowS)
      survivorUnlinkedMidS
  have survivorAtRankWholeS :
      natListGetAt wholeState.openWires (phi survivorRank) = natListGetAt capState.openWires survivorRank := by
    rw [embedding.reads survivorRank survivorRankLt]
  have sPartnerEq : natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner
      (natListGetAt capState.openWires survivorRank) = bottomCount + phi survivorRank := by
    rw [wholeSplit, extractDiagram_partner_getAt bottomCount wholeState
      (natListGetAt capState.openWires survivorRank)
      (Nat.lt_of_lt_of_le survivorBelowS (Nat.le_add_right bottomCount wholeState.openWires.length))]
    exact partnerIndexOf_survivorUnlinked_eq_rank wholeState.links bottomCount wholeState
      survivorBelowS survivorUnlinkedWholeS wholeDistinct (embedding.inRange survivorRank survivorRankLt)
      survivorAtRankWholeS
  have notFixedS : natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner
      (natListGetAt capState.openWires survivorRank) ≠ natListGetAt capState.openWires survivorRank := by
    rw [sPartnerEq]
    intro eq
    exact Nat.lt_irrefl _
      (eq ▸ Nat.lt_of_lt_of_le survivorBelowS (Nat.le_add_right bottomCount (phi survivorRank)))
  have involS := stringMatchingOf_partner_isInvolution bottomCount bottomPositive (capBlock ++ cupBlock)
    wholeArity wholeChained (natListGetAt capState.openWires survivorRank)
    (Nat.lt_of_lt_of_le survivorBelowS (Nat.le_add_right bottomCount
      (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).topCount))
    notFixedS
  rw [sPartnerEq] at involS
  have topCollapse : bottomCount + phi survivorRank = bottomCount + topOffset :=
    congrArg (bottomCount + ·) phiEq
  rw [topCollapse, partnerAtTop] at involS
  rw [involS]
  exact survivorMemS

/-! ## The cap-TOP partner-field agreement (prereq #4b) -/

/-- ★ **The CAP-TOP partner-field agreement.**  For a cap-TOP port `bottomCount + rankCap`
(`rankCap < midWidth = capState.openWires.length`), the cap block's OWN partner equals `capRestrict`'s
reconstructed value `V.partner[nthSurvivorTop V rankCap]`.  Both sides equal the `rankCap`-th survivor bottom: the
cap-alone INVOLUTION reflects the survivor's cap-alone partner `bottomCount + rankCap`, and
`nthSurvivorTop V rankCap = bottomCount + phi rankCap` (`nthSurvivorTop_correct`) + the whole-valley INVOLUTION
reflects the survivor's whole-valley partner `bottomCount + phi rankCap`. -/
theorem stringCapRestrict_partner_capTop
    {overallSource overallTarget : adjointTripleGraph.Mode} (bottomCount : Nat)
    (bottomPositive : 0 < bottomCount)
    (capBlock cupBlock : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (capPure : AllCapArity capBlock) (cupPure : AllCupArity cupBlock)
    (cupChained : SpineBoundaryChained
        (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length cupBlock)
    (wholeChained : SpineBoundaryChained bottomCount (capBlock ++ cupBlock))
    {rankCap : Nat}
    (rankCapLt : rankCap < (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length) :
    natListGetAt (matchingOfSpineList bottomCount capBlock).partner (bottomCount + rankCap)
      = natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner
          (nthSurvivorTop (matchingOfSpineList bottomCount (capBlock ++ cupBlock)) rankCap) := by
  let capState := processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock
  let wholeState := processSpine capState cupBlock
  have capChained : SpineBoundaryChained bottomCount capBlock :=
    spineBoundaryChained_prefix_ofAppend capBlock cupBlock bottomCount wholeChained
  have wholeSplit : matchingOfSpineList bottomCount (capBlock ++ cupBlock)
      = extractDiagram bottomCount wholeState := by
    show extractDiagram bottomCount (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩
        (capBlock ++ cupBlock)) = extractDiagram bottomCount wholeState
    rw [processSpine_append capBlock cupBlock ⟨List.range bottomCount, [], bottomCount, 0⟩]
  have survivorMem : natListGetAt capState.openWires rankCap ∈ capState.openWires :=
    getAtMemOfLtSVCR capState.openWires rankCap rankCapLt
  have survivorBelowSelf : natListGetAt capState.openWires rankCap < bottomCount :=
    stringProcessSpine_openWires_below_ofAllCapArity_seed bottomCount bottomPositive capBlock capPure
      (natListGetAt capState.openWires rankCap) survivorMem
  have survivorUnlinkedMid : ArcNodeUnlinked capState.links (natListGetAt capState.openWires rankCap) :=
    processSpine_openWires_unlinked_ofAllCapArity_seed bottomCount capBlock capPure capChained
      (natListGetAt capState.openWires rankCap) survivorMem
  have capDistinct : WireListDistinct capState.openWires :=
    processSpine_fromSeed_wireListDistinct bottomCount bottomPositive capBlock
  have capAllUnlinked : ∀ wire ∈ capState.openWires, ArcNodeUnlinked capState.links wire :=
    processSpine_openWires_unlinked_ofAllCapArity_seed bottomCount capBlock capPure capChained
  have capNextFresh : capState.nextFresh = bottomCount :=
    stringProcessSpine_nextFresh_ofAllCapArity_seed bottomCount capBlock capPure
  obtain ⟨phi, embedding, cover⟩ := stringProcessSpine_wireOrderImageCover_ofAllCupArity bottomCount cupBlock cupPure
    capState capState.openWires.length rfl (Nat.le_of_eq capNextFresh.symm) cupChained
  have survivorUnlinkedWhole : ArcNodeUnlinked wholeState.links (natListGetAt capState.openWires rankCap) :=
    stringProcessSpine_preservesArcNodeUnlinked_ofAllCupArity cupBlock cupPure capState
      (natListGetAt capState.openWires rankCap) (by rw [capNextFresh]; exact survivorBelowSelf)
      survivorUnlinkedMid
  have wholeDistinct : WireListDistinct wholeState.openWires := by
    have base : WireListDistinct
        (processSpine (canonicalMatchingSeed bottomCount) (capBlock ++ cupBlock)).openWires :=
      processSpine_fromSeed_wireListDistinct bottomCount bottomPositive (capBlock ++ cupBlock)
    rw [show canonicalMatchingSeed bottomCount
          = (⟨List.range bottomCount, [], bottomCount, 0⟩ : WireState) from rfl,
      processSpine_append capBlock cupBlock ⟨List.range bottomCount, [], bottomCount, 0⟩] at base
    exact base
  have rankWholeLt : phi rankCap < wholeState.openWires.length := embedding.inRange rankCap rankCapLt
  have survivorAtRankWhole :
      natListGetAt wholeState.openWires (phi rankCap) = natListGetAt capState.openWires rankCap := by
    rw [embedding.reads rankCap rankCapLt]
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
  have rootBelowFloor : ∀ node, node < bottomCount → unionFindRootOf wholeState.links node < bottomCount :=
    fun node nodeBelow =>
      unionFindRootOf_lt_of_edgesBelowFloor wholeState.links bottomCount
        (fun edge edgeIn => (wholeEdgesHomog edge edgeIn).2) node nodeBelow
  have rootAboveFloor : ∀ node, bottomCount ≤ node → bottomCount ≤ unionFindRootOf wholeState.links node :=
    fun node nodeAbove =>
      unionFindRootOf_ge_of_edgesPreserveFloor wholeState.links bottomCount
        (fun edge edgeIn => (wholeEdgesHomog edge edgeIn).1) node nodeAbove
  have survivorBelowAll : ∀ index, index < capState.openWires.length →
      natListGetAt capState.openWires index < bottomCount :=
    fun index indexLt =>
      stringProcessSpine_openWires_below_ofAllCapArity_seed bottomCount bottomPositive capBlock capPure
        (natListGetAt capState.openWires index) (getAtMemOfLtSVCR capState.openWires index indexLt)
  have wholePartnerEq :
      natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner
          (natListGetAt capState.openWires rankCap)
        = bottomCount + phi rankCap := by
    rw [wholeSplit, extractDiagram_partner_getAt bottomCount wholeState
      (natListGetAt capState.openWires rankCap)
      (Nat.lt_of_lt_of_le survivorBelowSelf (Nat.le_add_right bottomCount wholeState.openWires.length))]
    exact partnerIndexOf_survivorUnlinked_eq_rank wholeState.links bottomCount wholeState
      survivorBelowSelf survivorUnlinkedWhole wholeDistinct rankWholeLt survivorAtRankWhole
  have capPartnerEq :
      natListGetAt (matchingOfSpineList bottomCount capBlock).partner
          (natListGetAt capState.openWires rankCap)
        = bottomCount + rankCap := by
    show natListGetAt (extractDiagram bottomCount capState).partner
        (natListGetAt capState.openWires rankCap) = bottomCount + rankCap
    rw [extractDiagram_partner_getAt bottomCount capState (natListGetAt capState.openWires rankCap)
      (Nat.lt_of_lt_of_le survivorBelowSelf (Nat.le_add_right bottomCount capState.openWires.length))]
    exact partnerIndexOf_survivor_eq_rank capState.links bottomCount capState
      survivorBelowSelf survivorUnlinkedMid capDistinct capAllUnlinked rankCapLt rfl
  have notFixedCap :
      natListGetAt (matchingOfSpineList bottomCount capBlock).partner
          (natListGetAt capState.openWires rankCap)
        ≠ natListGetAt capState.openWires rankCap := by
    rw [capPartnerEq]
    intro eq
    exact Nat.lt_irrefl _
      (eq ▸ Nat.lt_of_lt_of_le survivorBelowSelf (Nat.le_add_right bottomCount rankCap))
  have legA :
      natListGetAt (matchingOfSpineList bottomCount capBlock).partner (bottomCount + rankCap)
        = natListGetAt capState.openWires rankCap := by
    have invol := stringMatchingOf_partner_isInvolution bottomCount bottomPositive capBlock
      (stringSpineHasCupCapAtoms_ofAllCapArity capBlock capPure) capChained
      (natListGetAt capState.openWires rankCap)
      (Nat.lt_of_lt_of_le survivorBelowSelf
        (Nat.le_add_right bottomCount (matchingOfSpineList bottomCount capBlock).topCount))
      notFixedCap
    rw [capPartnerEq] at invol
    exact invol
  have nthEq :
      nthSurvivorTop (matchingOfSpineList bottomCount (capBlock ++ cupBlock)) rankCap
        = bottomCount + phi rankCap := by
    rw [wholeSplit]
    exact nthSurvivorTop_correct bottomCount wholeState capState.openWires rootBelowFloor rootAboveFloor
      embedding cover survivorBelowAll rankCapLt
  have notFixedWhole :
      natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner
          (natListGetAt capState.openWires rankCap)
        ≠ natListGetAt capState.openWires rankCap := by
    rw [wholePartnerEq]
    intro eq
    exact Nat.lt_irrefl _
      (eq ▸ Nat.lt_of_lt_of_le survivorBelowSelf (Nat.le_add_right bottomCount (phi rankCap)))
  have involWhole := stringMatchingOf_partner_isInvolution bottomCount bottomPositive (capBlock ++ cupBlock)
    (stringSpineHasCupCapAtoms_append capBlock cupBlock
      (stringSpineHasCupCapAtoms_ofAllCapArity capBlock capPure)
      (spineHasCupCapAtoms_ofAllCupArity cupBlock cupPure))
    wholeChained (natListGetAt capState.openWires rankCap)
    (Nat.lt_of_lt_of_le survivorBelowSelf
      (Nat.le_add_right bottomCount (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).topCount))
    notFixedWhole
  rw [wholePartnerEq] at involWhole
  rw [legA, nthEq, involWhole]

/-! ## Private range / map plumbing (distinct `SVCR` suffix, propext-free copies) -/

private theorem rangeLoopLengthSVCR : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := rangeLoopLengthSVCR count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1, Nat.add_right_comm count accumulated.length 1]

private theorem rangeLengthSVCR (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [rangeLoopLengthSVCR count []]
  exact Nat.add_zero count

private theorem rangeLoopGetAtPastSVCR : (count : Nat) → (accumulated : List Nat) → (offset : Nat) →
    natListGetAt (List.range.loop count accumulated) (offset + count) = natListGetAt accumulated offset
  | 0, _, _ => rfl
  | count + 1, accumulated, offset => by
      have inner := rangeLoopGetAtPastSVCR count (count :: accumulated) (offset + 1)
      rw [Nat.add_assoc offset 1 count, Nat.add_comm 1 count] at inner
      exact inner

private theorem rangeLoopGetAtBelowSVCR : (count : Nat) → (accumulated : List Nat) →
    (index : Nat) → index < count →
    natListGetAt (List.range.loop count accumulated) index = index
  | 0, _, _, indexBelow => absurd indexBelow (Nat.not_succ_le_zero _)
  | count + 1, accumulated, index, indexBelow => by
      cases Nat.lt_or_ge index count with
      | inl below => exact rangeLoopGetAtBelowSVCR count (count :: accumulated) index below
      | inr atLeast =>
          have indexEq : index = count := Nat.le_antisymm (Nat.le_of_succ_le_succ indexBelow) atLeast
          have pastRead := rangeLoopGetAtPastSVCR count (count :: accumulated) 0
          rw [Nat.zero_add count] at pastRead
          rw [indexEq]
          exact pastRead

private theorem rangeGetAtBelowSVCR (count index : Nat) (indexBelow : index < count) :
    natListGetAt (List.range count) index = index :=
  rangeLoopGetAtBelowSVCR count [] index indexBelow

private theorem listMapLenSVCR {carrier : Type} (mapFn : Nat → carrier) :
    (values : List Nat) → (values.map mapFn).length = values.length
  | [] => rfl
  | _ :: rest => congrArg (· + 1) (listMapLenSVCR mapFn rest)

/-- `base + (extra - base) = extra` for `base ≤ extra` (hand-rolled; `Nat.add_sub_cancel'` leaks `propext`). -/
private theorem addSubCancelSVCR : (base extra : Nat) → base ≤ extra → base + (extra - base) = extra
  | 0, extra, _ => by rw [Nat.zero_add, Nat.sub_zero]
  | base + 1, 0, atMost => absurd atMost (Nat.not_succ_le_zero base)
  | base + 1, extra + 1, atMost => by
      have inner := addSubCancelSVCR base extra (Nat.le_of_succ_le_succ atMost)
      rw [Nat.succ_sub_succ, Nat.succ_add, inner]

private theorem bltTrueOfLtSVCR {smaller larger : Nat} (isLess : smaller < larger) :
    Nat.blt smaller larger = true := Nat.ble_eq_true_of_le isLess

private theorem bltFalseOfGeSVCR {value bound : Nat} (isGe : bound ≤ value) :
    Nat.blt value bound = false := by
  cases probe : Nat.blt value bound with
  | false => rfl
  | true =>
      exact absurd (Nat.lt_of_lt_of_le (Nat.le_of_ble_eq_true probe) isGe) (Nat.lt_irrefl value)

private theorem neTrueOfEqFalseSVCR {flag : Bool} (isFalse : flag = false) : ¬ (flag = true) :=
  fun isTrue => Bool.noConfusion (isFalse.symm.trans isTrue)

/-! ## The cap-side reconstruction — the full `DiagramType.ext` -/

/-- ★ **The cap-side reconstruction (F-assembly).**  The cap block's OWN diagram is `capRestrict` of the whole
valley's diagram: `matchingOf bc capBlock = capRestrict (matchingOf bc (capBlock ++ cupBlock))`.  Componentwise via
`diagramType_eq_of_fields`: `bottomCount` copies (`rfl`), `topCount` is the survivor-top total
(`stringSurvivorTopTotal_eq_midWidth`), `loops` copies (`stringCapRestrict_loops_eq`), and the `partner` list agrees
pointwise (`natListEqOfPointwiseGetAt`) by the three shipped partner cases —
cap-consumed (`stringCapConsumed_partner_agree`), survivor-bottom (`stringCapRestrict_partner_survivorBottom` routed
through `stringBottomSurvivor_of_partnerAbove`), and cap-top (`stringCapRestrict_partner_capTop`). -/
theorem stringCapRestrict_reconstructs
    {overallSource overallTarget : adjointTripleGraph.Mode} (bottomCount : Nat)
    (bottomPositive : 0 < bottomCount)
    (capBlock cupBlock : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (capPure : AllCapArity capBlock) (cupPure : AllCupArity cupBlock)
    (cupChained : SpineBoundaryChained
        (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock).openWires.length cupBlock)
    (wholeChained : SpineBoundaryChained bottomCount (capBlock ++ cupBlock)) :
    matchingOfSpineList bottomCount capBlock
      = capRestrict (matchingOfSpineList bottomCount (capBlock ++ cupBlock)) := by
  let capState := processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlock
  have capChained : SpineBoundaryChained bottomCount capBlock :=
    spineBoundaryChained_prefix_ofAppend capBlock cupBlock bottomCount wholeChained
  have wholeArity : SpineHasCupCapAtoms (capBlock ++ cupBlock) :=
    stringSpineHasCupCapAtoms_append capBlock cupBlock
      (stringSpineHasCupCapAtoms_ofAllCapArity capBlock capPure)
      (spineHasCupCapAtoms_ofAllCupArity cupBlock cupPure)
  have midEq : survivorTopTotal (matchingOfSpineList bottomCount (capBlock ++ cupBlock))
      = capState.openWires.length :=
    stringSurvivorTopTotal_eq_midWidth bottomCount bottomPositive capBlock cupBlock capPure cupPure cupChained
  apply diagramType_eq_of_fields
  · rfl
  · exact midEq.symm
  · apply natListEqOfPointwiseGetAt
    · show ((List.range (bottomCount + capState.openWires.length)).map
          (partnerIndexOf capState.links (matchingBoundaryNodes bottomCount capState)
            (bottomCount + capState.openWires.length))).length
        = ((List.range (bottomCount
            + survivorTopTotal (matchingOfSpineList bottomCount (capBlock ++ cupBlock)))).map _).length
      rw [listMapLenSVCR, listMapLenSVCR, rangeLengthSVCR, rangeLengthSVCR, midEq]
    · intro index indexRaw
      have indexLt : index < bottomCount + capState.openWires.length := by
        have lenLHS : (matchingOfSpineList bottomCount capBlock).partner.length
            = bottomCount + capState.openWires.length := by
          show ((List.range (bottomCount + capState.openWires.length)).map
              (partnerIndexOf capState.links (matchingBoundaryNodes bottomCount capState)
                (bottomCount + capState.openWires.length))).length
            = bottomCount + capState.openWires.length
          rw [listMapLenSVCR, rangeLengthSVCR]
        rw [lenLHS] at indexRaw
        exact indexRaw
      have indexLtRHS : index < bottomCount
          + survivorTopTotal (matchingOfSpineList bottomCount (capBlock ++ cupBlock)) := by
        rw [midEq]; exact indexLt
      have mapRead : natListGetAt
            (capRestrict (matchingOfSpineList bottomCount (capBlock ++ cupBlock))).partner index
          = (if Nat.blt index bottomCount then
              (if Nat.blt (natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner index)
                    bottomCount
                then natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner index
                else bottomCount + survivorTopRank (matchingOfSpineList bottomCount (capBlock ++ cupBlock))
                       (natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner index))
            else natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner
                   (nthSurvivorTop (matchingOfSpineList bottomCount (capBlock ++ cupBlock))
                     (index - bottomCount))) := by
        show natListGetAt ((List.range (bottomCount
              + survivorTopTotal (matchingOfSpineList bottomCount (capBlock ++ cupBlock)))).map
            (fun idx =>
              if Nat.blt idx bottomCount then
                (if Nat.blt (natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner idx)
                      bottomCount
                  then natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner idx
                  else bottomCount + survivorTopRank (matchingOfSpineList bottomCount (capBlock ++ cupBlock))
                         (natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner idx))
              else natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner
                     (nthSurvivorTop (matchingOfSpineList bottomCount (capBlock ++ cupBlock))
                       (idx - bottomCount)))) index = _
        rw [natListGetAt_map_inRange _ _ index (by rw [rangeLengthSVCR]; exact indexLtRHS),
          rangeGetAtBelowSVCR _ index indexLtRHS]
      rw [mapRead]
      rcases Nat.lt_or_ge index bottomCount with indexBelow | indexAtLeast
      · rw [if_pos (bltTrueOfLtSVCR indexBelow)]
        rcases Nat.lt_or_ge
            (natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner index)
            bottomCount with wpBelow | wpAbove
        · rw [if_pos (bltTrueOfLtSVCR wpBelow)]
          have wpNe :
              natListGetAt (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).partner index ≠ index :=
            stringMatchingOf_partner_neSelf bottomCount bottomPositive (capBlock ++ cupBlock) wholeArity
              wholeChained index
              (Nat.lt_of_lt_of_le indexBelow (Nat.le_add_right bottomCount
                (matchingOfSpineList bottomCount (capBlock ++ cupBlock)).topCount))
          exact stringCapConsumed_partner_agree bottomCount bottomPositive capBlock cupBlock cupPure
            indexBelow wpBelow wpNe
        · rw [if_neg (neTrueOfEqFalseSVCR (bltFalseOfGeSVCR wpAbove))]
          have survivorMem : index ∈ capState.openWires :=
            stringBottomSurvivor_of_partnerAbove bottomCount bottomPositive capBlock cupBlock capPure cupPure
              cupChained wholeChained indexBelow wpAbove
          exact stringCapRestrict_partner_survivorBottom bottomCount bottomPositive capBlock cupBlock capPure
            cupPure capChained cupChained survivorMem
      · rw [if_neg (neTrueOfEqFalseSVCR (bltFalseOfGeSVCR indexAtLeast))]
        have idxEq : bottomCount + (index - bottomCount) = index :=
          addSubCancelSVCR bottomCount index indexAtLeast
        have rLt : index - bottomCount < capState.openWires.length := by
          have step : bottomCount + (index - bottomCount) < bottomCount + capState.openWires.length := by
            rw [idxEq]; exact indexLt
          exact Nat.lt_of_add_lt_add_left step
        have capTop := stringCapRestrict_partner_capTop bottomCount bottomPositive capBlock cupBlock capPure
          cupPure cupChained wholeChained rLt
        rw [idxEq] at capTop
        exact capTop
  · exact stringCapRestrict_loops_eq bottomCount capBlock cupBlock cupPure

/-! ## The cap half of the valley-append split — derived, no longer a hypothesis -/

/-- ★ **The cap-block half of the valley-append split.**  Two valleys `capBlock ++ cupBlock` with EQUAL whole
`matchingOf` have EQUAL cap-block `matchingOf`.  Derived — not assumed — by `congrArg capRestrict` over the whole
equality, sandwiched between the two `stringCapRestrict_reconstructs` field agreements: the cap block's own diagram
is a FUNCTION (`capRestrict`) of the whole valley's diagram, so equal wholes force equal cap blocks. -/
theorem stringSameWholeMatching_capBlockMatchingEq
    {overallSource overallTarget : adjointTripleGraph.Mode} (bottomCount : Nat)
    (bottomPositive : 0 < bottomCount)
    (capBlockFirst capBlockSecond cupBlockFirst cupBlockSecond :
      List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (capPureFirst : AllCapArity capBlockFirst) (capPureSecond : AllCapArity capBlockSecond)
    (cupPureFirst : AllCupArity cupBlockFirst) (cupPureSecond : AllCupArity cupBlockSecond)
    (cupChainedFirst : SpineBoundaryChained
        (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockFirst).openWires.length cupBlockFirst)
    (cupChainedSecond : SpineBoundaryChained
        (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capBlockSecond).openWires.length cupBlockSecond)
    (wholeChainedFirst : SpineBoundaryChained bottomCount (capBlockFirst ++ cupBlockFirst))
    (wholeChainedSecond : SpineBoundaryChained bottomCount (capBlockSecond ++ cupBlockSecond))
    (wholeEq : matchingOfSpineList bottomCount (capBlockFirst ++ cupBlockFirst)
      = matchingOfSpineList bottomCount (capBlockSecond ++ cupBlockSecond)) :
    matchingOfSpineList bottomCount capBlockFirst = matchingOfSpineList bottomCount capBlockSecond :=
  (stringCapRestrict_reconstructs bottomCount bottomPositive capBlockFirst cupBlockFirst capPureFirst cupPureFirst
      cupChainedFirst wholeChainedFirst).trans
    ((congrArg capRestrict wholeEq).trans
      (stringCapRestrict_reconstructs bottomCount bottomPositive capBlockSecond cupBlockSecond capPureSecond
        cupPureSecond cupChainedSecond wholeChainedSecond).symm)

/-! ## Concrete truth-probes — the ext + splitter FIRE on the shipped r30 probe valleys -/

/-- The wide cap block `[ε]` at `bottomCount = 4` is pure-cap: `stringGF` domain (length `2`), `id_tip` codomain
(length `0`). -/
theorem stringWideProbeCapBlock_pureCap : AllCapArity [stringWideProbeCapAtom] :=
  AllCapArity.cons rfl rfl AllCapArity.nil

/-- The wide cup block `[η']` at `bottomCount = 4` is pure-cup: `id_tip` domain (length `0`), `stringGH` codomain
(length `2`). -/
theorem stringWideProbeCupBlock_pureCup : AllCupArity [stringWideProbeCupAtom] :=
  AllCupArity.cons rfl rfl AllCupArity.nil

/-- The wide cup block is boundary-chained at the cap block's `processSpine` mid-width (`2`): the cup fires at
width `2`.  The `rfl` discharges `stringWideProbeCupAtom.domBoundaryLength = 2 = (processSpine ⟨range 4, …⟩ [ε])
.openWires.length` — the same numeric mid-width the shipped `stringWideProbe_midWidth_isTwo` cross-checks. -/
theorem stringWideProbeCupBlock_chained :
    SpineBoundaryChained
      (processSpine ⟨List.range 4, [], 4, 0⟩ [stringWideProbeCapAtom]).openWires.length
      [stringWideProbeCupAtom] :=
  SpineBoundaryChained.cons stringWideProbeCupAtom rfl (SpineBoundaryChained.nil _)

/-- ★ **The cap-side reconstruction FIRES on the genuine non-degenerate wide valley.**  On the concrete valley
`[ε] ++ [η']` at `bottomCount = 4` (mid-width `2`, `stringWideProbe_midWidth_isTwo`), the cap block's OWN diagram is
`capRestrict` of the whole valley's diagram — a real inhabitation over a valley with non-zero mid content, NOT
vacuous. -/
theorem stringCapRestrict_reconstructs_firesOnWideValley :
    matchingOfSpineList 4 [stringWideProbeCapAtom]
      = capRestrict (matchingOfSpineList 4 ([stringWideProbeCapAtom] ++ [stringWideProbeCupAtom])) :=
  stringCapRestrict_reconstructs 4 (by decide) [stringWideProbeCapAtom] [stringWideProbeCupAtom]
    stringWideProbeCapBlock_pureCap stringWideProbeCupBlock_pureCup
    stringWideProbeCupBlock_chained stringWideProbeValley_chained

/-- ★ **The cap-block splitter FIRES on the genuine non-degenerate wide valley (reflexive instance).**  Two copies
of the wide valley with equal whole `matchingOf` (`rfl`) force equal cap-block `matchingOf` — the splitter machinery
driven end-to-end through `capRestrict_reconstructs` twice on a non-zero-mid valley. -/
theorem stringSameWholeMatching_capBlockMatchingEq_firesOnWideValley :
    matchingOfSpineList 4 [stringWideProbeCapAtom] = matchingOfSpineList 4 [stringWideProbeCapAtom] :=
  stringSameWholeMatching_capBlockMatchingEq 4 (by decide)
    [stringWideProbeCapAtom] [stringWideProbeCapAtom] [stringWideProbeCupAtom] [stringWideProbeCupAtom]
    stringWideProbeCapBlock_pureCap stringWideProbeCapBlock_pureCap
    stringWideProbeCupBlock_pureCup stringWideProbeCupBlock_pureCup
    stringWideProbeCupBlock_chained stringWideProbeCupBlock_chained
    stringWideProbeValley_chained stringWideProbeValley_chained rfl

/-- The mid-zero cap block `[ε]` at `bottomCount = 2` is pure-cap. -/
theorem stringMidZeroProbeCapBlock_pureCap : AllCapArity [stringWidthTelescopeProbeCapAtom] :=
  AllCapArity.cons rfl rfl AllCapArity.nil

/-- The mid-zero cup block `[η']` at `bottomCount = 2` is pure-cup. -/
theorem stringMidZeroProbeCupBlock_pureCup : AllCupArity [stringWidthTelescopeProbeCupAtom] :=
  AllCupArity.cons rfl rfl AllCupArity.nil

/-- The mid-zero cup block is boundary-chained at the cap block's `processSpine` mid-width (`0`). -/
theorem stringMidZeroProbeCupBlock_chained :
    SpineBoundaryChained
      (processSpine ⟨List.range 2, [], 2, 0⟩ [stringWidthTelescopeProbeCapAtom]).openWires.length
      [stringWidthTelescopeProbeCupAtom] :=
  SpineBoundaryChained.cons stringWidthTelescopeProbeCupAtom rfl (SpineBoundaryChained.nil _)

/-- ★ **The cap-side reconstruction smoke-fires on the mid-zero valley.**  The empty-context valley `[ε] ++ [η']`
at `bottomCount = 2` instantiates the ext end-to-end — the cheap "does it instantiate" check. -/
theorem stringCapRestrict_reconstructs_firesOnMidZeroValley :
    matchingOfSpineList 2 [stringWidthTelescopeProbeCapAtom]
      = capRestrict (matchingOfSpineList 2
          ([stringWidthTelescopeProbeCapAtom] ++ [stringWidthTelescopeProbeCupAtom])) :=
  stringCapRestrict_reconstructs 2 (by decide)
    [stringWidthTelescopeProbeCapAtom] [stringWidthTelescopeProbeCupAtom]
    stringMidZeroProbeCapBlock_pureCap stringMidZeroProbeCupBlock_pureCup
    stringMidZeroProbeCupBlock_chained stringMidZeroProbeValley_chained

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the string cap-side restriction `capRestrict` RECONSTRUCTS the cap block's own diagram, and
the cap-block splitter is SHIPPED, zero-axiom (FC-3 r32, B4).**  Landed here over the walking ADJOINT-TRIPLE
signature, consuming the r31 involution floor (`stringMatchingOf_partner_isInvolution` / `_neSelf`) and the r29
survivor-top-total leg (`stringSurvivorTopTotal_eq_midWidth`):

  * the four partner legs — `stringCapRestrict_partner_survivorBottom` (cup-shift re-ranking keystone),
    `stringCapConsumed_partner_agree` (front-confined bottom-bottom transparency),
    `stringBottomSurvivor_of_partnerAbove` + `stringCapRestrict_partner_capTop` (the involution-consuming cap-top
    leg) — plus the two copied fields (`stringCapRestrict_bottomCount_eq` / `stringCapRestrict_loops_eq`);
  * ★ `stringCapRestrict_reconstructs` — the full `DiagramType.ext`: `matchingOf bc capBlock = capRestrict
    (matchingOf bc (capBlock ++ cupBlock))`, componentwise via `diagramType_eq_of_fields` + the three partner cases;
  * ★ `stringSameWholeMatching_capBlockMatchingEq` — the cap-block half of the valley-append split (equal wholes
    force equal cap blocks).

  The reconstruction function `capRestrict`, `survivorTopTotal` / `nthSurvivorTop` + `nthSurvivorTop_correct`, the
  front-confinement helpers, `matchingOf_partner_below`, and the whole read-off substrate are signature-BLIND — all
  REUSED verbatim by import.  The seed facts `processSpine_openWires_unlinked_ofAllCapArity_seed` /
  `processSpine_fromSeed_wireListDistinct` / `processSpine_wireStateFresh` /
  `matchingSwapStateConditions_processSpine` / `spineBoundaryChained_prefix_ofAppend` and the generic cup classifier
  `spineHasCupCapAtoms_ofAllCupArity` are `{signature}`-generic — REUSED.  The five newly-cloned keyed substrate
  lemmas (`stringProcessSpine_loops_ofAllCupArity` / `stringMatchingOf_loops_split` /
  `stringProcessSpine_preservesArcNodeUnlinked_ofAllCupArity` /
  `stringProcessSpine_isSameComponent_bottom_ofAllCupArity` / `stringSpineHasCupCapAtoms_ofAllCapArity` /
  `stringSpineHasCupCapAtoms_append`) are byte-identical token-swaps of the walking-adjunction originals — no new
  mathematics, no unproven residual.

  Two truth-probes fire the ext + splitter end-to-end: the genuine NON-DEGENERATE WIDE valley `[ε] ++ [η']` at
  `bottomCount = 4` (mid-width `2`, cross-checked by the shipped `stringWideProbe_midWidth_isTwo` `by decide`) —
  both `stringCapRestrict_reconstructs_firesOnWideValley` and the reflexive splitter
  `stringSameWholeMatching_capBlockMatchingEq_firesOnWideValley` — and the mid-zero valley at `bottomCount = 2` as
  the instantiation smoke test (`stringCapRestrict_reconstructs_firesOnMidZeroValley`).

  What this marker does NOT claim (honestly), and what the FC-3 completeness capstone still needs above it (the B5
  bill, sized in this file's footer):
    * the CUP-side restriction `stringCupRestrict_reconstructs` / `stringSameWholeMatching_cupBlockMatchingEq` (a
      DISTINCT substrate — `cupRestrict`, `ValleyCupBottomPartner`, and a `midPositive : 0 < mid` hypothesis, none
      touched here);
    * the whole valley-append split `valleysWithBlockMatchingEq_spineTraceEquiv` (needs BOTH cap + cup splitters).

  So the completeness/producer flip `fxString_hasAdjointTripleCompleteness` (`StringMatchingCompleteness`) and
  `fxString_hasConvOfMapEqPortFlip` (`StringConvOfMapEqPort`) stay `false`.  This round flips ONLY this NEW marker:
  B4 (the cap side) is shipped as the `DiagramType.ext` reconstruction + the cap-block splitter, above the r31
  involution floor and the r29 survivor-top-total leg.  `= true`. -/
def fxString_hasCapRestrictReconstructs : Bool := true

/-! ## The B5 bill (the cup side, next round) — sized in the subject file

The cap side of the valley-append split is complete.  The remaining half — B5, the CUP side — rides a DISTINCT
substrate and is a clean separate round:

  * PORT `cupRestrict` (the `def`) + `ValleyCupBottomPartner` (401 lines: the cup-block bottom partner leg) +
    `ValleyCupReconstruct` (278 lines: `cupRestrict_reconstructs`, which carries an EXTRA `midPositive : 0 < mid`
    hypothesis the cap side does NOT need) + `ValleyCupAssembly` (240 lines: `sameWholeMatching_cupBlockMatchingEq`,
    the cup-block splitter, which takes the two `cupReconstructs` as hypotheses).
  * The new keyed substrate for the cup side mirrors the cap side (a survivor/bottom re-ranking on the cup block's
    own open wires) plus the `midPositive` guard; estimated typed core comparable to B4 (~250-350 real Lean lines),
    but stated over `cupRestrict` / `ValleyCupBottomPartner` — none of it touched here.

Once BOTH `stringSameWholeMatching_capBlockMatchingEq` (this round) and `stringSameWholeMatching_cupBlockMatchingEq`
(B5) ship, the whole valley-append split `valleysWithBlockMatchingEq_spineTraceEquiv` unblocks and the
completeness/producer flip (`fxString_hasAdjointTripleCompleteness`, WP-STRING-3 #2020 / FC-3 #2209) becomes
reachable. -/

end FX1Poly.Polygraph
