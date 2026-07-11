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

end FX1Poly.Polygraph
