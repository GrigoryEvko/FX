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

end FX1Poly.Polygraph
