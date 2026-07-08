import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupMixedLastReadoff
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineTraceAppendCongruence
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcChainedExtraction

/-! # ArcCupPeelLastAssembly — the PEEL-LAST reconstruction assembly (route D, no head-windowPin)

`ArcChainedExtraction` reduces `ArcCellReconstruction adjunctionModeSignature` to the HEAD-first per-head
obligation `SpineArcHeadExtractionChained` — peel the head, recurse on the tail with the boundary moving
UP.  For a cup head that obligation runs straight into the REFUTED census read-off `headCupWindowReadoff_isFalse`
(`ArcCupHeadWindowUniversalRefuted`): two boundary-chained cup-headed spines whose head cups sit at DIFFERENT
windows share the WHOLE `FullArcStructure`, so a cup's HEAD window is NOT an arc-field read-off — the head
fronting needs the un-readable `windowPin`.

This brick ships the DUAL assembly — the FM/Delpeuch-Vicary peel-LAST recursion (DV LMCS 18(1:10) 2022,
Lemma 5.1: a leaf/turnback endpoint has a UNIQUE arc-determined position; Theorem 5.8: normalize by removing
the leaf and recursing on the strictly smaller diagram).  Instead of peeling the head it peels the LAST atom,
keeping the bottom boundary FIXED (the last atom fires last, so the prefix runs at the same bottom boundary
and only the TOP boundary shrinks).  The point is `mixedSpine_lastCup_isShortChord`
(`ArcCupMixedLastReadoff`): the LAST cup of a mixed spine reads off the boundary matching as an adjacent
SHORT CHORD — its window IS arc-readable, unlike the head cup — so the peel-last route AVOIDS the refuted
`windowPin` on the boundary-cup branch.

  * ★ `SpineArcLastExtractionChained` — the peel-LAST per-atom obligation (dual of the shipped head-first
    `SpineArcHeadExtractionChained`): given `initList ++ [lastAtom]` and `secondList` arc-equal at the FIXED
    bottom boundary, extract `lastAtom` to the BACK of `secondList` via a realized `SpineTraceEquiv` bubble,
    leaving an `initList`-arc-equal remainder chained at the SAME bottom boundary.
  * ★ `spineTraceEquiv_of_chainedLastExtraction` — the assembly, by STRUCTURAL recursion on a `Nat` width
    measure = `firstList.length` (`induction measure`, `Nat.rec`, no `WellFounded.fix`): the empty base closes
    by nil-inversion, the successor case splits off the last atom (`existsInitLast`), peels it via the
    obligation, recurses on the strictly shorter `initList`, and glues the recursive equivalence back through
    the shipped tail-append congruence `spineTraceEquiv_backAppendListCongr` composed with the bubble's
    symmetry.
  * ★ `adjunctionArcCellReconstruction_of_chainedLastExtraction` — the cell-level reduction: granted the
    peel-last obligation at every boundary, `ArcCellReconstruction adjunctionModeSignature` FOLLOWS (spines
    chained by `RawTwoCellExpr.spineBoundaryChained_spine`, nil-inversion by `spineArcNilInversion_adjunction`,
    `arcStructureOf` definitionally the spine-list fold).  The peel-LAST analog of
    `adjunctionArcCellReconstruction_of_chainedExtraction`.
  * ★ `lastCup_sharedShortChord_ofArcEqual` — the CUP-branch anchor with NO windowPin: when `lastAtom` is a
    cup, `secondList`'s OWN arc (not the syntactic last atom) carries the SAME adjacent short chord at the
    arc-determined port `bottomCount + lastCup.leftContext.length`, read straight off the shared
    `FullArcStructure`.  This is the arc-readable datum the refuted head windowPin lacked.

## The exact residual (peel-last ISOLATES but does NOT bypass)

The assembly is complete: the ENTIRE reconstruction is now `SpineArcLastExtractionChained` at every boundary
(alternatively to the head-first `SpineArcHeadExtractionChained`).  Discharging the peel-last obligation still
splits by the last atom's arity:

  * last atom a CUP → arc-readable short chord (`lastCup_sharedShortChord_ofArcEqual`), so the residual is the
    OWNER-LOCATE-and-bubble: `secondList` shares the top short chord `[p, p+1]`; its OWNER cup must be bubbled
    to the BACK.  This is arc-ANCHORED (the target is a top-boundary short chord), the honest windowPin
    replacement — but the bubble itself is unbuilt;
  * last atom a CAP → NOT arc-locatable as last (a cap REMOVES two top ports via `natListRemoveTwoAt`, not
    left-invertible, no fresh `[1,1]` census window — the blocked `dropLastCap_arc_injective`), and if no
    boundary cup and no seed cap exist the spine is STUCK.  `ArcStuckSpineNonSingleton` machine-refutes the
    "stuck ⟹ singleton ⟹ refl" shortcut: two DISTINCT stuck spines (double vs nested snake on `left`) share
    the whole `FullArcStructure`, so the stuck case carries the reconstruction's full "sequential vs nested
    arches" planar-isotopy content.

So peel-last relocates the wall OFF the refuted head windowPin onto the owner-locate-and-bubble + the stuck
case — an honest ISOLATION of the residual, not its discharge.  `fxMode_hasArcStructureReconstruction` stays
`false`.

Raw Lean 4 + Init; STRUCTURAL (list recursion in `existsInitLast`, `Nat.rec` on the width measure), zero-axiom;
per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

universe u

namespace FX1Poly.Polygraph

/-! ## Splitting the last atom off a non-empty list (structural) -/

/-- **Split a non-empty list as `initList ++ [lastAtom]`.**  Structural recursion on the list: a singleton is
`[] ++ [singleton]`, a longer list recurses on its tail and re-cons the head onto the returned `initList`.  Also
returns the length bookkeeping `initList.length + 1 = fullList.length` so the peel-last recursion decreases its
`Nat` width measure structurally. -/
private theorem existsInitLast {Elem : Type u} :
    (fullList : List Elem) → fullList ≠ [] →
      ∃ (initList : List Elem) (lastAtom : Elem),
        fullList = initList ++ [lastAtom] ∧ initList.length + 1 = fullList.length
  | [], hNonEmpty => absurd rfl hNonEmpty
  | [singleton], _ => ⟨[], singleton, rfl, rfl⟩
  | first :: second :: rest, _ =>
      match existsInitLast (second :: rest) (fun listEqNil => nomatch listEqNil) with
      | ⟨initList, lastAtom, splitEq, lengthEq⟩ =>
          ⟨first :: initList, lastAtom,
            congrArg (fun tailList => first :: tailList) splitEq,
            congrArg (· + 1) lengthEq⟩

/-! ## The peel-LAST per-atom obligation -/

/-- **The peel-LAST per-atom geometric extraction obligation** — the dual of the head-first
`SpineArcHeadExtractionChained`.  Both lists are boundary-chained at the FIXED bottom boundary `bottomCount`
and arc-equal there; then the LAST atom `lastAtom` extracts from `secondList` via a realized `SpineTraceEquiv`
bubble to the BACK, leaving a remainder that is (i) chained at the SAME bottom boundary and (ii) arc-equal to
`initList` there.  Unlike the head-first obligation the boundary does NOT move: the last atom fires last, so the
prefix `initList` runs at the same bottom boundary and only the top boundary shrinks with the peel. -/
def SpineArcLastExtractionChained (signature : ModeSignature)
    {overallSource overallTarget : signature.graph.Mode} (bottomCount : Nat) : Prop :=
  ∀ (initList : List (SpineAtom signature overallSource overallTarget))
    (lastAtom : SpineAtom signature overallSource overallTarget)
    (secondList : List (SpineAtom signature overallSource overallTarget)),
    SpineBoundaryChained bottomCount (initList ++ [lastAtom]) →
    SpineBoundaryChained bottomCount secondList →
    arcStructureOfSpineList bottomCount (initList ++ [lastAtom])
        = arcStructureOfSpineList bottomCount secondList →
    ∃ matchedInit,
      SpineTraceEquiv signature secondList (matchedInit ++ [lastAtom])
        ∧ SpineBoundaryChained bottomCount matchedInit
        ∧ arcStructureOfSpineList bottomCount initList
            = arcStructureOfSpineList bottomCount matchedInit

/-! ## The peel-LAST assembly -/

/-- ★ **The peel-last extraction matching, assembled.**  STRUCTURAL recursion on a `Nat` width measure
= `firstList.length` (`induction measure`, `Nat.rec`, no `WellFounded.fix`): the empty base closes by
nil-inversion (`secondList` is empty too) and reflexivity; the successor case splits `firstList` as
`initList ++ [lastAtom]` (`existsInitLast`), peels the last atom via `lastExtraction` (a realized back-bubble,
a chained remainder, `initList`-arc-equality — all at the FIXED bottom boundary), recurses on the strictly
shorter `initList`, and glues the recursive `SpineTraceEquiv initList matchedInit` back through the shipped
tail-append congruence `spineTraceEquiv_backAppendListCongr` (appending `[lastAtom]`) composed with the
bubble's symmetry.  The peel-LAST analog of `spineTraceMatched_of_chainedHeadExtraction`. -/
theorem spineTraceEquiv_of_chainedLastExtraction {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} (bottomCount : Nat)
    (lastExtraction : SpineArcLastExtractionChained signature
      (overallSource := overallSource) (overallTarget := overallTarget) bottomCount)
    (nilInversion : SpineArcNilInversion signature
      (overallSource := overallSource) (overallTarget := overallTarget) bottomCount)
    (measure : Nat) :
    ∀ {firstList : List (SpineAtom signature overallSource overallTarget)},
      firstList.length = measure →
      ∀ {secondList : List (SpineAtom signature overallSource overallTarget)},
        SpineBoundaryChained bottomCount firstList →
        SpineBoundaryChained bottomCount secondList →
        arcStructureOfSpineList bottomCount firstList
            = arcStructureOfSpineList bottomCount secondList →
        SpineTraceEquiv signature firstList secondList := by
  induction measure with
  | zero =>
      intro firstList lengthEq secondList _ _ arcEqual
      match firstList, lengthEq, arcEqual with
      | [], _, arcEqualNil =>
          rw [nilInversion secondList arcEqualNil]
          exact SpineTraceEquiv.refl []
  | succ measure inductionHypothesis =>
      intro firstList lengthEq secondList firstChained secondChained arcEqual
      obtain ⟨initList, lastAtom, splitEq, initLengthEq⟩ :=
        existsInitLast firstList (fun listEqNil => by rw [listEqNil] at lengthEq; exact Nat.noConfusion lengthEq)
      subst splitEq
      have initLength : initList.length = measure := Nat.succ.inj (initLengthEq.trans lengthEq)
      obtain ⟨matchedInit, backBubble, matchedChained, initArcEqual⟩ :=
        lastExtraction initList lastAtom secondList firstChained secondChained arcEqual
      have initChained : SpineBoundaryChained bottomCount initList :=
        spineBoundaryChained_prefix_ofAppend initList [lastAtom] bottomCount firstChained
      exact (spineTraceEquiv_backAppendListCongr
        (inductionHypothesis initLength initChained matchedChained initArcEqual) [lastAtom]).trans
        backBubble.symm

/-! ## The cell-level reduction (peel-last) -/

/-- ★ **`ArcCellReconstruction adjunctionModeSignature` from the peel-last obligation.**  Granted the peel-last
per-atom extraction at every boundary, the cup/cap-seed cell reconstruction follows: parallel cells' spines are
boundary-chained at `sourcePath.length` (`RawTwoCellExpr.spineBoundaryChained_spine`), `arcStructureOf` is
definitionally the spine-list fold there, nil-inversion is the shipped `spineArcNilInversion_adjunction`, and the
peel-last assembly lands the trace equivalence at width measure `firstCell.spine.length`.  The peel-LAST analog
of `adjunctionArcCellReconstruction_of_chainedExtraction`. -/
theorem adjunctionArcCellReconstruction_of_chainedLastExtraction
    (lastExtraction : ∀ {sourceMode targetMode : adjunctionGraph.Mode} (bottomCount : Nat),
      SpineArcLastExtractionChained adjunctionModeSignature
        (overallSource := sourceMode) (overallTarget := targetMode) bottomCount) :
    ArcCellReconstruction adjunctionModeSignature := by
  intro sourceMode targetMode sourcePath targetPath firstCell secondCell arcEqual
  exact spineTraceEquiv_of_chainedLastExtraction sourcePath.length
    (lastExtraction sourcePath.length)
    (spineArcNilInversion_adjunction sourcePath.length)
    firstCell.spine.length rfl
    firstCell.spineBoundaryChained_spine
    secondCell.spineBoundaryChained_spine
    arcEqual

/-! ## The CUP-branch anchor — the shared short chord (NO windowPin) -/

/-- ★ **The last cup's short chord is SHARED by the second spine, read from the arc (NO windowPin).**  When
`lastAtom` is a cup (`lastDom`, `lastCod`), `mixedSpine_lastCup_isShortChord` reads its window off `firstList`'s
boundary matching as an adjacent short chord at the arc-determined port `bottomCount + lastCup.leftContext.length`;
since `secondList` shares the WHOLE `FullArcStructure` (`arcEqual`), `secondList`'s OWN boundary matching carries
the SAME short chord at the SAME arc-determined port.  This is the arc-readable datum the refuted head windowPin
lacked (`headCupWindowReadoff_isFalse`): the target short chord is a genuine TOP-boundary anchor.  It does NOT
claim `secondList`'s syntactic last atom sits there — locating the OWNER cup of `[p, p+1]` in `secondList` and
bubbling it to the back is the remaining (arc-anchored) residual. -/
theorem lastCup_sharedShortChord_ofArcEqual
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (initList : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (lastCup : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (secondList : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained bottomCount (initList ++ [lastCup]))
    (lastDom : lastCup.generatorDom.length = 0)
    (lastCod : lastCup.generatorCod.length = 2)
    (arcEqual : arcStructureOfSpineList bottomCount (initList ++ [lastCup])
        = arcStructureOfSpineList bottomCount secondList) :
    natListGetAt (arcStructureOfSpineList bottomCount secondList).diagram.partner
        (bottomCount + lastCup.leftContext.length)
      = bottomCount + lastCup.leftContext.length + 1 := by
  have shortChord := mixedSpine_lastCup_isShortChord bottomCount initList lastCup chained lastDom lastCod
  rw [arcEqual] at shortChord
  exact shortChord

/-! ## Honesty marker -/

/-- **Honesty marker — the PEEL-LAST assembly is SHIPPED (route D), relocating the wall OFF the refuted head
windowPin.**  `spineTraceEquiv_of_chainedLastExtraction` assembles the full reconstruction by STRUCTURAL `Nat.rec`
on the width measure (peel the LAST atom, recurse on the strictly shorter prefix at the FIXED bottom boundary,
glue via the shipped tail-append congruence), and `adjunctionArcCellReconstruction_of_chainedLastExtraction` lands
`ArcCellReconstruction adjunctionModeSignature` from the peel-last obligation `SpineArcLastExtractionChained`.
`lastCup_sharedShortChord_ofArcEqual` ships the CUP-branch anchor with NO windowPin: `secondList`'s own arc carries
the last cup's short chord at the arc-determined port.

What this marker does NOT claim: the peel-last obligation itself.  Discharging it splits by the last atom's arity:
the CUP branch reduces to the OWNER-LOCATE-and-bubble (arc-anchored via `lastCup_sharedShortChord_ofArcEqual`, the
honest windowPin replacement, but unbuilt); the CAP branch is not arc-locatable as last (blocked
`dropLastCap_arc_injective`), and the STUCK case (no boundary cup, no seed cap) is machine-refuted as
NON-singleton by `ArcStuckSpineNonSingleton` (double vs nested snake share the whole `FullArcStructure`), carrying
the reconstruction's full "sequential vs nested arches" planar-isotopy content.  So peel-last ISOLATES the residual
onto the owner-bubble + the stuck case, it does NOT bypass them.  No gate flip;
`fxMode_hasArcStructureReconstruction` stays `false`.  `= true`. -/
def fxMode_hasArcPeelLastAssembly : Bool := true

end FX1Poly.Polygraph
