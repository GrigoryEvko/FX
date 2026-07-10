import FX1Poly.Polygraph.TwoCategory.WalkingString.StringCapNonCrossingJoin

/-! # WalkingString — the JOINT reachable-class invariant + the label-read projection (STRING-JOINT r1)

The four connectivity fold invariants over the bare `WireState` — freshness (`StringWireStateFresh`), forest
(`stringIsUnionFindForest`), boundary census (`StringBoundaryCensus`), non-crossing planarity
(`StringNonCrossing`) — are each SHIPPED with cup + cap + whole-fold preservation (FC-3b / FC-4 / FC-5).  This file
BUNDLES them into ONE reachable-class witness `StringJointInvariant`, threaded through the fold ONCE, and adds the
missing arity wrapper for non-crossing.  The bundle IS the reachable-class witness: it holds at the fresh seed and is
preserved by every cup/cap atom, so every state in a cell's fold image satisfies it.

It also ships the LABEL-READ projection that the FC-1 `capPin` obligation is a consequence of: a cap window reads its
`generatorDom` cap word (`stringCapWindow_notCupWord`), so `isCupWordOrdered` is `false` on the window — modulo the
one word-boundary decomposition hypothesis (`labels = pathLabels (leftContext · generatorDom · rightContext)`), which
is the string port of `ArcBoundaryTracking` and the exact remaining residual for the headline no-loops flip.

## What closes here (each zero-axiom)

  * ★ `StringJointInvariant` — the bundled reachable-class witness (fresh + forest + census + non-crossing + the
    seed-below-fresh bound), with the seed base `stringJointInvariant_initial`;
  * ★ `StringNonCrossing_stepAtom` — the arity-dispatch wrapper (both branches are the shipped
    `stringNonCrossing_stepCup` / `stringNonCrossing_stepCap`);
  * ★ `stringJointInvariant_stepAtom` / `_processSpine_ofChained` / `_fromCell` — the whole-fold transport, so every
    reachable state (from a cup/cap cell) satisfies the joint invariant;
  * ★ the LABEL-READ kit `stringPathLabels_read_pastLeft` / `_belowLeft` (pure `pathLabels ∘ composePath` reads),
    `stringCapGeneratorDomWord_notCupWord` (a cap generator's dom word fails `isCupWordOrdered`), and the assembled
    `stringCapWindow_notCupWord` (the FC-1 `capPin` conclusion, modulo the word decomposition).

## The honest residuals (the headline no-loops flip)

Adding the ORIENTATION field to the joint invariant needs the CAP-orient survivor P4 preservation
(`stringOrientationDiscipline_stepCap`, the merge-dual of the shipped 16-region cup-orient); adding the LABEL-WORD
field needs `advanceLabels` to track `pathLabels` of the evolving boundary word (the word-chaining fold).  Both are
named precisely in the honesty markers.  This file localizes the frontier to exactly those two, with the connectivity
substrate + the capPin label-read projection SHIPPED.

Raw Lean 4 + Init; the fold transport mirrors the shipped census fold, the label reads are cons-only structural
recursion.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private range plumbing (per-file copy, following the codebase pattern) -/

private theorem jointRangeLoopLength : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := jointRangeLoopLength count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1, Nat.add_right_comm count accumulated.length 1]

private theorem jointRangeLength (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [jointRangeLoopLength count []]; exact Nat.add_zero count

/-! ## The non-crossing arity wrapper (both branches shipped) -/

/-- ★ **One cup/cap atom preserves the non-crossing (planarity) invariant** — dispatch on the arity, computing the
window range from the boundary tracking (`domBoundaryLength`), and apply the shipped cup / cap non-crossing
preservation (`stringNonCrossing_stepCup` for a cup, consuming freshness + forest; `stringNonCrossing_stepCap` for a
cap, consuming forest + the boundary census).  The arity-dispatch wrapper the joint fold rides, both branches SHIPPED. -/
theorem StringNonCrossing_stepAtom {sourceMode targetMode : AdjointTripleMode}
    (seedBoundary : Nat) (state : WireState)
    (atom : SpineAtom adjointTripleModeSignature sourceMode targetMode)
    (arity : AtomHasCupOrCapArity atom) (fresh : StringWireStateFresh state)
    (forest : stringIsUnionFindForest state.links) (census : StringBoundaryCensus seedBoundary state)
    (tracksEntry : state.openWires.length = atom.domBoundaryLength)
    (nonCrossing : StringNonCrossing state) :
    StringNonCrossing (stepAtom state atom) := by
  have entryShape : state.openWires.length
      = atom.leftContext.length + atom.generatorDom.length + atom.rightContext.length := tracksEntry
  cases arity with
  | inl cupArity =>
      obtain ⟨hasCupDom, hasCupCod⟩ := cupArity
      have cupInRange : atom.leftContext.length ≤ state.openWires.length := by
        rw [entryShape, hasCupDom, Nat.add_zero]
        exact Nat.le_add_right atom.leftContext.length atom.rightContext.length
      rw [stepAtom_ofCupArity state atom hasCupDom hasCupCod]
      exact stringNonCrossing_stepCup state atom.leftContext.length cupInRange fresh forest nonCrossing
  | inr capArity =>
      obtain ⟨hasCapDom, hasCapCod⟩ := capArity
      have capInRange : atom.leftContext.length + 2 ≤ state.openWires.length := by
        rw [entryShape, hasCapDom]
        exact Nat.le_add_right (atom.leftContext.length + 2) atom.rightContext.length
      rw [stepAtom_ofCapArity state atom hasCapDom hasCapCod]
      exact stringNonCrossing_stepCap seedBoundary state atom.leftContext.length forest capInRange
        census nonCrossing

/-! ## The bundled reachable-class witness -/

/-- ★ **The JOINT reachable-class invariant.**  A state reachable from the fresh seed by a cup/cap fold carries all
four connectivity fold invariants at once — freshness, forest (acyclic union-find), the two-endpoint boundary census,
and non-crossing planarity — plus the bound `seedBoundary ≤ nextFresh` the census fold consumes.  This bundle IS the
reachable-class witness the headline no-loops flip runs on: the CAP-orient survivor and `capPin` label-read both
consume it (all four fields feed the survivor read + the census refutation). -/
structure StringJointInvariant (seedBoundary : Nat) (state : WireState) : Prop where
  /-- Every open wire and link endpoint is below `nextFresh` (the freshness invariant). -/
  fresh : StringWireStateFresh state
  /-- The union-find is a forest (acyclic). -/
  forest : stringIsUnionFindForest state.links
  /-- Every union-find component carries at most two boundary ends (the perfect-matching census). -/
  census : StringBoundaryCensus seedBoundary state
  /-- No two same-component open-wire windows interleave (planarity). -/
  nonCrossing : StringNonCrossing state
  /-- The seed boundary width is below the fresh counter (the census fold's bound). -/
  seedBelowFresh : seedBoundary ≤ state.nextFresh

/-- ★ **The fresh seed satisfies the joint invariant.**  Each field is the shipped seed leg: freshness
(`stringInitialWireState_fresh`), forest (`stringInitialWireState_isUnionFindForest`), census
(`stringBoundaryCensus_initial`), non-crossing (`stringInitialNonCrossing`), and `seedBoundary ≤ seedBoundary`. -/
theorem stringJointInvariant_initial (seedBoundary : Nat) :
    StringJointInvariant seedBoundary (stringInitialWireState seedBoundary) :=
  ⟨stringInitialWireState_fresh seedBoundary,
   stringInitialWireState_isUnionFindForest seedBoundary,
   stringBoundaryCensus_initial seedBoundary,
   stringInitialNonCrossing seedBoundary,
   Nat.le_refl seedBoundary⟩

/-- ★ **One cup/cap atom preserves the joint invariant** — each of the five fields is advanced by its shipped per-atom
leg (freshness `StringWireStateFresh_stepAtom`, forest `stringUnionFindForest_stepAtom`, census
`stringBoundaryCensus_stepAtom`, non-crossing `StringNonCrossing_stepAtom`, seed-bound via `stepAtom_nextFresh_le`). -/
theorem stringJointInvariant_stepAtom {sourceMode targetMode : AdjointTripleMode}
    (seedBoundary : Nat) (state : WireState)
    (atom : SpineAtom adjointTripleModeSignature sourceMode targetMode)
    (arity : AtomHasCupOrCapArity atom)
    (tracksEntry : state.openWires.length = atom.domBoundaryLength)
    (joint : StringJointInvariant seedBoundary state) :
    StringJointInvariant seedBoundary (stepAtom state atom) :=
  ⟨StringWireStateFresh_stepAtom state atom arity joint.fresh tracksEntry,
   stringUnionFindForest_stepAtom state atom joint.forest,
   stringBoundaryCensus_stepAtom seedBoundary state atom arity joint.fresh joint.forest
     joint.seedBelowFresh tracksEntry joint.census,
   StringNonCrossing_stepAtom seedBoundary state atom arity joint.fresh joint.forest joint.census
     tracksEntry joint.nonCrossing,
   Nat.le_trans joint.seedBelowFresh (stepAtom_nextFresh_le state atom)⟩

/-- ★ **A cup/cap-disciplined boundary-chained spine fold preserves the joint invariant end-to-end** — the arity /
boundary-tracking companions thread through the fold, and each atom's step preserves the bundle by the per-atom
dispatch.  Mirrors the shipped census fold `stringBoundaryCensus_processSpine_ofChained`. -/
theorem stringJointInvariant_processSpine_ofChained {sourceMode targetMode : AdjointTripleMode} :
    (atoms : List (SpineAtom adjointTripleModeSignature sourceMode targetMode)) →
    (state : WireState) → (boundaryLength seedBoundary : Nat) →
    state.openWires.length = boundaryLength →
    SpineBoundaryChained boundaryLength atoms →
    SpineHasCupCapAtoms atoms →
    StringJointInvariant seedBoundary state →
    StringJointInvariant seedBoundary (processSpine state atoms)
  | [], _, _, _, _, _, _, joint => joint
  | headAtom :: restAtoms, state, _, seedBoundary, tracks, chained, arityAll, joint => by
      obtain ⟨headFires, tailChained⟩ := spineBoundaryChained_tail chained
      obtain ⟨headArity, tailArity⟩ := spineHasCupCapAtoms_tail arityAll
      have tracksEntry : state.openWires.length = headAtom.domBoundaryLength :=
        tracks.trans headFires.symm
      show StringJointInvariant seedBoundary (processSpine (stepAtom state headAtom) restAtoms)
      exact stringJointInvariant_processSpine_ofChained restAtoms (stepAtom state headAtom)
        headAtom.codBoundaryLength seedBoundary
        (stepAtom_openWires_tracksBoundary state headAtom headArity tracksEntry)
        tailChained tailArity
        (stringJointInvariant_stepAtom seedBoundary state headAtom headArity tracksEntry joint)

/-- ★★ **The joint invariant at the canonical seed** — every cup/cap-generated adjoint-triple cell folds from the
fresh initial state to a state satisfying the joint reachable-class invariant (all four connectivity fields).  The
substrate the CAP-orient survivor + `capPin` label-read consume. -/
theorem stringJointInvariant_fromCell {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (cell : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath)
    (cellCupCap : CellHasCupCapGenerators cell) :
    StringJointInvariant sourcePath.length
      (processSpine (stringInitialWireState sourcePath.length) cell.spine) :=
  stringJointInvariant_processSpine_ofChained cell.spine
    (stringInitialWireState sourcePath.length) sourcePath.length sourcePath.length
    (jointRangeLength sourcePath.length)
    (RawTwoCellExpr.spineBoundaryChained_spine cell)
    (RawTwoCellExpr.spineHasCupCapAtoms_spine cell cellCupCap)
    (stringJointInvariant_initial sourcePath.length)

/-! ## The LABEL-READ projection — a cap window reads its `generatorDom` cap word

The FC-1 `capPin` obligation (a cap window reads a NON-cup word) is a PROJECTION of the label-boundary-word invariant
`labels = pathLabels boundaryWord` at the head atom's boundary decomposition
`boundaryWord = leftContext · generatorDom · rightContext`.  These pure reads discharge exactly that projection. -/

/-- ★ **Reading `pathLabels (leftWord · restWord)` past the left factor reads `restWord`.**  Cons-only structural
recursion on `leftWord`: at index `leftWord.length + offset` the read enters `restWord` at `offset`. -/
theorem stringPathLabels_read_pastLeft {sourceMode midMode targetMode : AdjointTripleMode} :
    (leftWord : ModalityPath adjointTripleGraph sourceMode midMode) →
    (restWord : ModalityPath adjointTripleGraph midMode targetMode) → (offset : Nat) →
    wireLabelListGetAt (pathLabels (composePath leftWord restWord)) (leftWord.length + offset)
      = wireLabelListGetAt (pathLabels restWord) offset
  | ModalityPath.nil _, restWord, offset => by
      show wireLabelListGetAt (pathLabels restWord) (0 + offset)
        = wireLabelListGetAt (pathLabels restWord) offset
      rw [Nat.zero_add]
  | ModalityPath.cons modality restLeft, restWord, offset => by
      show wireLabelListGetAt (wireLabelOfModality modality :: pathLabels (composePath restLeft restWord))
          (restLeft.length + 1 + offset)
        = wireLabelListGetAt (pathLabels restWord) offset
      rw [Nat.add_right_comm restLeft.length 1 offset]
      show wireLabelListGetAt (pathLabels (composePath restLeft restWord)) (restLeft.length + offset)
        = wireLabelListGetAt (pathLabels restWord) offset
      exact stringPathLabels_read_pastLeft restLeft restWord offset

/-- ★ **Reading `pathLabels (leftWord · restWord)` below the left length reads `leftWord`.**  Cons-only structural
recursion on `leftWord`; an index inside the left factor is untouched by the composition. -/
theorem stringPathLabels_read_belowLeft {sourceMode midMode targetMode : AdjointTripleMode} :
    (leftWord : ModalityPath adjointTripleGraph sourceMode midMode) →
    (restWord : ModalityPath adjointTripleGraph midMode targetMode) → (index : Nat) →
    index < leftWord.length →
    wireLabelListGetAt (pathLabels (composePath leftWord restWord)) index
      = wireLabelListGetAt (pathLabels leftWord) index
  | ModalityPath.nil _, _, index, indexBelow => absurd indexBelow (Nat.not_lt_zero index)
  | ModalityPath.cons _ _, _, 0, _ => rfl
  | ModalityPath.cons _ restLeft, restWord, index + 1, indexBelow =>
      stringPathLabels_read_belowLeft restLeft restWord index (Nat.lt_of_succ_lt_succ indexBelow)

/-- ★★ **A cap generator's dom word fails `isCupWordOrdered`.**  Casing the generator: the two CUP cases
(`unitLower` / `unitUpper`) are excluded by `codZero` (their cod word has length 2); the two CAP cases read the cap
words `(G, F)` (`counitLower`, `stringGF`) and `(H, G)` (`counitUpper`, `stringHG`), each `false` under
`isCupWordOrdered` on the nose.  This is `stringBothCapWords_notCupWord` read off the generator. -/
theorem stringCapGeneratorDomWord_notCupWord {midSource midTarget : AdjointTripleMode}
    {generatorDom generatorCod : ModalityPath adjointTripleGraph midSource midTarget}
    (generator : StringTwoCell generatorDom generatorCod) (codZero : generatorCod.length = 0) :
    isCupWordOrdered (wireLabelListGetAt (pathLabels generatorDom) 0)
      (wireLabelListGetAt (pathLabels generatorDom) 1) = false := by
  cases generator with
  | unitLower => exact absurd codZero (by decide)
  | unitUpper => exact absurd codZero (by decide)
  | counitLower => rfl
  | counitUpper => rfl

/-- ★★ **A cap window reads its `generatorDom` cap word** (modulo the boundary-word decomposition).  Given
`labels = pathLabels (leftContext · generatorDom · rightContext)` at the head atom (the label-boundary-tracking
invariant, the string port of `ArcBoundaryTracking`) and a cap arity, the window labels at `leftContext.length` and
`leftContext.length + 1` are the two letters of `pathLabels generatorDom` (the label reads
`stringPathLabels_read_pastLeft` / `_belowLeft`), and that cap word fails `isCupWordOrdered`
(`stringCapGeneratorDomWord_notCupWord`).  This is EXACTLY the FC-1 `capPin` conclusion, discharged as a PROJECTION of
the label-word invariant — the piece the boundary census could not give. -/
theorem stringCapWindow_notCupWord {sourceMode targetMode : AdjointTripleMode}
    (atom : SpineAtom adjointTripleModeSignature sourceMode targetMode) (labels : List WireLabel)
    (labelsEq : labels = pathLabels
      (composePath atom.leftContext (composePath atom.generatorDom atom.rightContext)))
    (domTwo : atom.generatorDom.length = 2) (codZero : atom.generatorCod.length = 0) :
    isCupWordOrdered (wireLabelListGetAt labels atom.leftContext.length)
      (wireLabelListGetAt labels (atom.leftContext.length + 1)) = false := by
  subst labelsEq
  have domPos0 : 0 < atom.generatorDom.length := by rw [domTwo]; decide
  have domPos1 : 1 < atom.generatorDom.length := by rw [domTwo]; decide
  have past0 := stringPathLabels_read_pastLeft atom.leftContext
    (composePath atom.generatorDom atom.rightContext) 0
  rw [Nat.add_zero] at past0
  have below0 := stringPathLabels_read_belowLeft atom.generatorDom atom.rightContext 0 domPos0
  have past1 := stringPathLabels_read_pastLeft atom.leftContext
    (composePath atom.generatorDom atom.rightContext) 1
  have below1 := stringPathLabels_read_belowLeft atom.generatorDom atom.rightContext 1 domPos1
  -- Rewrite BACKWARD inside the cap-word fact (all reads share the `signature.graph` form), then bridge to the
  -- goal by `exact` (which closes the residual `adjointTripleGraph`-vs-`signature.graph` gap definitionally).
  have capWord := stringCapGeneratorDomWord_notCupWord atom.generator codZero
  rw [← below0, ← below1, ← past0, ← past1] at capWord
  exact capWord

/-! ## Honesty markers -/

/-- **★ ESTABLISHED — the JOINT reachable-class invariant is bundled and folds end-to-end.**  `StringJointInvariant`
bundles the four SHIPPED connectivity fold invariants (freshness, forest, two-endpoint boundary census, non-crossing
planarity) plus the `seedBoundary ≤ nextFresh` bound into ONE reachable-class witness, threaded through the fold ONCE:
the seed base (`stringJointInvariant_initial`), the per-atom preservation (`stringJointInvariant_stepAtom`, each field
by its shipped leg, non-crossing via the NEW arity wrapper `StringNonCrossing_stepAtom`), the whole-fold transport
(`stringJointInvariant_processSpine_ofChained`), and the seed capstone (`stringJointInvariant_fromCell`: every
cup/cap-generated adjoint-triple cell folds to a state satisfying the bundle).  All UNCONDITIONAL, zero-axiom — the
substrate the headline no-loops flip runs on.  `= true`. -/
def fxString_hasJointReachableInvariant : Bool := true

/-- **★ ESTABLISHED — the FC-1 `capPin` obligation is a PROJECTION of the label-boundary-word invariant.**  The pure
label reads `stringPathLabels_read_pastLeft` / `_belowLeft` (`pathLabels ∘ composePath` at an index past / below the
left factor), the cap-generator dom-word fact `stringCapGeneratorDomWord_notCupWord` (both cap words `(G,F)`, `(H,G)`
fail `isCupWordOrdered`), and the assembled `stringCapWindow_notCupWord` discharge EXACTLY the FC-1 `capPin`
conclusion (a cap window reads a non-cup word) — MODULO the one hypothesis
`labels = pathLabels (leftContext · generatorDom · rightContext)`, the label-boundary-word decomposition at the head
atom.  So `capPin` is no longer a universal-over-all-states (which is FALSE — a free-label state reads a cup word at a
cap window); it is a consequence of the reachable label-word invariant.  This is the census docstring's named
prerequisite ("strengthening the fold invariant to carry label-boundary-tracking, from which capPin is a projection"),
now SHIPPED as the projection.  `= true`. -/
def fxString_hasCapPinLabelReadProjection : Bool := true

/-- **★★ ESTABLISHED — the headline no-loops flip is CLOSED; both fold-preservation residuals are DISCHARGED.**  The
two residuals this docstring named on top of the joint invariant are both shipped (STRING-JOINT r2):

  * **the CAP-orient survivor P4** (`stringOrientationDiscipline_stepCap`, `StringOrientationCapPreserves`, WALL 1) —
    the MERGE-dual of the shipped 16-region cup-orient, CLOSED via the join-branch survivor dispatch
    (`sameComponent_unionFindJoin_dispatch`) with the interleaving sub-cases refuted by non-crossing and the nested
    sub-cases read by the three finite-`WireLabel` colour deductions, fed the window cap word;
  * **the label-WORD chaining** (`SpineBoundaryWordChained` + `stringAdvanceLabels_tracksWordChain`, WALL 2) — the
    word analog of the length-only `SpineBoundaryChained`, threaded so `stringCapWindow_isCapWord` supplies the cap
    word at each reachable cap.

The assembly (`StringNoLoopsAssembly.stringMatchingOf_loops_zero`) glues them: it threads the joint invariant + the
orientation discipline (labels `pathLabels boundaryWord`) through the fold, producing `CapsDistinctAlongFold`
unconditionally, and FC-0's reduction closes loop-freedom.  All the substrate this file shipped
(connectivity bundle, chirality refutation, seed, capPin label-read projection) feeds directly in.  `= true`. -/
def fxString_hasNoLoopsFlipFromJointInvariant : Bool := true

end FX1Poly.Polygraph
