import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcArity
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSpineValleyWidthTelescope
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPerfectMatchingFold

/-! # WalkingString/StringArcBoundaryCensusPerfectMatchingFold — the arc-engine boundary census and token-frame
perfect matching thread the whole chained arc fold over the walking ADJOINT-TRIPLE (`F ⊣ G ⊣ H`) signature
(FC-3 r30, B1: the arc-engine token folds)

The string clones of the walking-adjunction `arcBoundaryCensus_processArcSpine_ofChained` /
`arcPerfectMatchingTokens_processArcSpine_ofChained` (`ArcCensusFold`, `ArcPerfectMatchingFold`).  This is the
deepest layer of the M2c cap subtree the mid-zero producer needs: the joint arc-engine foundation the involution
and no-fixed-point legs (B3) rest on.  For a boundary-chained spine over the three-colour signature, the arc fold
carries the two-endpoint BOUNDARY CENSUS (every union-find component touches at most two boundary ends) and the
token-frame PERFECT MATCHING (every boundary token has a distinct same-component partner) from the fresh seed to
the folded state.

The arc engine is signature-BLIND: every per-atom step worker (`stepArcAtom_eq_stepCupArc` /
`_stepCapArc`, `arcStateFresh_stepArcAtom`, `isUnionFindForest_stepArcAtom_ofCupOrCap`,
`stepArcAtom_openWires_tracksBoundary`, `stepArcAtom_nextFresh_le`) and every preservation worker
(`arcBoundaryCensus_stepCupArc` / `_stepCapArc`, `arcPerfectMatchingTokens_stepCupArc` / `_stepCapArc`) is stated
over the bare `ArcWireState` / a `{signature}`-generic `SpineAtom`, so it is REUSED verbatim by import — no
re-derivation.  The ONE signature-keyed hook is the cup/cap arity dispatch, and the shipped
`adjointTripleSpineAtom_hasCupOrCapArity` (`StringArcArity`) supplies it as the direct four-generator analog of
`adjunctionSpineAtom_hasCupOrCapArity`.  So every brick below is a byte-identical token-swap of the walking-adjunction
original, rerouting the signature token alone `adjunctionModeSignature → adjointTripleModeSignature`.  No new
mathematics, no unproven residual.

  * `stringArcBoundaryCensus_stepArcAtom` — one boundary-tracked atom preserves the census (cup window in range by
    boundary tracking, cap window fits inside the tracked boundary), dispatching on the shipped arity classifier.
  * ★ `stringArcBoundaryCensus_processArcSpine_ofChained` / `_ofChainedSpineList` — the whole-fold census transport
    and the canonical-seed capstone: every boundary-chained string spine folds from the fresh initial state to a
    state whose every component touches at most two boundary endpoints.
  * `stringArcPerfectMatchingTokens_stepArcAtom` — one atom preserves the token-frame perfect matching (the cap step
    consumes the census threaded alongside).
  * ★ `stringArcPerfectMatchingTokens_processArcSpine_ofChained` / `_ofChainedSpineList` — the whole-fold transport
    (threading the census for the cap step) and the canonical-seed capstone: every boundary token of the folded
    state has a distinct same-component partner — the `noFixedPoint` fact the short-chord planar lemma consumes.

Two concrete truth-probes fire the census and perfect-matching capstones end-to-end: a genuine NON-DEGENERATE WIDE
valley `[ε] ++ [η']` at `bottomCount = 4` whose cap has a length-2 left context, so it consumes wires 2, 3 leaving
survivors {0, 1} — a real mid-width `2` (a `decide` cross-check pins it), the first probe in this arc that carries
non-zero mid content — and the mid-zero probe `[ε] ++ [η']` at `bottomCount = 2` (empty contexts) as the "does it
instantiate at all" smoke test.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free;
structural recursion on the atom list, no `WellFounded.fix`; per-declaration `#assert_no_axioms` gated in the audit
twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private range plumbing (per-file copy with a distinct `PMF` suffix, keeping the umbrella build's global
table duplicate-free against the two walking-adjunction fold copies) -/

private theorem rangeLoopLengthPMF : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := rangeLoopLengthPMF count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length
        = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1,
        Nat.add_right_comm count accumulated.length 1]

private theorem rangeLengthPMF (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [rangeLoopLengthPMF count []]
  exact Nat.add_zero count

/-! ## The per-atom census step -/

/-- One boundary-tracked adjoint-triple atom preserves the census: a cup via the splice preservation (its position
is in range because the generator consumes nothing), a cap via the window preservation (its two-wire window fits
inside the tracked boundary).  The arc engine dispatches on the shipped four-generator arity classifier
(`adjointTripleSpineAtom_hasCupOrCapArity`) — the direct analog of `arcBoundaryCensus_stepArcAtom`. -/
theorem stringArcBoundaryCensus_stepArcAtom
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (seedBoundary : Nat) (state : ArcWireState)
    (atom : SpineAtom adjointTripleModeSignature overallSource overallTarget)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (seedBelowFresh : seedBoundary ≤ state.nextFresh)
    (tracksEntry : state.openWires.length = atom.domBoundaryLength)
    (oldCensus : ArcBoundaryCensus seedBoundary state) :
    ArcBoundaryCensus seedBoundary (stepArcAtom state atom) := by
  have entryShape : state.openWires.length
      = atom.leftContext.length + atom.generatorDom.length + atom.rightContext.length :=
    tracksEntry
  cases adjointTripleSpineAtom_hasCupOrCapArity atom with
  | inl cupArity =>
      obtain ⟨hasCupDomArity, hasCupCodArity⟩ := cupArity
      have cupInRange : atom.leftContext.length ≤ state.openWires.length := by
        rw [entryShape, hasCupDomArity, Nat.add_zero]
        exact Nat.le_add_right atom.leftContext.length atom.rightContext.length
      rw [stepArcAtom_eq_stepCupArc state atom hasCupDomArity hasCupCodArity]
      exact arcBoundaryCensus_stepCupArc seedBoundary state atom.leftContext.length
        fresh forest seedBelowFresh cupInRange oldCensus
  | inr capArity =>
      obtain ⟨hasCapDomArity, hasCapCodArity⟩ := capArity
      have capInRange : atom.leftContext.length + 2 ≤ state.openWires.length := by
        rw [entryShape, hasCapDomArity]
        exact Nat.le_add_right (atom.leftContext.length + 2) atom.rightContext.length
      rw [stepArcAtom_eq_stepCapArc state atom hasCapDomArity hasCapCodArity]
      exact arcBoundaryCensus_stepCapArc seedBoundary state atom.leftContext.length
        fresh forest seedBelowFresh capInRange oldCensus

/-! ## The whole-fold census transport and the canonical-seed capstone -/

/-- ★ **A chained string spine's arc fold preserves the boundary census end-to-end** — the freshness /
forestness / boundary-tracking / seed-bound companions thread through the fold exactly as in the discipline fold,
and each atom's step preserves the census by the per-atom dispatch.  The string port of
`arcBoundaryCensus_processArcSpine_ofChained`. -/
theorem stringArcBoundaryCensus_processArcSpine_ofChained
    {overallSource overallTarget : adjointTripleGraph.Mode} :
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)) →
    (state : ArcWireState) → (boundaryLength seedBoundary : Nat) →
    ArcStateFresh state → isUnionFindForest state.links →
    state.openWires.length = boundaryLength →
    SpineBoundaryChained boundaryLength atoms →
    seedBoundary ≤ state.nextFresh →
    ArcBoundaryCensus seedBoundary state →
    ArcBoundaryCensus seedBoundary (processArcSpine state atoms)
  | [], _, _, _, _, _, _, _, _, census => census
  | headAtom :: restAtoms, state, _, seedBoundary, fresh, forest, tracks, chained,
      seedBelowFresh, census => by
      obtain ⟨headFires, tailChained⟩ := spineBoundaryChained_tail chained
      have tracksEntry : state.openWires.length = headAtom.domBoundaryLength :=
        tracks.trans headFires.symm
      have headArity := adjointTripleSpineAtom_hasCupOrCapArity headAtom
      show ArcBoundaryCensus seedBoundary
        (processArcSpine (stepArcAtom state headAtom) restAtoms)
      exact stringArcBoundaryCensus_processArcSpine_ofChained restAtoms
        (stepArcAtom state headAtom) headAtom.codBoundaryLength seedBoundary
        (arcStateFresh_stepArcAtom state headAtom fresh)
        (isUnionFindForest_stepArcAtom_ofCupOrCap state headAtom headArity forest)
        (stepArcAtom_openWires_tracksBoundary state headAtom headArity tracksEntry)
        tailChained
        (Nat.le_trans seedBelowFresh (stepArcAtom_nextFresh_le state headAtom))
        (stringArcBoundaryCensus_stepArcAtom seedBoundary state headAtom fresh forest
          seedBelowFresh tracksEntry census)

/-- ★ **The census capstone at the canonical seed**: every boundary-chained walking-adjoint-triple spine folds from
the fresh initial state to a state whose every component touches at most two boundary endpoints (bottom ports and
surviving open slots). -/
theorem stringArcBoundaryCensus_ofChainedSpineList
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (bottomCount : Nat)
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained bottomCount atoms) :
    ArcBoundaryCensus bottomCount
      (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        atoms) :=
  stringArcBoundaryCensus_processArcSpine_ofChained atoms
    (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) bottomCount bottomCount
    (arcStateFresh_initial bottomCount) isUnionFindForest_nil (rangeLengthPMF bottomCount)
    chained (Nat.le_refl bottomCount) (arcBoundaryCensus_initial bottomCount)

/-! ## The per-atom perfect-matching step -/

/-- One boundary-tracked adjoint-triple atom preserves the token-frame perfect matching: a cup via the splice
preservation, a cap via the census-coupled merge preservation (its window fits inside the tracked boundary).  The
string port of `arcPerfectMatchingTokens_stepArcAtom`. -/
theorem stringArcPerfectMatchingTokens_stepArcAtom
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (seedBoundary : Nat) (state : ArcWireState)
    (atom : SpineAtom adjointTripleModeSignature overallSource overallTarget)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (seedBelowFresh : seedBoundary ≤ state.nextFresh)
    (tracksEntry : state.openWires.length = atom.domBoundaryLength)
    (census : ArcBoundaryCensus seedBoundary state)
    (oldPerfect : ArcPerfectMatchingTokens seedBoundary state) :
    ArcPerfectMatchingTokens seedBoundary (stepArcAtom state atom) := by
  have entryShape : state.openWires.length
      = atom.leftContext.length + atom.generatorDom.length + atom.rightContext.length :=
    tracksEntry
  cases adjointTripleSpineAtom_hasCupOrCapArity atom with
  | inl cupArity =>
      obtain ⟨hasCupDomArity, hasCupCodArity⟩ := cupArity
      have cupInRange : atom.leftContext.length ≤ state.openWires.length := by
        rw [entryShape, hasCupDomArity, Nat.add_zero]
        exact Nat.le_add_right atom.leftContext.length atom.rightContext.length
      rw [stepArcAtom_eq_stepCupArc state atom hasCupDomArity hasCupCodArity]
      exact arcPerfectMatchingTokens_stepCupArc seedBoundary state atom.leftContext.length
        fresh forest seedBelowFresh cupInRange oldPerfect
  | inr capArity =>
      obtain ⟨hasCapDomArity, hasCapCodArity⟩ := capArity
      have capInRange : atom.leftContext.length + 2 ≤ state.openWires.length := by
        rw [entryShape, hasCapDomArity]
        exact Nat.le_add_right (atom.leftContext.length + 2) atom.rightContext.length
      rw [stepArcAtom_eq_stepCapArc state atom hasCapDomArity hasCapCodArity]
      exact arcPerfectMatchingTokens_stepCapArc seedBoundary state atom.leftContext.length
        forest capInRange census oldPerfect

/-! ## The whole-fold transport and the canonical-seed capstone -/

/-- ★ **A chained string spine's arc fold preserves the token-frame perfect matching end-to-end** — the
freshness / forestness / boundary-tracking / seed-bound / census companions thread through the fold exactly as in
the census fold, and each atom's step preserves the perfect matching by the per-atom dispatch.  The string port of
`arcPerfectMatchingTokens_processArcSpine_ofChained`. -/
theorem stringArcPerfectMatchingTokens_processArcSpine_ofChained
    {overallSource overallTarget : adjointTripleGraph.Mode} :
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)) →
    (state : ArcWireState) → (boundaryLength seedBoundary : Nat) →
    ArcStateFresh state → isUnionFindForest state.links →
    state.openWires.length = boundaryLength →
    SpineBoundaryChained boundaryLength atoms →
    seedBoundary ≤ state.nextFresh →
    ArcBoundaryCensus seedBoundary state →
    ArcPerfectMatchingTokens seedBoundary state →
    ArcPerfectMatchingTokens seedBoundary (processArcSpine state atoms)
  | [], _, _, _, _, _, _, _, _, _, perfect => perfect
  | headAtom :: restAtoms, state, _, seedBoundary, fresh, forest, tracks, chained,
      seedBelowFresh, census, perfect => by
      obtain ⟨headFires, tailChained⟩ := spineBoundaryChained_tail chained
      have tracksEntry : state.openWires.length = headAtom.domBoundaryLength :=
        tracks.trans headFires.symm
      have headArity := adjointTripleSpineAtom_hasCupOrCapArity headAtom
      show ArcPerfectMatchingTokens seedBoundary
        (processArcSpine (stepArcAtom state headAtom) restAtoms)
      exact stringArcPerfectMatchingTokens_processArcSpine_ofChained restAtoms
        (stepArcAtom state headAtom) headAtom.codBoundaryLength seedBoundary
        (arcStateFresh_stepArcAtom state headAtom fresh)
        (isUnionFindForest_stepArcAtom_ofCupOrCap state headAtom headArity forest)
        (stepArcAtom_openWires_tracksBoundary state headAtom headArity tracksEntry)
        tailChained
        (Nat.le_trans seedBelowFresh (stepArcAtom_nextFresh_le state headAtom))
        (stringArcBoundaryCensus_stepArcAtom seedBoundary state headAtom fresh forest
          seedBelowFresh tracksEntry census)
        (stringArcPerfectMatchingTokens_stepArcAtom seedBoundary state headAtom fresh forest
          seedBelowFresh tracksEntry census perfect)

/-- ★ **The perfect-matching capstone at the canonical seed**: every boundary-chained walking-adjoint-triple spine
folds from the fresh initial state to a state whose every boundary token has a distinct same-component boundary
token — i.e. no fixed point, the short-chord planar lemma's third hypothesis. -/
theorem stringArcPerfectMatchingTokens_ofChainedSpineList
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (bottomCount : Nat)
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained bottomCount atoms) :
    ArcPerfectMatchingTokens bottomCount
      (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        atoms) :=
  stringArcPerfectMatchingTokens_processArcSpine_ofChained atoms
    (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) bottomCount bottomCount
    (arcStateFresh_initial bottomCount) isUnionFindForest_nil (rangeLengthPMF bottomCount)
    chained (Nat.le_refl bottomCount) (arcBoundaryCensus_initial bottomCount)
    (arcPerfectMatchingTokens_initial bottomCount)

/-! ## Concrete truth-probes -/

/-! ### P1 — the genuine NON-DEGENERATE WIDE valley `[ε] ++ [η']` at `bottomCount = 4`, mid-width `2`.

The cap `ε` carries a length-`2` left context (`stringGF`), so from the width-`4` seed it consumes wires `2, 3`
leaving survivors `{0, 1}` — a real mid-width `2`, unreachable by the empty-context probes (whose caps always fire
at width `2` and collapse the valley to mid-width `0`). -/

/-- A WIDE CAP spine atom at `tip`: the lower counit `ε : G·F ⇒ id_tip` with a length-`2` LEFT context `stringGF`.
Left context `2`, window `stringGF` (`2`), cod `id_tip` (`0`) ⇒ `domBoundaryLength = 4`, `codBoundaryLength = 2`. -/
def stringWideProbeCapAtom :
    SpineAtom adjointTripleModeSignature AdjointTripleMode.tip AdjointTripleMode.tip :=
  ⟨AdjointTripleMode.tip, AdjointTripleMode.tip, stringGF, stringGF,
    ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip,
    StringTwoCell.counitLower,
    ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip⟩

/-- A WIDE CUP spine atom at `tip`: the upper unit `η' : id_tip ⇒ G·H` with a length-`2` LEFT context `stringGF`.
Left context `2`, window `id_tip` (`0`), cod `stringGH` (`2`) ⇒ `domBoundaryLength = 2`, `codBoundaryLength = 4` —
the same-endpoint partner of the wide cap, chaining from its mid-width `2`. -/
def stringWideProbeCupAtom :
    SpineAtom adjointTripleModeSignature AdjointTripleMode.tip AdjointTripleMode.tip :=
  ⟨AdjointTripleMode.tip, AdjointTripleMode.tip, stringGF,
    ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip,
    stringGH, StringTwoCell.unitUpper,
    ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip⟩

/-- The whole wide valley is boundary-chained at `bottomCount = 4`: the cap fires at width `4`, drops to `2`, the
cup fires at width `2`, rises to `4`. -/
theorem stringWideProbeValley_chained :
    SpineBoundaryChained 4 ([stringWideProbeCapAtom] ++ [stringWideProbeCupAtom]) :=
  SpineBoundaryChained.cons stringWideProbeCapAtom rfl
    (SpineBoundaryChained.cons stringWideProbeCupAtom rfl (SpineBoundaryChained.nil 4))

/-- ★ **The wide valley is genuinely NON-DEGENERATE: mid-width `2`.**  A machine-checked (`decide`) cross-check
that the cap block alone, folded from the width-`4` arc seed, leaves `2` open wires — the cap consumes `2` of the
`4` bottom wires, so survivors `{0, 1}` remain and the mid boundary is a real width `2`, NOT zero. -/
theorem stringWideProbe_midWidth_isTwo :
    (processArcSpine (ArcWireState.mk (List.range 4) [] 4 0 [] [])
        [stringWideProbeCapAtom]).openWires.length = 2 := by decide

/-- ★ **The census capstone FIRES on the genuine non-degenerate wide valley.**  On the concrete valley
`[ε] ++ [η']` at `bottomCount = 4` (mid-width `2`), the whole arc fold from the fresh seed carries the two-endpoint
boundary census end-to-end — a real inhabitation over a valley with non-zero mid content, not vacuous. -/
theorem stringArcBoundaryCensus_firesOnWideValley :
    ArcBoundaryCensus 4
      (processArcSpine (ArcWireState.mk (List.range 4) [] 4 0 [] [])
        ([stringWideProbeCapAtom] ++ [stringWideProbeCupAtom])) :=
  stringArcBoundaryCensus_ofChainedSpineList 4
    ([stringWideProbeCapAtom] ++ [stringWideProbeCupAtom]) stringWideProbeValley_chained

/-- ★ **The perfect-matching capstone FIRES on the genuine non-degenerate wide valley.**  On the same wide valley
the arc fold carries the token-frame perfect matching end-to-end: every boundary token of the folded state has a
distinct same-component partner — the `noFixedPoint` fact, established on a non-zero-mid-width valley. -/
theorem stringArcPerfectMatchingTokens_firesOnWideValley :
    ArcPerfectMatchingTokens 4
      (processArcSpine (ArcWireState.mk (List.range 4) [] 4 0 [] [])
        ([stringWideProbeCapAtom] ++ [stringWideProbeCupAtom])) :=
  stringArcPerfectMatchingTokens_ofChainedSpineList 4
    ([stringWideProbeCapAtom] ++ [stringWideProbeCupAtom]) stringWideProbeValley_chained

/-! ### P0 — the mid-zero smoke probe `[ε] ++ [η']` at `bottomCount = 2` (empty contexts).

The empty-context cap fires at width `2` and consumes both bottom wires (mid-width `0`); the "does it instantiate
at all" smoke test on the shipped width-telescope probe atoms. -/

/-- The whole mid-zero valley is boundary-chained at `bottomCount = 2`: the cap fires at width `2`, drops to `0`,
the cup fires at width `0`, rises to `2`. -/
theorem stringMidZeroProbeValley_chained :
    SpineBoundaryChained 2
      ([stringWidthTelescopeProbeCapAtom] ++ [stringWidthTelescopeProbeCupAtom]) :=
  SpineBoundaryChained.cons stringWidthTelescopeProbeCapAtom rfl
    (SpineBoundaryChained.cons stringWidthTelescopeProbeCupAtom rfl (SpineBoundaryChained.nil 2))

/-- ★ **The census capstone smoke-fires on the mid-zero valley.**  The empty-context valley `[ε] ++ [η']` at
`bottomCount = 2` instantiates the census transport end-to-end — the cheap "does it instantiate" check. -/
theorem stringArcBoundaryCensus_firesOnMidZeroValley :
    ArcBoundaryCensus 2
      (processArcSpine (ArcWireState.mk (List.range 2) [] 2 0 [] [])
        ([stringWidthTelescopeProbeCapAtom] ++ [stringWidthTelescopeProbeCupAtom])) :=
  stringArcBoundaryCensus_ofChainedSpineList 2
    ([stringWidthTelescopeProbeCapAtom] ++ [stringWidthTelescopeProbeCupAtom])
    stringMidZeroProbeValley_chained

/-- ★ **The perfect-matching capstone smoke-fires on the mid-zero valley.** -/
theorem stringArcPerfectMatchingTokens_firesOnMidZeroValley :
    ArcPerfectMatchingTokens 2
      (processArcSpine (ArcWireState.mk (List.range 2) [] 2 0 [] [])
        ([stringWidthTelescopeProbeCapAtom] ++ [stringWidthTelescopeProbeCupAtom])) :=
  stringArcPerfectMatchingTokens_ofChainedSpineList 2
    ([stringWidthTelescopeProbeCapAtom] ++ [stringWidthTelescopeProbeCupAtom])
    stringMidZeroProbeValley_chained

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the string arc-engine census + perfect-matching FOLD TRANSPORT is SHIPPED, zero-axiom
(FC-3 r30, B1).**  Landed here over the walking ADJOINT-TRIPLE signature, as the deepest layer of the M2c cap
subtree:

  * `stringArcBoundaryCensus_stepArcAtom` / `_processArcSpine_ofChained` / `_ofChainedSpineList` — the per-atom
    census step, the whole-fold transport, and the canonical-seed capstone: every boundary-chained string spine
    folds from the fresh seed to a state whose every union-find component touches at most two boundary endpoints.
  * `stringArcPerfectMatchingTokens_stepArcAtom` / `_processArcSpine_ofChained` / `_ofChainedSpineList` — the
    per-atom step (threading the census for the cap), the whole-fold transport, and the canonical-seed capstone:
    every boundary token of the folded state has a distinct same-component partner (the `noFixedPoint` fact).

  The arc engine is signature-BLIND: every per-atom step / preservation worker is stated over the bare
  `ArcWireState` / a `{signature}`-generic `SpineAtom`, so it is REUSED verbatim by import.  The ONE signature-keyed
  hook — the cup/cap arity dispatch — is supplied by the shipped `adjointTripleSpineAtom_hasCupOrCapArity`, the direct
  four-generator analog of `adjunctionSpineAtom_hasCupOrCapArity`.  Every brick is a byte-identical token-swap of the
  walking-adjunction `ArcCensusFold` / `ArcPerfectMatchingFold` original — no new mathematics, no unproven residual.

  Two truth-probes fire the capstones end-to-end: the genuine NON-DEGENERATE WIDE valley `[ε] ++ [η']` at
  `bottomCount = 4` (length-`2` cap context → mid-width `2`, pinned by a `decide` cross-check
  `stringWideProbe_midWidth_isTwo` — the first non-zero-mid-width probe in this arc), and the mid-zero valley at
  `bottomCount = 2` as the instantiation smoke test.

  What this marker does NOT claim (honestly), and what the M2c cap subtree still needs above it:
    * the involution / no-fixed-point transport `stringArcDiagramPartnerReadAt` / `stringArcDiagram_partner_isInvolution`
      / `stringMatchingOf_partner_isInvolution` / `_neSelf` (B3) that CONSUMES these folds;
    * the cap-CONSUMED / survivor-bottom partner legs (B4) and the top + splitters
      `stringCapRestrict_reconstructs` / `stringSameWholeMatching_capBlockMatchingEq` (B5).

  So `stringSameWholeMatching_capBlockMatchingEq` (M2c cap) stays un-landed, and
  `fxString_hasAdjointTripleCompleteness` / `fxString_hasConvOfMapEqPortFlip` stay `false`.  This round flips ONLY
  this NEW marker: B1 is shipped as the arc-engine floor of the M2c cap subtree.  `= true`. -/
def fxString_hasArcCensusPerfectMatchingFold : Bool := true

end FX1Poly.Polygraph
