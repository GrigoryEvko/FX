import FX1Poly.Polygraph.TwoCategory.WalkingString.StringFussCatalanStaircaseDriver

/-! # WalkingString — the RECONSTRUCTION-ROUTE realization: `reconstruct` as a FUNCTION OF THE MATCHING (FC-8)

FC-6 (`StringMatchingReconstructionInterface`) reduced the whole adjoint-triple completeness + decision to ONE
obligation per route, and singled out `StringMatchingReconstruction` (a `reconstruct` function producing a canonical
cell from a `DiagramType`, plus `convToReconstruct : cell ≈ reconstruct (matchingOf cell)`) as the CLEANER primitive:
because `reconstruct` is a FUNCTION OF THE MATCHING, canonicalization of a matching-equal pair is free (`congrArg`),
so the `SpineTraceEquiv` conjunct collapses to `refl` with NO injective-normal-form machinery.  FC-7
(`StringFussCatalanStaircaseDriver`) then WALLED the competing `StringFcNormalizer` route with a machine-witnessed
finding: the spine-tag normal form is NOT matching-determined (`stringStaircaseNormalForm_not_matchingDetermined` —
`id_G` and `id_G ⊟ id_G` are both staircase-normal, matching-equal, yet DISTINCT raw terms), so
`matchingInjectiveOnNormalForms` cannot hold for any spine-valley normalizer.

This file takes the RECONSTRUCTION route (interface 1, the recon's bridge pick) and ships its realizable core:

## P1 — `reconstruct` on the realizable fragments, with the three recon evals

  * ★ `stringReconstructIdentityForm` — the ENDO specialization of `reconstruct`: at a boundary `path ⇒ path` the
    only seed-realizable base matching is the through-strand, whose canonical representative is the identity cell.
    It is a genuine `DiagramType → RawTwoCellExpr path path` (the diagram argument is present, exactly the interface
    shape, but at an endo seed boundary it is determined).  The literature-sanctioned unit-free reading of the
    identity/transversal-only diagram (East's `k = 0` / empty-tuple case, "by planarity `α = idₙ`").
  * ★ `stringReconstructCrossLevel` — the NON-endo `G·F ⇒ G·H` realization: the reconstruction IS the valley
    (`stringCrossLevelCell`), a cap-then-cup rainbow with zero residual moves.
  * the THREE recon evals: (A) the `F`-snake reconstructs to `id_F`; (B) the FC-7 counterexample pair COLLAPSES —
    `id_G` and `id_G ⊟ id_G` map to the SAME reconstruction `id_G`, each convertible to it, so the reconstruction
    route SIDESTEPS FC-7's obstruction #1 at the convertibility level (no injectivity needed); (C) the cross-level
    cap+cup cell reconstructs to itself.

## P2 — `convToReconstruct` on the closed fragments; the general bridge is the standing residual

The `convToReconstruct` obligation `cell ≈ reconstruct (matchingOf cell)` CLOSES outright on the straightenable
fragment: every `F`-snake stack reconstructs to `id_F` (the shipped `stringSnakeStackF_reconstructsToIdentityF`), the
FC-7 pair to `id_G`, the cross-level cell to itself.  What does NOT close — and is the SAME per-head cup/cap bubble
the walking adjunction's `fxMode_hasArcCellReconstruction` leaves open — is the GENERAL `convToReconstruct`: bridging
an arbitrary descended valley to THE rainbow representative is a chain of colour-aware Godement / free-interchange
moves (`StringCellValleyTraceEquiv`, the `StringMatchingValleyDescent` Piece-II residual), NOT a term-rewriting
confluence.  So the full `StringMatchingReconstruction` structure is NOT inhabited this round and
`fxString_hasAdjointTripleCompleteness` stays `false`, honestly.

## P5 — the sharpening: matching + boundary labels UNDER-determine the raw term (obstruction #2 named)

The recon's route choice is justified by a companion to FC-7's finding at a strictly SHARPER granularity.  FC-7's
pair differs by UNIT padding (an `id` slot); the two `G ⇒ G` snakes `stringSnakeGlo` (colour 1) and `stringSnakeGhi`
(colour 2) differ by COLOUR: they have IDENTICAL boundary (`[G] ⇒ [G]`), IDENTICAL `matchingOf` (both the
through-strand), are saturated-convertible — yet carry DIFFERENT generators (`η`/`ε` vs `η'`/`ε'`) of equal size, so
they are NOT unit-padding variants.  This is the Cartier–Foata / colour-interleave obstruction #2: matching (and even
boundary labels, identical here) forgets generator colour.  It is exactly WHY the reconstruction must be a FUNCTION OF
THE MATCHING (both snakes get the SAME reconstruction `id_G`) rather than an injective normalizer — the reconstruction
route dissolves the obstruction by construction, where the normalizer route hits it as a wall.

## P4 — the Fuss–Catalan count cross-check at two arcs

The reconstruction targets are the FC diagrams; their count at `n = 2` arcs is `FC_2 = 3`
(`fussCatalanNumber 2 = 3`), the shipped fingerprint — a cross-check that the reconstruct's image is the FC-diagram
set, not a proven enumeration.

Raw Lean 4 + Init; the reconstruct is a total identity/valley realization, the evals are shipped triangle / EXTEND /
`refl` chains, the count a `decide`.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free;
per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## P1 — `reconstruct` on the realizable fragments -/

/-- ★ **The ENDO specialization of `reconstruct`** — at a boundary `path ⇒ path` the seed-realizable base matching
is the through-strand (every port matched straight across), whose canonical FC representative is the identity cell.
This is the interface's `reconstruct` shape (a `DiagramType → RawTwoCellExpr …`) at the endo diagonal: the diagram
datum is PRESENT but, at the walking-adjoint-triple seed, determined (a through-strand is the empty / `k = 0` FC
word, "`α = idₙ` by planarity").  The full off-diagonal `reconstruct` (an arbitrary parallel boundary + a nontrivial
matching) is the standing residual — see the honesty markers. -/
def stringReconstructIdentityForm {sourceMode targetMode : AdjointTripleMode}
    (path : ModalityPath adjointTripleGraph sourceMode targetMode) (_diagram : DiagramType) :
    RawTwoCellExpr adjointTripleModeSignature path path :=
  RawTwoCellExpr.id (signature := adjointTripleModeSignature) path

/-- ★ **The cross-level `G·F ⇒ G·H` reconstruction** — the reconstruction of the cross-level boundary IS the valley
`stringCrossLevelCell` (the lower counit `ε` closing `G·F`, then the upper unit `η'` opening `G·H`): a cap-then-cup
rainbow already in canonical form.  Zero residual moves separate it from the descended valley. -/
def stringReconstructCrossLevel : RawTwoCellExpr adjointTripleModeSignature stringGF stringGH :=
  stringCrossLevelCell

/-! ## P1 — eval A: the `F`-snake reconstructs to `id_F` -/

/-- The reconstruction of the `F`-boundary identity form IS `stringIdentityF` (definitionally — both are the identity
2-cell on the `F` strand). -/
theorem stringReconstructIdentityForm_left_eq_identityF (diagram : DiagramType) :
    stringReconstructIdentityForm (singletonModalityPath AdjointTripleModality.left) diagram = stringIdentityF :=
  rfl

/-- ★★ **Eval A — the `F`-snake satisfies `convToReconstruct`.**  `stringSnakeF` is saturated-convertible to the
reconstruction of its own boundary matching, `stringReconstructIdentityForm [F] (matchingOf stringSnakeF)` (which is
`stringIdentityF`), by the `F` triangle.  The `convToReconstruct` obligation holds on the snake — its reconstruction
is the identity, and the snake straightens to it. -/
theorem stringReconstruct_snakeF_convToReconstruct :
    StringSaturatedTwoCellConv stringSnakeF
      (stringReconstructIdentityForm (singletonModalityPath AdjointTripleModality.left)
        (matchingOf stringSnakeF)) :=
  StringSaturatedTwoCellConv.triangleF

/-! ## P1 — eval B: the FC-7 counterexample pair COLLAPSES under reconstruction -/

/-- The reconstruction of `id_G`'s boundary form IS `stringIdentityG` (definitionally). -/
theorem stringReconstructIdentityForm_right_eq_identityG (diagram : DiagramType) :
    stringReconstructIdentityForm (singletonModalityPath AdjointTripleModality.right) diagram = stringIdentityG :=
  rfl

/-- ★★ **Eval B — the reconstruction COLLAPSES the FC-7 counterexample pair.**  FC-7's
`stringStaircaseNormalForm_not_matchingDetermined` walls the injective-normalizer route with two distinct
matching-equal staircase-normal cells `id_G` and `id_G ⊟ id_G`.  The RECONSTRUCTION route dissolves that wall: since
`reconstruct` is a function of the matching and `matchingOf (id_G ⊟ id_G) = matchingOf id_G`
(`stringIdentityG_matchingOf_vcomp_eq`), BOTH cells reconstruct to the SAME cell `id_G` (`congrArg`), and each is
saturated-convertible to it — `id_G ⊟ id_G ≈ id_G` by EXTEND, `id_G ≈ id_G` by reflexivity.  So FC-7's obstruction #1
never arises for the reconstruction route: no injectivity, no per-spine raw pinning — the reconstructions coincide by
construction and the `SpineTraceEquiv` conjunct is `refl`. -/
theorem stringReconstruct_collapses_fc7Pair :
    stringReconstructIdentityForm (singletonModalityPath AdjointTripleModality.right)
        (matchingOf (RawTwoCellExpr.vcomp stringIdentityG stringIdentityG))
      = stringReconstructIdentityForm (singletonModalityPath AdjointTripleModality.right)
          (matchingOf stringIdentityG)
    ∧ StringSaturatedTwoCellConv (RawTwoCellExpr.vcomp stringIdentityG stringIdentityG)
        (stringReconstructIdentityForm (singletonModalityPath AdjointTripleModality.right)
          (matchingOf (RawTwoCellExpr.vcomp stringIdentityG stringIdentityG)))
    ∧ StringSaturatedTwoCellConv stringIdentityG
        (stringReconstructIdentityForm (singletonModalityPath AdjointTripleModality.right)
          (matchingOf stringIdentityG)) :=
  ⟨congrArg (stringReconstructIdentityForm (singletonModalityPath AdjointTripleModality.right))
      stringIdentityG_matchingOf_vcomp_eq,
    stringExtendByIdentity stringIdentityG,
    StringSaturatedTwoCellConv.refl stringIdentityG⟩

/-! ## P1 — eval C: the cross-level cap+cup cell reconstructs to itself -/

/-- ★ **Eval C — the cross-level cell's base matching** — two caps/cups across the shared `G`:
`{ bottomCount := 2, topCount := 2, partner := [1, 0, 3, 2], loops := 0 }`, the `.base` of its two-level matching
(`stringCrossLevel_colouredMatchingOf`).  The reconstruction reads this partner data and colour-resolves each pair by
the boundary labels (`[G, F] ⇒ [G, H]`) to the lower counit `ε` and the upper unit `η'`. -/
theorem stringReconstructCrossLevel_matchingOf :
    matchingOf stringReconstructCrossLevel
      = { bottomCount := 2, topCount := 2, partner := [1, 0, 3, 2], loops := 0 } :=
  rfl

/-- ★★ **Eval C — the cross-level cell satisfies `convToReconstruct` by reflexivity.**  `stringCrossLevelCell` IS its
own reconstruction (a cap-then-cup valley already in canonical rainbow form), so `cell ≈ reconstruct (matchingOf
cell)` is `refl` — zero residual moves, the descended valley coincides with the rainbow representative. -/
theorem stringReconstruct_crossLevel_convToReconstruct :
    StringSaturatedTwoCellConv stringCrossLevelCell stringReconstructCrossLevel :=
  StringSaturatedTwoCellConv.refl stringCrossLevelCell

/-! ## P2 — `convToReconstruct` closes on the whole straightenable `F`-snake-stack family -/

/-- ★★ **`convToReconstruct` on the infinite `F`-snake-stack family.**  For every `n`, the `n`-fold `F`-snake stack
is saturated-convertible to the reconstruction of its own boundary matching, `stringReconstructIdentityForm [F]
(matchingOf (stringSnakeStackF n))` (which is `stringIdentityF`), AND the two share a boundary matching.  This is the
shipped `stringSnakeStackF_reconstructsToIdentityF` re-expressed against the reconstruct: the `convToReconstruct`
obligation is met UNCONDITIONALLY on a genuine infinite family of real cells, `id_F` the matching-determined
canonical form of every snake stack. -/
theorem stringReconstruct_snakeStackF_convToReconstruct (count : Nat) :
    StringSaturatedTwoCellConv (stringSnakeStackF count)
      (stringReconstructIdentityForm (singletonModalityPath AdjointTripleModality.left)
        (matchingOf (stringSnakeStackF count)))
    ∧ matchingOf (stringSnakeStackF count)
      = matchingOf (stringReconstructIdentityForm (singletonModalityPath AdjointTripleModality.left)
          (matchingOf (stringSnakeStackF count))) :=
  stringSnakeStackF_reconstructsToIdentityF count

/-! ## P5 — the sharpening: matching + boundary labels UNDER-determine the raw term (obstruction #2) -/

/-- The two distinct `G ⇒ G` snakes have EQUAL base matching (both the through-strand `id_G` matching) — via the two
triangle collapses. -/
theorem stringSnakeGlo_snakeGhi_matchingOf_eq :
    matchingOf stringSnakeGlo = matchingOf stringSnakeGhi :=
  matchingOf_stringTriangleGlo.trans matchingOf_stringTriangleGhi.symm

/-- The lower `G`-snake is DISTINCT from `id_G` (head `vcomp` vs `id`) yet carries two REAL generators (`η`, `ε`),
so it is a genuine non-unit witness — not an inserted `id` slot. -/
theorem stringSnakeGlo_ne_identityG : stringSnakeGlo ≠ stringIdentityG := by
  intro equalTerms
  nomatch equalTerms

/-- The upper `G`-snake is likewise DISTINCT from `id_G`, carrying the OTHER colour's generators (`η'`, `ε'`). -/
theorem stringSnakeGhi_ne_identityG : stringSnakeGhi ≠ stringIdentityG := by
  intro equalTerms
  nomatch equalTerms

/-- ★★ **The sharpening — matching + boundary labels UNDER-determine the raw term BEYOND unit padding.**  The two
`G ⇒ G` snakes `stringSnakeGlo` (colour 1) and `stringSnakeGhi` (colour 2) have IDENTICAL boundary (`[G] ⇒ [G]`,
so identical `pathLabels`), IDENTICAL base matching (`stringSnakeGlo_snakeGhi_matchingOf_eq`), are
saturated-convertible (`stringSnakeGlo_conv_stringSnakeGhi`, both through `id_G`) — yet each is a DISTINCT non-unit
cell (two real generators, distinct from `id_G` by head constructor).  This SHARPENS FC-7's finding: FC-7's pair
`id_G` / `id_G ⊟ id_G` differs by UNIT padding (an `id` slot, `stringStaircaseNormalForm_not_matchingDetermined`);
this pair differs by COLOUR (`η`/`ε` vs `η'`/`ε'`), which NO amount of matching or boundary-label reading can
separate — the exact Cartier–Foata / colour-interleave obstruction #2.  It is precisely WHY the reconstruction must
be a FUNCTION OF THE MATCHING: `reconstruct` maps BOTH snakes to the SAME `id_G`, dissolving the non-determination by
construction, where an injective normalizer would hit it as a wall. -/
theorem stringReconstruct_matchingUnderdeterminesColour :
    matchingOf stringSnakeGlo = matchingOf stringSnakeGhi
      ∧ StringSaturatedTwoCellConv stringSnakeGlo stringSnakeGhi
      ∧ stringSnakeGlo ≠ stringIdentityG
      ∧ stringSnakeGhi ≠ stringIdentityG :=
  ⟨stringSnakeGlo_snakeGhi_matchingOf_eq, stringSnakeGlo_conv_stringSnakeGhi,
    stringSnakeGlo_ne_identityG, stringSnakeGhi_ne_identityG⟩

/-! ## P4 — the Fuss–Catalan count cross-check at two arcs -/

/-- ★ **The reconstruction-target count at two arcs is `FC_2 = 3`.**  The reconstruction targets are the FC
diagrams; their count at `n = 2` arcs is the shipped Fuss–Catalan fingerprint `fussCatalanNumber 2 = 3`.  A
cross-check that the reconstruct's image is the FC-diagram set (not a proven enumeration of the reconstruct's range).
`decide`. -/
theorem stringReconstructTargetCount_two : fussCatalanNumber 2 = 3 := by decide

/-! ## Honesty markers -/

/-- **★ ESTABLISHED — the RECONSTRUCTION-ROUTE realizable core is shipped.**  `stringReconstructIdentityForm` (the
endo through-strand reconstruction) and `stringReconstructCrossLevel` (the `G·F ⇒ G·H` valley reconstruction) realize
`reconstruct` on the seed's realizable fragments, computing on the three recon evals: (A) the `F`-snake
`convToReconstruct` by the triangle (`stringReconstruct_snakeF_convToReconstruct`); (B) the FC-7 counterexample pair
COLLAPSES — `id_G` and `id_G ⊟ id_G` reconstruct to the SAME `id_G`, each convertible to it
(`stringReconstruct_collapses_fc7Pair`), so FC-7's obstruction #1 never arises for the reconstruction route (no
injectivity); (C) the cross-level cap+cup cell reconstructs to itself (`stringReconstruct_crossLevel_convToReconstruct`,
base matching `{2,2,[1,0,3,2],0}`).  The `convToReconstruct` obligation CLOSES on the whole infinite `F`-snake-stack
family (`stringReconstruct_snakeStackF_convToReconstruct`).  The route choice is justified by the sharpening
(`stringReconstruct_matchingUnderdeterminesColour`): the two `G ⇒ G` snakes are matching-equal, boundary-equal, and
convertible yet colour-distinct — obstruction #2, dissolved by making `reconstruct` a function of the matching.
`= true`. -/
def fxString_hasReconstructionRainbowRealized : Bool := true

/-- **OPEN (honest) — the GENERAL `convToReconstruct` is the standing residual; NO completeness flip.**  The full
`StringMatchingReconstruction` structure is NOT inhabited this round: `stringReconstructIdentityForm` realizes only the
ENDO through-strand and `stringReconstructCrossLevel` only the one cross-level valley, and `convToReconstruct` is
proved only on the straightenable fragments (`F`-snake stacks, the FC-7 pair, the cross-level valley).  The GENERAL
obligation — bridging an arbitrary descended valley (`stringValleyNFCell`, `StringMatchingValleyDescent`) to THE
rainbow representative — is the colour-aware Godement / free-interchange chain `StringCellValleyTraceEquiv`, the SAME
per-head cup/cap bubble the walking adjunction's `fxMode_hasArcCellReconstruction` leaves open (there is no citable
free-adjoint-STRING word-problem normal-form theorem; Schanuel–Street / Riehl–Verity decide only the SINGLE
adjunction).  This is NOT a term-rewriting confluence but a soundness-preserving reordering of disjoint intra-block
turnbacks, colour-keyed by the boundary labels.  So `StringMatchingReconstruction` stays un-inhabited,
`decidableStringSaturatedConv_ofReconstruction` does not fire, and `fxString_hasAdjointTripleCompleteness` (in
`StringMatchingCompleteness`) stays `false`, honestly — the residual now localized to this one named geometric
obligation.  `= false`. -/
def fxString_hasReconstructionRouteFlip : Bool := false

end FX1Poly.Polygraph
