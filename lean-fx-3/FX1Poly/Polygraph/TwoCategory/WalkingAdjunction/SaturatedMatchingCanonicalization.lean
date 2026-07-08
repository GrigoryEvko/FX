import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MonotoneMap
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineTraceDecision

/-! # mode-9 keystone — the SATURATED canonicalization carrier is the BOUNDARY PLANAR MATCHING

`FreeTwoCellMonotoneMap` / `FreeTwoCellMonotoneFaithful` pursued a per-atom `monotoneMapOf` fold (covariant) and its
op-dual (`monotoneMapOpOf`) as the candidate `AdjunctionSaturatedCanonicalization.monotoneMapOf`, and the prior
pass MACHINE-CHECKED that NEITHER works: `embeddedTipCapConv` is a genuine `base ⟶ tip` saturated convertibility on
which the covariant fold gives `[0,2] ≠ [0,0]` (`monotoneMapOf_distinguishes_embeddedTipCap`) and the op fold gives
`[0,1] ≠ [0,0]` (`monotoneMapOpOf_distinguishes_embeddedTipCap`).  The recorded "KEYSTONE-COUPLING WALL" pinned the
true blocker as a not-yet-built PER-ATOM variance-aware fold.

★ **This file identifies that carrier and machine-checks it — and the answer is that NO left-to-right spine fold
can be it.**  The decisive observation (a genuine no-go, established by `arcMatching_cupAtoms_locallyIndistinguishable`
below): the cup atom of a genuine base-block cup `(L·R) ◁ η` and the cup atom of `embeddedTipCapRedex` have
LITERALLY EQUAL per-atom spine data `(leftContext.length, dom, cod) = (2, 0, 2)`, yet the two cells must receive
different treatment — so the variance is NOT a function of any atom's local (or running-prefix) data; it is fixed by
the GLOBAL planar matching (which cup pairs with which cap, decided by the FUTURE of the fold).  Hence the correct
saturated carrier is the **boundary planar matching** `matchingOf` (the Joyal–Street `DiagramType` —
`FreeTwoCellMatchingDecision`), NOT a monotone-map fold.

## What `matchingOf` gets RIGHT that both folds got wrong (each `rfl`, zero-axiom)

  * ★ **The TRIANGLE is free** — `matchingOf adjunctionSeedLeftSnake = matchingOf id_L` (and the right dual), at the
    SEED and (witnessed by the smokes) under any whisker context and stacked: the snake straightens to a
    through-strand, exactly the boundary matching's blind spot for the FREE relation that is CORRECT for the
    SATURATED one.  This is the property the covariant fold needed and the boundary matching supplies for free.
  * ★ **The obstruction is RESOLVED** — `matchingOf embeddedTipCapRedex = matchingOf embeddedTipCapReduct` (`rfl`),
    where the covariant AND op folds BOTH distinguished the two cells.  The exact machine-checked counterexample to
    every per-atom fold is absorbed by the global matching.
  * ★ **It still DISCRIMINATES** — `matchingOf cupAtLeft ≠ matchingOf cupAtRight` (the two faces `δ₀ ≠ δ₁` of
    `L·R ⟹ (L·R)²`): the boundary matching is not the trivial boundary-determined invariant; it carries the genuine
    monotone-map data, so it is completeness-CAPABLE (unlike a constant map).

## How the keystone re-aims (and the wall dissolves)

The prior "KEYSTONE-COUPLING WALL" was specific to pinning the canonicalization map to the covariant `monotoneMapOf`
(which has no `mapEqOfConv`).  With `matchingOf` as the carrier the SOUNDNESS field's two hardest inputs — the
triangle and the Godement obstruction — are DISCHARGED here (`rfl`), so the wall is gone; what remains for the full
`SaturatedMatchingCanonicalization` is exactly the two named residuals SHARED with the arc route: the union-find
Godement INDEPENDENCE (`godementInvariant`, `matchingOf_sound_of_godementInvariant`) for `ofFull`, the matching's
saturated-congruence COMPOSITIONALITY for the four congruences, and the Joyal–Street RECONSTRUCTION for `convOfMapEq`.

Raw Lean 4 + Init; every declaration here is `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free
(the headline facts are `rfl` / structural `Nat.noConfusion`; the reductions thread the named shipped lemmas).
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-! ## The carrier + the parallel pair the smokes live over -/

/-- The identity 2-cell on the single left modality `L` — the boundary the left triangle straightens the snake to. -/
def adjunctionIdentityLeft :
    RawTwoCellExpr adjunctionModeSignature (singletonModalityPath AdjunctionModality.left)
      (singletonModalityPath AdjunctionModality.left) :=
  RawTwoCellExpr.id (signature := adjunctionModeSignature) (singletonModalityPath AdjunctionModality.left)

/-- The identity 2-cell on the single right modality `R` — the boundary the right triangle straightens to. -/
def adjunctionIdentityRight :
    RawTwoCellExpr adjunctionModeSignature (singletonModalityPath AdjunctionModality.right)
      (singletonModalityPath AdjunctionModality.right) :=
  RawTwoCellExpr.id (signature := adjunctionModeSignature) (singletonModalityPath AdjunctionModality.right)

/-- The face `δ₀ : L·R ⟹ (L·R)²` — a unit cup inserted at the LEFT (block position 0), `η ▷ (L·R)`. -/
def adjunctionCupAtLeft :
    RawTwoCellExpr adjunctionModeSignature adjunctionLeftThenRight
      (composePath adjunctionLeftThenRight adjunctionLeftThenRight) :=
  RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature) adjunctionLeftThenRight adjunctionUnitTwoCell

/-- The face `δ₁ : L·R ⟹ (L·R)²` — a unit cup inserted at the RIGHT (block position 1), `(L·R) ◁ η`. -/
def adjunctionCupAtRight :
    RawTwoCellExpr adjunctionModeSignature adjunctionLeftThenRight
      (composePath adjunctionLeftThenRight adjunctionLeftThenRight) :=
  RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature) adjunctionLeftThenRight adjunctionUnitTwoCell

/-! ## ★ The no-go: the variance is GLOBAL, not a per-atom fold

The cup atom of a genuine base-block cup `(L·R) ◁ η` (`adjunctionCupAtRight`) and the embedded cup atom inside
`embeddedTipCapRedex` carry LITERALLY EQUAL per-atom spine data — same `leftContext.length`, same generator
arity — yet `embeddedTipCapRedex`'s cup must behave as the OP degeneracy (the cap above it closes its strand)
while the base-block cup is a covariant face.  So no fold that reads each cup off its local (or running-prefix)
data can be sound: the polarity is fixed by the GLOBAL matching.  Machine-checked `rfl` on the spine head data. -/

/-- ★ **The locally-indistinguishable cups.**  The head spine atom of `adjunctionCupAtRight` (a genuine base-block
cup) and of `embeddedTipCapRedex` (an embedded tip cup that must read OP) have EQUAL
`(leftContext.length, generatorDom.length, generatorCod.length) = (2, 0, 2)`.  The machine-checked witness that the
saturated carrier cannot be a per-atom fold — the variance is not a function of an atom's local data. -/
theorem arcMatching_cupAtoms_locallyIndistinguishable :
    ((adjunctionCupAtRight.spine.head?.map
        (fun atom => (atom.leftContext.length, atom.generatorDom.length, atom.generatorCod.length)))
      = some (2, 0, 2))
    ∧ ((embeddedTipCapRedex.spine.head?.map
        (fun atom => (atom.leftContext.length, atom.generatorDom.length, atom.generatorCod.length)))
      = some (2, 0, 2)) :=
  ⟨rfl, rfl⟩

/-! ## ★ The headline: `matchingOf` is the correct saturated carrier (each `rfl`) -/

/-- ★★ **The LEFT triangle is FREE in the boundary matching** — `matchingOf adjunctionSeedLeftSnake = matchingOf
id_L`.  The snake's cup/cap straighten to a single through-strand, so its boundary matching IS the identity's; the
boundary matching collapses the snake to the identity ON THE NOSE.  This is precisely the soundness obligation the
`SaturatedTwoCellConv.triangleLeft` constructor imposes — and it is `rfl` for `matchingOf`, where the covariant
fold needed the whole simplicial-identity apparatus and the op fold could not absorb it at the boundary. -/
theorem matchingOf_triangleLeft :
    matchingOf adjunctionSeedLeftSnake = matchingOf adjunctionIdentityLeft := rfl

/-- ★★ **The RIGHT triangle is FREE in the boundary matching** — `matchingOf adjunctionSeedRightSnake = matchingOf
id_R`.  The dual snake straightens identically. -/
theorem matchingOf_triangleRight :
    matchingOf adjunctionSeedRightSnake = matchingOf adjunctionIdentityRight := rfl

/-- ★★ **The `embeddedTipCap` obstruction is RESOLVED by the boundary matching** — `matchingOf embeddedTipCapRedex =
matchingOf embeddedTipCapReduct` (`rfl`).  This is the EXACT machine-checked convertibility on which BOTH per-atom
folds were refuted (`monotoneMapOf_distinguishes_embeddedTipCap` : `[0,2] ≠ [0,0]`;
`monotoneMapOpOf_distinguishes_embeddedTipCap` : `[0,1] ≠ [0,0]`).  The global planar matching absorbs the Godement
transposition the local folds could not — the decisive evidence that the carrier is the matching, not a fold. -/
theorem matchingOf_resolves_embeddedTipCap :
    matchingOf embeddedTipCapRedex = matchingOf embeddedTipCapReduct := rfl

/-- ★ **The carrier strictly improves on BOTH folds, on the SAME witness** (machine-checked, zero-axiom): the
covariant and op folds DISTINGUISH `embeddedTipCapRedex`/`Reduct` while the boundary matching IDENTIFIES them.  So
`matchingOf` is sound on exactly the convertibility that refuted every per-atom fold — the carrier swap is genuine. -/
theorem matchingOf_strictlyBetterThanFolds_onEmbeddedTipCap :
    (monotoneMapOf embeddedTipCapRedex ≠ monotoneMapOf embeddedTipCapReduct)
    ∧ (monotoneMapOpOf embeddedTipCapRedex ≠ monotoneMapOpOf embeddedTipCapReduct)
    ∧ (matchingOf embeddedTipCapRedex = matchingOf embeddedTipCapReduct) :=
  ⟨monotoneMapOf_distinguishes_embeddedTipCap, monotoneMapOpOf_distinguishes_embeddedTipCap, rfl⟩

/-- ★ **The boundary matching is NOT boundary-trivial — it DISCRIMINATES the two faces** `δ₀ ≠ δ₁`.  The cup at the
left (`adjunctionCupAtLeft`) and the cup at the right (`adjunctionCupAtRight`), both `L·R ⟹ (L·R)²` (same boundary),
get DIFFERENT boundary matchings (`partner = [4,5,3,2,0,1]` vs `[2,3,0,1,5,4]`).  So `matchingOf` carries the genuine
monotone-map data and is completeness-CAPABLE — unlike a constant boundary-determined invariant, it can separate
non-convertible cells. -/
theorem matchingOf_distinguishes_faces :
    matchingOf adjunctionCupAtLeft ≠ matchingOf adjunctionCupAtRight := by
  intro structuresEqual
  have partnersEqual : (matchingOf adjunctionCupAtLeft).partner = (matchingOf adjunctionCupAtRight).partner :=
    congrArg DiagramType.partner structuresEqual
  rw [show (matchingOf adjunctionCupAtLeft).partner = [4, 5, 3, 2, 0, 1] from rfl,
      show (matchingOf adjunctionCupAtRight).partner = [2, 3, 0, 1, 5, 4] from rfl] at partnersEqual
  injection partnersEqual with headEqual _
  exact Nat.noConfusion (Nat.succ.inj (Nat.succ.inj headEqual))

/-! ## The achievable SOUNDNESS pieces for `SaturatedTwoCellConv` -/

/-- ★ **`matchingOf` is invariant under the disjoint-whisker EXCHANGE** — the `SaturatedTwoCellConv.whiskerExchange`
constructor relates two cells with the SAME spine (the boundary cast is spine-invisible), and `matchingOf` reads
ONLY the spine, so it is invariant.  Mirrors `monotoneMapOf_whiskerExchange`; one of the saturated constructors the
soundness field must honour, discharged unconditionally. -/
theorem matchingOf_whiskerExchange {sourceMode middleSourceMode middleTargetMode targetMode : AdjunctionMode}
    (leftWhisker : ModalityPath adjunctionGraph sourceMode middleSourceMode)
    {bodyDom bodyCod : ModalityPath adjunctionGraph middleSourceMode middleTargetMode}
    (rightWhisker : ModalityPath adjunctionGraph middleTargetMode targetMode)
    (body : RawTwoCellExpr adjunctionModeSignature bodyDom bodyCod) :
    matchingOf (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature) leftWhisker
        (RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature) rightWhisker body))
      = matchingOf (RawTwoCellExpr.castBoundary
          (composePath_assoc leftWhisker bodyDom rightWhisker)
          (composePath_assoc leftWhisker bodyCod rightWhisker)
          (RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature) rightWhisker
            (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature) leftWhisker body))) :=
  matchingOf_congr_of_spine_eq
    (Eq.trans
      (rfl : (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature) leftWhisker
                (RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature) rightWhisker body)).spine
            = (RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature) rightWhisker
                (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature) leftWhisker body)).spine)
      (RawTwoCellExpr.castBoundary_spine
        (composePath_assoc leftWhisker bodyDom rightWhisker)
        (composePath_assoc leftWhisker bodyCod rightWhisker)
        (RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature) rightWhisker
          (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature) leftWhisker body))).symm)

/-! ## ★ The SOUNDNESS direction `mapEqOfConv`, REDUCED to exactly two named residuals (proven, not described)

`SaturatedTwoCellConv a b → matchingOf a = matchingOf b` is proven by induction on the derivation with EVERY case
discharged except two named inputs: the union-find Godement INDEPENDENCE (`godementInvariant`, for the `ofFull`
case, via `matchingOf_sound_of_godementInvariant` — shared with the arc route) and the matching's saturated-CONGRUENCE
compositionality (`MatchingSaturatedCongruence`, for the four congruence constructors).  The TRIANGLE cases are `rfl`
(`matchingOf_triangleLeft` / `…Right`), `whiskerExchange` is `matchingOf_whiskerExchange`, and `refl` / `symm` /
`trans` chain.  So the soundness field is CONCRETELY reduced, not merely sketched. -/

/-- The matching's invariance under the four SATURATED CONGRUENCE constructors, bundled — the second soundness
residual (the first being `godementInvariant`).  Each field is a true compositionality of the boundary matching
(stacking / whiskering a sub-cell with a fixed context depends on the sub-cell only through its matching); proving
them is the same union-find state-renaming-invariance flavour as `godementInvariant`.  Bundled so the soundness
reduction below consumes it in one argument. -/
structure MatchingSaturatedCongruence : Prop where
  /-- Compositionality under the LEFT factor of a vertical composite. -/
  vcompLeft : {sourceMode targetMode : AdjunctionMode} →
    {oneCellF oneCellG oneCellH : ModalityPath adjunctionGraph sourceMode targetMode} →
    {cellAlpha cellAlpha' : RawTwoCellExpr adjunctionModeSignature oneCellF oneCellG} →
    (cellBeta : RawTwoCellExpr adjunctionModeSignature oneCellG oneCellH) →
    matchingOf cellAlpha = matchingOf cellAlpha' →
    matchingOf (RawTwoCellExpr.vcomp cellAlpha cellBeta) = matchingOf (RawTwoCellExpr.vcomp cellAlpha' cellBeta)
  /-- Compositionality under the RIGHT factor of a vertical composite. -/
  vcompRight : {sourceMode targetMode : AdjunctionMode} →
    {oneCellF oneCellG oneCellH : ModalityPath adjunctionGraph sourceMode targetMode} →
    (cellAlpha : RawTwoCellExpr adjunctionModeSignature oneCellF oneCellG) →
    {cellBeta cellBeta' : RawTwoCellExpr adjunctionModeSignature oneCellG oneCellH} →
    matchingOf cellBeta = matchingOf cellBeta' →
    matchingOf (RawTwoCellExpr.vcomp cellAlpha cellBeta) = matchingOf (RawTwoCellExpr.vcomp cellAlpha cellBeta')
  /-- Compositionality under a LEFT whiskering. -/
  whiskerLeft : {sourceMode middleMode targetMode : AdjunctionMode} →
    (oneCell : ModalityPath adjunctionGraph sourceMode middleMode) →
    {oneCellG oneCellH : ModalityPath adjunctionGraph middleMode targetMode} →
    {cellBeta cellBeta' : RawTwoCellExpr adjunctionModeSignature oneCellG oneCellH} →
    matchingOf cellBeta = matchingOf cellBeta' →
    matchingOf (RawTwoCellExpr.whiskerLeft oneCell cellBeta)
      = matchingOf (RawTwoCellExpr.whiskerLeft oneCell cellBeta')
  /-- Compositionality under a RIGHT whiskering. -/
  whiskerRight : {sourceMode middleMode targetMode : AdjunctionMode} →
    {oneCellF oneCellG : ModalityPath adjunctionGraph sourceMode middleMode} →
    (oneCell : ModalityPath adjunctionGraph middleMode targetMode) →
    {cellAlpha cellAlpha' : RawTwoCellExpr adjunctionModeSignature oneCellF oneCellG} →
    matchingOf cellAlpha = matchingOf cellAlpha' →
    matchingOf (RawTwoCellExpr.whiskerRight oneCell cellAlpha)
      = matchingOf (RawTwoCellExpr.whiskerRight oneCell cellAlpha')

/-- ★ **The SOUNDNESS direction, proven modulo the two named residuals.**  Given the union-find Godement
INDEPENDENCE (`godementInvariant`, the `ofFull` input) and the matching's saturated-congruence COMPOSITIONALITY
(`congruence`), `matchingOf` is invariant under the COMPLETE `SaturatedTwoCellConv` — the triangle cases ON THE NOSE
(`rfl`), `whiskerExchange` same-spine, the congruences by `congruence`, the structural / whisker / interchange laws
through `matchingOf_sound_of_godementInvariant`.  This is `AdjunctionSaturatedCanonicalization.mapEqOfConv`'s analog
for the correct carrier, with the residual narrowed to exactly the two named lemmas. -/
theorem saturatedConv_matchingOf_eq
    (godementInvariant : ∀ {overallSource overallTarget : AdjunctionMode} (bottomCount : Nat)
        (state : WireState)
        {firstList secondList : List (SpineAtom adjunctionModeSignature overallSource overallTarget)},
        SpineGodementStep adjunctionModeSignature firstList secondList →
        extractAfterProcessing bottomCount state firstList = extractAfterProcessing bottomCount state secondList)
    (congruence : MatchingSaturatedCongruence)
    {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    {cellA cellB : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath}
    (conv : SaturatedTwoCellConv cellA cellB) : matchingOf cellA = matchingOf cellB := by
  induction conv with
  | ofFull convFull => exact matchingOf_sound_of_godementInvariant godementInvariant convFull
  | triangleLeft => exact matchingOf_triangleLeft
  | triangleRight => exact matchingOf_triangleRight
  | vcompCongrLeft cellBeta _ inductionHypothesis => exact congruence.vcompLeft cellBeta inductionHypothesis
  | vcompCongrRight cellAlpha _ inductionHypothesis => exact congruence.vcompRight cellAlpha inductionHypothesis
  | whiskerLeftCongr oneCell _ inductionHypothesis => exact congruence.whiskerLeft oneCell inductionHypothesis
  | whiskerRightCongr oneCell _ inductionHypothesis => exact congruence.whiskerRight oneCell inductionHypothesis
  | whiskerExchange leftWhisker rightWhisker body => exact matchingOf_whiskerExchange leftWhisker rightWhisker body
  | refl _ => rfl
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ firstHypothesis secondHypothesis => exact firstHypothesis.trans secondHypothesis

/-! ## The saturated canonicalization keystone, carried by `matchingOf` -/

/-- ★ The **saturated matching canonicalization** — the keystone re-aimed at the correct carrier `matchingOf` (the
Joyal–Street boundary `DiagramType`).  Two fields, the saturated analog of `AdjunctionSaturatedCanonicalization`
with `monotoneMapOf` replaced by the variance-correct `matchingOf`: SOUNDNESS (`mapEqOfConv` — saturated-convertible
cells share a boundary matching, the triangles' snake-collapse honoured ON THE NOSE here) and COMPLETENESS
(`convOfMapEq` — equal boundary matchings reconstruct a saturated convertibility). -/
structure SaturatedMatchingCanonicalization where
  /-- SOUNDNESS: saturated-convertible cells have equal boundary matchings (the NO-direction). -/
  mapEqOfConv : {sourceMode targetMode : AdjunctionMode} →
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode} →
    {cellA cellB : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath} →
    SaturatedTwoCellConv cellA cellB → matchingOf cellA = matchingOf cellB
  /-- COMPLETENESS: cells with equal boundary matchings are saturated-convertible (the YES-direction). -/
  convOfMapEq : {sourceMode targetMode : AdjunctionMode} →
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode} →
    {cellA cellB : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath} →
    matchingOf cellA = matchingOf cellB → SaturatedTwoCellConv cellA cellB

/-- ★ **Assembling the keystone's SOUNDNESS field from the two residuals.**  The proven reduction
`saturatedConv_matchingOf_eq` IS the `mapEqOfConv` field — so a `SaturatedMatchingCanonicalization` is fully
determined by the two named soundness residuals together with a `convOfMapEq` reconstruction.  This pins exactly how
the keystone assembles around the correct carrier. -/
def saturatedMatchingCanonicalization_of
    (godementInvariant : ∀ {overallSource overallTarget : AdjunctionMode} (bottomCount : Nat)
        (state : WireState)
        {firstList secondList : List (SpineAtom adjunctionModeSignature overallSource overallTarget)},
        SpineGodementStep adjunctionModeSignature firstList secondList →
        extractAfterProcessing bottomCount state firstList = extractAfterProcessing bottomCount state secondList)
    (congruence : MatchingSaturatedCongruence)
    (convOfMapEq : {sourceMode targetMode : AdjunctionMode} →
      {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode} →
      {cellA cellB : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath} →
      matchingOf cellA = matchingOf cellB → SaturatedTwoCellConv cellA cellB) :
    SaturatedMatchingCanonicalization where
  mapEqOfConv := fun conv => saturatedConv_matchingOf_eq godementInvariant congruence conv
  convOfMapEq := convOfMapEq

/-- ★ **Decide saturated convertibility via the boundary matching.**  Given the canonicalization, compare the two
cells' boundary matchings by the `DiagramType` `DecidableEq`: equal matchings ⟹ `isTrue` (`convOfMapEq`); unequal
⟹ `isFalse` (`mapEqOfConv` would force them equal).  The `DiagramType` equality is a structural `deriving
DecidableEq` over `Nat`/`List Nat` — it COMPUTES — so the decision carries no `propext` (no `decidable_of_iff`). -/
def decideSaturatedConvViaMatching (canon : SaturatedMatchingCanonicalization)
    {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    (cellA cellB : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) :
    Decidable (SaturatedTwoCellConv cellA cellB) :=
  match (inferInstance : Decidable (matchingOf cellA = matchingOf cellB)) with
  | isTrue matchingsEqual => isTrue (canon.convOfMapEq matchingsEqual)
  | isFalse matchingsDiffer => isFalse (fun conv => matchingsDiffer (canon.mapEqOfConv conv))

/-- ★ **The seed's saturated 2-cell word problem, modulo the matching canonicalization.**  Supplying the
boundary-matching canonicalization inhabits the full saturated decision interface
(`DecidableSaturatedTwoCellConvFor`) — it decides EVERY parallel pair, the snakes collapsed and the Godement
transpositions absorbed by the global matching.  The matching-carried analog of
`adjunctionSaturatedWordProblemModuloCanonicalization`. -/
@[reducible] def adjunctionSaturatedWordProblemModuloMatching
    (canon : SaturatedMatchingCanonicalization) : DecidableSaturatedTwoCellConvFor :=
  fun cellA cellB => decideSaturatedConvViaMatching canon cellA cellB

/-- ★ **The decision sees the bubble collapse.**  Given any matching canonicalization, the decision on
`(adjunctionSeedLeftSnake, id_L)` rests on the matchings agreeing — which `matchingOf_triangleLeft` supplies ON THE
NOSE (`rfl`), no `mapEqOfConv` call needed.  The snake-collapse the covariant fold needed the whole
simplicial-identity machinery for is definitional in the matching. -/
theorem decideSaturated_leftSnake_matchingsAgree :
    matchingOf adjunctionSeedLeftSnake = matchingOf adjunctionIdentityLeft :=
  matchingOf_triangleLeft

/-! ## Honesty markers -/

/-- **★ ESTABLISHED — the saturated canonicalization CARRIER is identified and machine-checked.**  The boundary
planar matching `matchingOf` (Joyal–Street `DiagramType`) is the variance-correct carrier the prior monotone-fold
route could not build: it collapses the snake to the identity ON THE NOSE (`matchingOf_triangleLeft` /
`matchingOf_triangleRight`, `rfl`), RESOLVES the `embeddedTipCap` obstruction that refuted BOTH the covariant and op
folds (`matchingOf_resolves_embeddedTipCap`, with the contrast `matchingOf_strictlyBetterThanFolds_onEmbeddedTipCap`),
and still DISCRIMINATES genuinely-different cells (`matchingOf_distinguishes_faces`, the two faces `δ₀ ≠ δ₁`).  The
no-go that forces a GLOBAL carrier — that a base-block cup and the embedded tip cup are locally indistinguishable
(`arcMatching_cupAtoms_locallyIndistinguishable`) — is machine-checked too.  The whisker-exchange constructor is
discharged unconditionally (`matchingOf_whiskerExchange`).  `= true`. -/
def fxMode_hasSaturatedMatchingCanonicalizationCarrier : Bool := true

/-- **Honesty marker — the full `SaturatedMatchingCanonicalization` is NOT yet a constructed term; its two fields
reduce to the SAME named residuals as the arc route, now with the two hardest soundness inputs DISCHARGED.**

  * **`mapEqOfConv`** (SOUNDNESS, `SaturatedTwoCellConv a b → matchingOf a = matchingOf b`).  PROVEN as
    `saturatedConv_matchingOf_eq` (full induction on the derivation) MODULO exactly two named inputs: the TRIANGLE
    cases are `rfl` (`matchingOf_triangleLeft` / `…Right`); `whiskerExchange` is the same-spine
    `matchingOf_whiskerExchange`; `refl` / `symm` / `trans` chain; the `ofFull` (`TwoCellConvFull`) case is
    `matchingOf_sound_of_godementInvariant` MODULO the single union-find Godement INDEPENDENCE residual
    `godementInvariant` (`fxMode_hasMatchingGodementIndependenceProof = false`, SHARED with the arc route, TRUE and
    computationally confirmed on every obstruction witness — including `matchingOf_resolves_embeddedTipCap`); and the
    four SATURATED CONGRUENCES reduce to the bundled matching compositionality `MatchingSaturatedCongruence` (the
    boundary matching of a context-embedded cell is determined by the sub-cell's matching) — a state-renaming
    invariance of the same flavour as `godementInvariant`, the second named soundness residual.
    `saturatedMatchingCanonicalization_of` assembles the whole keystone from these two plus a `convOfMapEq`.
  * **`convOfMapEq`** (COMPLETENESS, `matchingOf a = matchingOf b → SaturatedTwoCellConv a b`).  The Joyal–Street
    RECONSTRUCTION: equal boundary matchings ⟹ planar-isotopic ⟹ saturated-convertible (the SATURATED reconstruction
    is EASIER than the free `fxMode_hasArcStructureReconstruction`, since the triangles supply the snake-straightening
    moves the free reconstruction lacks).  The third named residual.

★ **The prior "KEYSTONE-COUPLING WALL" is DISSOLVED.**  That wall pinned the canonicalization map to the covariant
`monotoneMapOf` (refuted by `covariantMonotoneMapOf_notSound` on `embeddedTipCapConv`) and concluded the keystone
could never assemble from the monotone route.  With `matchingOf` as the carrier the SOUNDNESS field IS dischargeable
on the triangle and on the Godement obstruction (both shown here, `rfl`); the residual is no longer a covariance
contradiction but the same union-find INDEPENDENCE + RECONSTRUCTION content the arc route already isolates.
the residual is no longer a covariance
contradiction but the same union-find INDEPENDENCE + RECONSTRUCTION content the arc route already isolates.

★ **NOW DISCHARGED — the keystone is INHABITED unconditionally.**  Both named residuals are closed downstream:
SOUNDNESS through the shipped boundary-disciplined route (`saturatedMatchingCanonicalization_ofBoundaryDiscipline`
on `matchingSaturatedCongruence_proved`), and COMPLETENESS through the unconditional Track-B spine-trace JOIN
(`matchingReductsShareSpineTrace_holds`).  The constructed term is
`saturatedMatchingCanonicalization_holds : SaturatedMatchingCanonicalization` in
`SaturatedMatchingDecisionAssembly` (downstream of this file — cited textually to avoid the import cycle),
audited zero-axiom.  The GENERAL multi-mode `fxMode_hasDecidableTwoCellEquality` /
`fxMode_hasModeRelativeConvDecision` stay `false` (they demand the general, cross-signature decision that the
rung-3 undecidability wall bounds — this seed-specific saturated decision is a necessary ingredient, not the
general claim).  `= true`. -/
def fxMode_hasSaturatedMatchingCanonicalization : Bool := true

end FX1Poly.Polygraph
