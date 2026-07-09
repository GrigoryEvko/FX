import FX1Poly.Polygraph.TwoCategory.Amalgam.DeciderReseat

/-! # Polygraph/TwoCategory/Amalgam/PushoutMonotoneReflection — the signature-generic arity fold, the cross-component
separation it COMPUTES, and the pushout non-convertibility reflection reduced to one bundle (WP-AMALG r7)

`DeciderReseat.lean` (r6 P4) shipped the genuinely interleaving pair `crossPairAlpha` / `crossPairBeta`
(`s·t ⇒ s·(t·t)`, the two monad faces `δ₁` / `δ₀` whiskered by the component-1 letter `s`), and SEPARATED their
monad blocks through the shipped bespoke walking-monad decision (`monadDecision_no_faces`: `[1] ≠ [0]`).  What it
could NOT ship was a LIVE combined `isFalse` over the pushout itself — because the bespoke decision lives on
`monadModeSignature`, not the pushout's reconstructed signature (the P3 reconstruction JAM), and because the
reflecting direction (a common `s`-whisker of non-convertible monad blocks stays non-convertible) is the
Nelson-Oppen / Baader-Tinelli purification completeness `DispatchSaturated.lean` flags as the wire-creating
residual.

This file settles the reflection by ROUTE (b) — the signature-generic arity fold as the carrier — up to a single
precisely-named bundle, and pins the exact residual.

## The reflection carrier: the signature-generic arity fold

The walking-monad Δ fold `monadMonotoneMapOf` (`WalkingMonad/MonadDeltaModel`) reads the spine ONLY through
`atom.leftContext.length`, `atom.generatorDom.length`, `atom.generatorCod.length` — never the generator PAYLOAD
type.  So its body is signature-generic verbatim: `arityMonotoneMapOf` is the identical fold over ANY
`ModeSignature`, and over `monadModeSignature` it IS `monadMonotoneMapOf` (`arityMonotoneMapOf_eq_monadMonotoneMapOf`,
`rfl`).  On the pushout `involution +_M monad` it reads through the `s`-prefix: `crossPairAlpha` folds to `[0, 2]`
and `crossPairBeta` to `[0, 1]` (each `rfl`), which DIFFER by `decide` — the non-vacuous discriminating content.
This is the free-product / Δ₊ word-problem fact (Nyberg-Brodda; Street "formal theory of monads"; Mac Lane §VII.5):
equality in the amalgam reflects blockwise equality in the monad factor, read off the ordinal fold.

## The reflection reduced to ONE bundle

The reflection object is `SaturatedConvOver pushout (SaturatedConvOverPushout … emptyCellRel emptyCellRel) …`,
the SAME base relation as r6's isTrue counterpart `crossPairConvertibleCounterpart` (real coprojection
`inclusionRightTwoReal`, empty component relations).  Its universal property `SaturatedConvOver.recInto` reduces
`arityMonotoneMapOf`-invariance to an `IsSaturatedCongruence`, whose free fields ship UNCONDITIONALLY: `ofRelation`
is `False.elim` (both component relations empty), `refl`/`symm`/`trans` are `Eq`, and the whole `ofFull` leg is
reduced generically (`arityMonotoneMapOf_eqOfConvFull`) to just `ArityFoldConvSound` — the interchange (Godement)
soundness plus the four fold congruence homomorphisms.  The eleven structural laws and the five whisker-
functoriality laws are spine-invariant (`arityMonotoneMapOf_eq_of_interchangeFreeStep` / `castBoundary_spine`), so
they cost nothing.  Hence:

  `crossPairPushoutNonConv : ArityFoldConvSound pushout → ¬ SaturatedConvOver pushout … crossPairAlpha crossPairBeta`.

## The residual, pinned (`= false`, the r8 target)

`ArityFoldConvSound involutionMonadPushout.toModeSignature` is the ONLY remaining brick.  It is the re-homing of
the walking-monad Δ-fold soundness (`monadMonotoneMapOf_interchange` + the four `monadMonotoneMapOf_*Congr`) onto
the pushout signature.  That re-homing needs the fold's ORDINAL-EMBEDDING discipline (`monadRunMonoCell_localEmbed`),
which holds only because every 2-generator has arity `(0,1)` or `(2,1)` — a fact the monad proofs establish by
`cases generator` on `MonadTwoCell`, and which for the pushout must be re-established by casing on the RECONSTRUCTED
generators (index `0` = `eta` arity `(0,1)`, index `1` = `mu` arity `(2,1)`).  The interchange field is the genuine
simplicial brick (the disjoint-window two-block commute, cap-free on Δ); the four congruence fields are fold
functoriality.  So `fxAmalg_hasLiveMonadPushoutIsFalse` (`DeciderReseat.lean`) stays `false`; the reflection is
GREEN modulo this one bundle, and the bundle is the concrete r8 target.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The signature-generic arity fold (the payload-blind generalization of the walking-monad Δ fold) -/

/-- One fold step, signature-GENERIC: read only the atom's arity `(generatorDom.length, generatorCod.length)` and
its whisker position `leftContext.length` — never the generator payload type.  Arity `(0,1)` (a unit-shaped
generator) post-composes a face `δ_p` and grows the width; arity `(2,1)` (a multiplication-shaped generator)
post-composes a degeneracy `σ_p` and shrinks it; any other arity leaves the state unchanged.  The verbatim
signature-generalization of `monadMonoStepAtom` (`WalkingMonad/MonadDeltaModel`), whose body already reads only
these three lengths. -/
def arityFoldStepAtom {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (state : Nat × List Nat) (atom : SpineAtom signature sourceMode targetMode) : Nat × List Nat :=
  let position := atom.leftContext.length
  match atom.generatorDom.length, atom.generatorCod.length with
  | 0, 1 => (state.1 + 1, composeMap state.2 (faceMap position state.1))
  | 2, 1 => (state.1 - 1, composeMap state.2 (degenMap position (state.1 - 1)))
  | _, _ => state

/-- ★ The **signature-generic arity monotone-map fold** of a free 2-cell — fold the arity/position spine into the
composite face / degeneracy map, starting from the identity on the source path LENGTH.  The identical body as
`monadMonotoneMapOf`, hoisted to an arbitrary `ModeSignature`.  Structural fold — it COMPUTES. -/
def arityMonotoneMapOf {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (cell : RawTwoCellExpr signature sourcePath targetPath) : List Nat :=
  (cell.spine.foldl arityFoldStepAtom (sourcePath.length, idMap sourcePath.length)).2

/-- ★ **The arity fold is a FAITHFUL generalization** — over the bespoke `monadModeSignature` it is DEFINITIONALLY
the walking-monad Δ fold `monadMonotoneMapOf` (`rfl`, since both bodies read the spine through the same three
lengths).  So the pushout reflection is literally the walking-monad word problem, signature-generalized. -/
theorem arityMonotoneMapOf_eq_monadMonotoneMapOf {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
    (cell : RawTwoCellExpr monadModeSignature sourcePath targetPath) :
    arityMonotoneMapOf cell = monadMonotoneMapOf cell := rfl

/-! ## The structural-fragment invariance (generic, UNCONDITIONAL) -/

/-- The arity fold depends on the cell only through its spine (the source length is fixed by the boundary): equal
spines give equal maps. -/
theorem arityMonotoneMapOf_congr_of_spine_eq {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {cellOne cellTwo : RawTwoCellExpr signature sourcePath targetPath}
    (spineEqual : cellOne.spine = cellTwo.spine) : arityMonotoneMapOf cellOne = arityMonotoneMapOf cellTwo := by
  show (cellOne.spine.foldl arityFoldStepAtom (sourcePath.length, idMap sourcePath.length)).2
    = (cellTwo.spine.foldl arityFoldStepAtom (sourcePath.length, idMap sourcePath.length)).2
  rw [spineEqual]

/-- ★ **The arity fold is invariant under the eleven structural strict-2-category laws** — each preserves the spine
on the nose (`TwoCellStepInterchangeFree.spine_eq`), so the fold is preserved.  The interchange-free leg, generic
and unconditional. -/
theorem arityMonotoneMapOf_eq_of_interchangeFreeStep {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {cellOne cellTwo : RawTwoCellExpr signature sourcePath targetPath}
    (step : TwoCellStepInterchangeFree signature cellOne cellTwo) :
    arityMonotoneMapOf cellOne = arityMonotoneMapOf cellTwo :=
  arityMonotoneMapOf_congr_of_spine_eq step.spine_eq

/-! ## The convertibility-soundness bundle: the interchange brick + the four fold congruence homomorphisms

`ArityFoldConvSound signature` is EXACTLY the arity-discipline consequences of the fold: the Godement/interchange
soundness (the disjoint-window commute) and the four congruence homomorphisms.  Everything else in
`TwoCellConvFull`-invariance is spine-invariant (structural laws + whisker functoriality) or trivial (refl/symm/
trans), so this bundle is the WHOLE non-trivial content, generically. -/

/-- ★ **The arity-fold convertibility-soundness bundle** — the interchange (Godement) soundness plus the four fold
congruence homomorphisms.  Over `monadModeSignature` this is inhabited by the shipped `monadMonotoneMapOf_interchange`
and the four `monadMonotoneMapOf_*Congr`; over the pushout it is the r8 target (the same lemmas re-homed with the
reconstructed generators' arity discipline).  Given it, the fold is invariant under the whole completed
convertibility. -/
structure ArityFoldConvSound (signature : ModeSignature) : Prop where
  /-- The Godement / interchange soundness — the two orders of the exchange redex fold to the same map (the
  disjoint-window two-block commute, cap-free on Δ; the genuine simplicial brick). -/
  interchange : {sourceMode middleMode targetMode : signature.graph.Mode} →
    {fLow fMid fHigh : ModalityPath signature.graph sourceMode middleMode} →
    {gLow gMid gHigh : ModalityPath signature.graph middleMode targetMode} →
    (cellAlpha : RawTwoCellExpr signature fLow fMid) →
    (cellAlphaUpper : RawTwoCellExpr signature fMid fHigh) →
    (cellBeta : RawTwoCellExpr signature gLow gMid) →
    (cellBetaUpper : RawTwoCellExpr signature gMid gHigh) →
    arityMonotoneMapOf (RawTwoCellExpr.hcomp (RawTwoCellExpr.vcomp cellAlpha cellAlphaUpper)
        (RawTwoCellExpr.vcomp cellBeta cellBetaUpper))
      = arityMonotoneMapOf (RawTwoCellExpr.vcomp (RawTwoCellExpr.hcomp cellAlpha cellBeta)
          (RawTwoCellExpr.hcomp cellAlphaUpper cellBetaUpper))
  /-- Left-vcomp congruence: maps agreeing on the left factor give equal composite maps. -/
  vcompCongrLeft : {sourceMode targetMode : signature.graph.Mode} →
    {oneCellF oneCellG oneCellH : ModalityPath signature.graph sourceMode targetMode} →
    {cellAlpha cellAlpha' : RawTwoCellExpr signature oneCellF oneCellG} →
    (cellBeta : RawTwoCellExpr signature oneCellG oneCellH) →
    arityMonotoneMapOf cellAlpha = arityMonotoneMapOf cellAlpha' →
    arityMonotoneMapOf (RawTwoCellExpr.vcomp cellAlpha cellBeta)
      = arityMonotoneMapOf (RawTwoCellExpr.vcomp cellAlpha' cellBeta)
  /-- Right-vcomp congruence: maps agreeing on the right factor give equal composite maps. -/
  vcompCongrRight : {sourceMode targetMode : signature.graph.Mode} →
    {oneCellF oneCellG oneCellH : ModalityPath signature.graph sourceMode targetMode} →
    (cellAlpha : RawTwoCellExpr signature oneCellF oneCellG) →
    {cellBeta cellBeta' : RawTwoCellExpr signature oneCellG oneCellH} →
    arityMonotoneMapOf cellBeta = arityMonotoneMapOf cellBeta' →
    arityMonotoneMapOf (RawTwoCellExpr.vcomp cellAlpha cellBeta)
      = arityMonotoneMapOf (RawTwoCellExpr.vcomp cellAlpha cellBeta')
  /-- Left-whisker congruence: whiskering map-equal bodies on the left gives equal maps. -/
  whiskerLeftCongr : {sourceMode middleMode targetMode : signature.graph.Mode} →
    (oneCell : ModalityPath signature.graph sourceMode middleMode) →
    {oneCellG oneCellH : ModalityPath signature.graph middleMode targetMode} →
    {cellBeta cellBeta' : RawTwoCellExpr signature oneCellG oneCellH} →
    arityMonotoneMapOf cellBeta = arityMonotoneMapOf cellBeta' →
    arityMonotoneMapOf (RawTwoCellExpr.whiskerLeft oneCell cellBeta)
      = arityMonotoneMapOf (RawTwoCellExpr.whiskerLeft oneCell cellBeta')
  /-- Right-whisker congruence: whiskering map-equal bodies on the right gives equal maps.  Binder order (the
  whiskered 1-cells before `oneCell`) mirrors `monadMonotoneMapOf_whiskerRightCongr` so the monad cross-check
  inhabits it by bare assignment. -/
  whiskerRightCongr : {sourceMode middleMode targetMode : signature.graph.Mode} →
    {oneCellF oneCellG : ModalityPath signature.graph sourceMode middleMode} →
    (oneCell : ModalityPath signature.graph middleMode targetMode) →
    {cellAlpha cellAlpha' : RawTwoCellExpr signature oneCellF oneCellG} →
    arityMonotoneMapOf cellAlpha = arityMonotoneMapOf cellAlpha' →
    arityMonotoneMapOf (RawTwoCellExpr.whiskerRight oneCell cellAlpha)
      = arityMonotoneMapOf (RawTwoCellExpr.whiskerRight oneCell cellAlpha')

/-- The arity fold is invariant under the base 3-cell rewrite `TwoCellStep` (Godement `interchange` INCLUDED),
GIVEN the soundness bundle: the eleven structural laws are spine-invariant, the four congruences use the bundle's
homomorphisms, and `interchange` is the bundle's interchange field. -/
theorem arityMonotoneMapOf_eqOfStep {signature : ModeSignature} (sound : ArityFoldConvSound signature)
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {cellA cellB : RawTwoCellExpr signature sourcePath targetPath}
    (step : TwoCellStep signature cellA cellB) :
    arityMonotoneMapOf cellA = arityMonotoneMapOf cellB := by
  induction step with
  | vcompIdLeft _ => exact arityMonotoneMapOf_congr_of_spine_eq rfl
  | vcompIdRight _ => exact arityMonotoneMapOf_congr_of_spine_eq rfl
  | vcompAssoc _ _ _ => exact arityMonotoneMapOf_congr_of_spine_eq rfl
  | whiskerLeftId _ _ => exact arityMonotoneMapOf_congr_of_spine_eq rfl
  | whiskerRightId _ _ => exact arityMonotoneMapOf_congr_of_spine_eq rfl
  | whiskerLeftVcomp _ _ _ => exact arityMonotoneMapOf_congr_of_spine_eq rfl
  | whiskerRightVcomp _ _ _ => exact arityMonotoneMapOf_congr_of_spine_eq rfl
  | vcompCongrLeft cellBeta _ ih => exact sound.vcompCongrLeft cellBeta ih
  | vcompCongrRight cellAlpha _ ih => exact sound.vcompCongrRight cellAlpha ih
  | whiskerLeftCongr oneCell _ ih => exact sound.whiskerLeftCongr oneCell ih
  | whiskerRightCongr oneCell _ ih => exact sound.whiskerRightCongr oneCell ih
  | interchange cellAlpha cellAlphaUpper cellBeta cellBetaUpper =>
      exact sound.interchange cellAlpha cellAlphaUpper cellBeta cellBetaUpper

/-- The arity fold is invariant under the free convertibility `TwoCellConv`, given the bundle. -/
theorem arityMonotoneMapOf_eqOfConv {signature : ModeSignature} (sound : ArityFoldConvSound signature)
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {cellA cellB : RawTwoCellExpr signature sourcePath targetPath}
    (conv : TwoCellConv signature cellA cellB) :
    arityMonotoneMapOf cellA = arityMonotoneMapOf cellB := by
  induction conv with
  | ofStep step => exact arityMonotoneMapOf_eqOfStep sound step
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- ★ **The arity fold is invariant under the COMPLETED convertibility `TwoCellConvFull`, given the bundle.**
`ofConv` via `arityMonotoneMapOf_eqOfConv`; the five whisker-functoriality laws relate SAME-SPINE cells
(`castBoundary` is spine-invisible; the whisker shifts are `composePath` identities), discharged by
`arityMonotoneMapOf_congr_of_spine_eq`; the four congruences by the bundle; refl/symm/trans trivially.  This is the
`ofFull` leg of the reflection, reduced to `ArityFoldConvSound`. -/
theorem arityMonotoneMapOf_eqOfConvFull {signature : ModeSignature} (sound : ArityFoldConvSound signature)
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {cellA cellB : RawTwoCellExpr signature sourcePath targetPath}
    (convFull : TwoCellConvFull signature cellA cellB) :
    arityMonotoneMapOf cellA = arityMonotoneMapOf cellB := by
  induction convFull with
  | ofConv conv => exact arityMonotoneMapOf_eqOfConv sound conv
  | whiskerLeftUnit _ => exact arityMonotoneMapOf_congr_of_spine_eq rfl
  | whiskerRightUnit _ =>
      exact arityMonotoneMapOf_congr_of_spine_eq (by rw [RawTwoCellExpr.castBoundary_spine]; rfl)
  | whiskerLeftComp _ _ _ =>
      exact arityMonotoneMapOf_congr_of_spine_eq (by rw [RawTwoCellExpr.castBoundary_spine]; rfl)
  | whiskerRightComp _ _ _ =>
      refine arityMonotoneMapOf_congr_of_spine_eq ?_
      rw [RawTwoCellExpr.castBoundary_spine]
      dsimp only [RawTwoCellExpr.spine, RawTwoCellExpr.spineDiff]
      rw [composePath_assoc]
  | whiskerExchange _ _ _ =>
      exact arityMonotoneMapOf_congr_of_spine_eq (by rw [RawTwoCellExpr.castBoundary_spine]; rfl)
  | vcompCongrLeft cellBeta _ ih => exact sound.vcompCongrLeft cellBeta ih
  | vcompCongrRight cellAlpha _ ih => exact sound.vcompCongrRight cellAlpha ih
  | whiskerLeftCongr oneCell _ ih => exact sound.whiskerLeftCongr oneCell ih
  | whiskerRightCongr oneCell _ ih => exact sound.whiskerRightCongr oneCell ih
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-! ## The pushout reflection: the arity-fold-equality relation is a `SaturatedConvOver`-congruence -/

/-- The base relation of the reflection — the r6 real-coprojection pushout with EMPTY component relations, the SAME
relation `crossPairConvertibleCounterpart` decides isTrue over.  Empty component relations make it the empty
relation on cells, so its rows are unfireable. -/
abbrev crossPairPushoutRel : CellRel involutionMonadPushout.toModeSignature :=
  SaturatedConvOverPushout involutionComputad monadComputad involutionMonadSameModes
    (inclusionLeftTwo involutionComputad monadComputad involutionMonadSameModes rfl)
    (inclusionRightTwoReal involutionComputad monadComputad involutionMonadSameModes)
    (emptyCellRel involutionComputad.toModeSignature)
    (emptyCellRel monadComputad.toModeSignature)

/-- The arity-fold-equality relation on the pushout's free 2-cells — the target congruence of the reflection. -/
abbrev arityFoldEqRel : CellRel involutionMonadPushout.toModeSignature :=
  fun cellAlpha cellBeta => arityMonotoneMapOf cellAlpha = arityMonotoneMapOf cellBeta

/-- Both rows of the empty-component-relation pushout relation are unfireable: `left` / `right` each carry an
`emptyCellRel` (`= False`) hypothesis.  So the `ofRelation` leg of the reflection is `False.elim` — UNCONDITIONAL. -/
theorem arityFoldEqRel_of_emptyPushoutRow
    {sourceMode targetMode : involutionMonadPushout.toModeSignature.graph.Mode}
    {sourcePath targetPath : ModalityPath involutionMonadPushout.toModeSignature.graph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr involutionMonadPushout.toModeSignature sourcePath targetPath}
    (row : crossPairPushoutRel cellAlpha cellBeta) : arityFoldEqRel cellAlpha cellBeta := by
  cases row with
  | left h => exact h.elim
  | right h => exact h.elim

/-- ★ **The arity-fold-equality relation absorbs the pushout saturated congruence, given the bundle.**  `ofFull`
via `arityMonotoneMapOf_eqOfConvFull sound`; `ofRelation` via `arityFoldEqRel_of_emptyPushoutRow` (`False.elim`);
the four congruences via the bundle's homomorphisms; `refl`/`symm`/`trans` are `Eq`.  Packaged for
`SaturatedConvOver.recInto`. -/
def arityFoldPushoutCongruence (sound : ArityFoldConvSound involutionMonadPushout.toModeSignature) :
    IsSaturatedCongruence involutionMonadPushout.toModeSignature crossPairPushoutRel arityFoldEqRel where
  ofFull full := arityMonotoneMapOf_eqOfConvFull sound full
  ofRelation row := arityFoldEqRel_of_emptyPushoutRow row
  vcompCongrLeft {_ _ _ _ _ _ _ cellBeta} ih := sound.vcompCongrLeft cellBeta ih
  vcompCongrRight {_ _ _ _ _ cellAlpha _ _} ih := sound.vcompCongrRight cellAlpha ih
  whiskerLeftCongr {_ _ _ oneCell _ _ _ _} ih := sound.whiskerLeftCongr oneCell ih
  whiskerRightCongr {_ _ _ _ _ oneCell _ _} ih := sound.whiskerRightCongr oneCell ih
  refl _ := rfl
  symm ih := ih.symm
  trans ihLeft ihRight := ihLeft.trans ihRight

/-! ## The concrete separation the fold COMPUTES + the conditional live isFalse -/

/-- ★ **The δ₁ face whiskered by `s` folds to `[0, 2]`** (`rfl`) — the arity fold reads the `eta` atom at position
`1` (after the `s`) over the width-`2` source `s·t`, so the composite face is `[0, 2]`. -/
theorem crossPairAlpha_arityMap : arityMonotoneMapOf crossPairAlpha = [0, 2] := rfl

/-- ★ **The δ₀ face whiskered by `s` folds to `[0, 1]`** (`rfl`) — the `eta` atom sits at position `2` (after
`s·t`), so the composite face is `[0, 1]`.  The bespoke fold gives `[1]` / `[0]`; the `s`-prefix shifts both. -/
theorem crossPairBeta_arityMap : arityMonotoneMapOf crossPairBeta = [0, 1] := rfl

/-- ★ **The arity fold SEPARATES the interleaving pair** — `[0, 2] ≠ [0, 1]` by `decide`.  The non-vacuous,
UNCONDITIONAL discriminating content: the payload-blind arity fold, read over the `s`-prefixed pushout words,
already distinguishes the two monad faces `δ₁` / `δ₀`.  This is the free-product / Δ₊ reflection made concrete. -/
theorem crossPair_arityMapsDiffer : arityMonotoneMapOf crossPairAlpha ≠ arityMonotoneMapOf crossPairBeta := by
  decide

/-- ★★ **The LIVE combined non-convertibility, reduced to the one bundle.**  Given `ArityFoldConvSound` for the
pushout, `crossPairAlpha` is NOT saturated-pushout-convertible to `crossPairBeta`: the fold would force their maps
equal (`SaturatedConvOver.recInto` through `arityFoldPushoutCongruence`), contradicting `crossPair_arityMapsDiffer`
(`[0, 2] ≠ [0, 1]`).  This is the reflection: pushout non-convertibility read off the ordinal fold — GREEN modulo
the single named bundle, whose pushout instance is the r8 target.  Pairs with r6's isTrue
`crossPairConvertibleCounterpart` (disjoint-component whiskers commute) as the discriminating pair. -/
theorem crossPairPushoutNonConv (sound : ArityFoldConvSound involutionMonadPushout.toModeSignature) :
    ¬ SaturatedConvOver involutionMonadPushout.toModeSignature crossPairPushoutRel
        crossPairAlpha crossPairBeta :=
  fun conv => crossPair_arityMapsDiffer (SaturatedConvOver.recInto (arityFoldPushoutCongruence sound) conv)

/-! ## The bundle is INHABITED: the walking-monad cross-check (UNCONDITIONAL)

The bundle `ArityFoldConvSound` is not a shape in a vacuum — over the BESPOKE `monadModeSignature` it is inhabited
by the shipped walking-monad Δ-fold soundness (`WalkingMonad/MonadDeltaDecision` + `MonadMapFactorization` +
`MonadWhiskerEmbedding`), verbatim, because `arityMonotoneMapOf = monadMonotoneMapOf` there.  So the reflection
route works END-TO-END and unconditionally on the monad — reproducing `monadDecision_no_faces` through the generic
fold machinery.  Only the pushout signature's bundle stays open (the reconstruction arity discipline). -/

/-- ★ **The convertibility-soundness bundle is INHABITED for the walking monad** — its five fields are the shipped
Δ-fold soundness lemmas (interchange = the disjoint-window commute; the four congruences = fold functoriality),
inhabiting `ArityFoldConvSound monadModeSignature` since `arityMonotoneMapOf = monadMonotoneMapOf` (`rfl`).  This
witnesses that the bundle is realizable — the pushout gap is precisely the RECONSTRUCTION arity discipline, not the
interface. -/
def monadArityFoldConvSound : ArityFoldConvSound monadModeSignature where
  interchange := monadMonotoneMapOf_interchange
  vcompCongrLeft := monadMonotoneMapOf_vcompCongrLeft
  vcompCongrRight := monadMonotoneMapOf_vcompCongrRight
  whiskerLeftCongr := monadMonotoneMapOf_whiskerLeftCongr
  whiskerRightCongr := monadMonotoneMapOf_whiskerRightCongr

/-- The two bespoke monad faces `t ⇒ t·t` fold to DIFFERENT arity maps (`[1] ≠ [0]`) by `decide` — the generic
fold reproducing the bespoke `monadDecision_no_faces` separation. -/
theorem monadFaces_arityMapsDiffer :
    arityMonotoneMapOf (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT monadUnitTwoCell)
      ≠ arityMonotoneMapOf (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT monadUnitTwoCell) := by
  decide

/-- ★★ **UNCONDITIONAL non-convertibility of the two monad faces, through the generic reflection.**  The bespoke
faces `whiskerRight t eta` (`δ₁`) and `whiskerLeft t eta` (`δ₀`) are NOT `TwoCellConvFull`-convertible: the arity
fold, invariant under the completed convertibility via the INHABITED bundle (`monadArityFoldConvSound`), would force
their maps equal, contradicting `monadFaces_arityMapsDiffer`.  This is `monadDecision_no_faces` re-derived through
the generic `arityMonotoneMapOf` machinery — the reflection route, closed end-to-end where the bundle is inhabited. -/
theorem monadFaces_notFullConv :
    ¬ TwoCellConvFull monadModeSignature
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT monadUnitTwoCell)
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT monadUnitTwoCell) :=
  fun conv => monadFaces_arityMapsDiffer (arityMonotoneMapOf_eqOfConvFull monadArityFoldConvSound conv)

/-! ## Observability -/

-- The δ₁ face (whiskered by s) folds to `[0, 2]`.
#eval arityMonotoneMapOf crossPairAlpha
-- The δ₀ face (whiskered by s) folds to `[0, 1]`.
#eval arityMonotoneMapOf crossPairBeta
-- They differ: the arity fold separates the pair. Expect `true`.
#eval decide (arityMonotoneMapOf crossPairAlpha ≠ arityMonotoneMapOf crossPairBeta)

/-! ## Honesty markers -/

/-- ★ **Honesty marker — the signature-generic arity fold + the reflection reduced to one bundle SHIP (r7).**  The
payload-blind arity fold `arityMonotoneMapOf` (a faithful generalization of the walking-monad Δ fold —
`arityMonotoneMapOf_eq_monadMonotoneMapOf`, `rfl`), its unconditional structural-fragment invariance
(`arityMonotoneMapOf_eq_of_interchangeFreeStep`), the generic reduction of `TwoCellConvFull`-invariance to the
soundness bundle `ArityFoldConvSound` (`arityMonotoneMapOf_eqOfConvFull` — the eleven structural + five
whisker-functoriality laws are spine-invariant, so free), the pushout congruence
(`arityFoldPushoutCongruence`, with `ofRelation` = `False.elim` on the empty component relations, `refl`/`symm`/
`trans` = `Eq`), and the concrete separation the fold COMPUTES (`crossPairAlpha` → `[0, 2]`, `crossPairBeta` →
`[0, 1]`, differing by `decide`) assembling into the CONDITIONAL live isFalse
`crossPairPushoutNonConv : ArityFoldConvSound pushout → ¬ SaturatedConvOver … crossPairAlpha crossPairBeta`.  The
non-vacuous discriminating pair: this isFalse (conditional) against r6's UNCONDITIONAL isTrue
`crossPairConvertibleCounterpart`.  The bundle is INHABITED (`monadArityFoldConvSound`, the shipped monad Δ-fold
soundness), so the route closes UNCONDITIONALLY on the monad (`monadFaces_notFullConv` re-derives
`monadDecision_no_faces` through the generic fold) — the pushout gap is precisely the reconstruction arity
discipline, not the interface.  Literature: free-product / Δ₊ word problem (Nyberg-Brodda; Street; Mac Lane
§VII.5); Nelson-Oppen soundness (the projecting direction needs no convexity).  `= true`. -/
def fxAmalg_hasArityFoldReflection : Bool := true

/-- ★ **Honesty marker — the reflection's residual `ArityFoldConvSound` for the pushout is DISCHARGED (r8).**
`crossPairPushoutNonConv` was green modulo `ArityFoldConvSound involutionMonadPushout.toModeSignature` — the
Godement/interchange soundness plus the four fold congruence homomorphisms.  `Amalgam/PushoutBundle.lean` now
inhabits it (`pushoutArityFoldConvSound`) by re-homing the walking-monad Δ-fold soundness generic-over-a-face/degen
arity DISCIPLINE (`arityFoldConvSound_ofDiscipline`) and proving the pushout satisfies that discipline
(`pushoutHasFaceDegenArity`): the reconstruction arity fact — every 2-generator has arity `(0,1)` or `(2,1)` — is
established by the interpreter length invariant `interpretWordFrom_length` casing the two `Fin 2` reconstructed
generators (index `0` = `eta`, index `1` = `mu`).  The interchange field remains the genuine cap-free
disjoint-window commute (`embedLocalMap_disjointCommute`, reused verbatim); the four congruence fields are fold
functoriality.  Hence `crossPairPushoutNonConvUnconditional` is hypothesis-free and `fxAmalg_hasLiveMonadPushoutIsFalse`
(`DeciderReseat.lean`) is now `true`.  `= true`. -/
def fxAmalg_hasPushoutArityFoldConvSoundness : Bool := true

end FX1Poly.Polygraph.Amalgam
