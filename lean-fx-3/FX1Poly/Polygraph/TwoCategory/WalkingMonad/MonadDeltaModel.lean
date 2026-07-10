import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MonotoneMap
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.Spine
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadSaturatedConv
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadSaturatedDeltaReps

/-! # WalkingMonad — the Δ model: the covariant monotone-map fold is SOUND for the walking monad

The augmented simplex category Δ₊ IS the walking monad (Street, "The formal theory of monads"; Mac Lane §VII.5):
a 2-cell between `t`-power paths is a MONOTONE MAP between finite ordinals, the unit `eta` is a FACE `δ` (grows
the ordinal), the multiplication `mu` is a DEGENERACY `σ` (merges), and the three monad LAWS are the SIMPLICIAL
IDENTITIES.  This file re-aims the monotone-map machinery — REFUTED for the walking adjunction
(`covariantMonotoneMapOf_notSound`, because the adjunction's two homs have opposite variance) — at the walking
monad, where there is ONE object, ONE variance, and the covariant fold IS the sound canonicalization carrier.

## Why the refuted-for-adjunction fold lives here

The adjunction's `monotoneMapOf` folds a CUP (`0 ⇒ 2`) to a face and a CAP (`2 ⇒ 0`) to a degeneracy, and half the
`base ⟶ tip` blocks flip variance — so no single covariant fold is sound (`covariantMonotoneMapOf_notSound`).  The
monad's atoms are `eta : 0 ⇒ 1` and `mu : 2 ⇒ 1`, BOTH covariant, and the "width" of a `t`-power path is just its
LENGTH (each `t` is one ordinal generator, no half-block).  So the same fold, retuned to these arities and to
`length` as width, is uniform-variance and sound.

## What this file ships (each piece zero-axiom)

  * **`monadMonoStepAtom` / `monadMonotoneMapOf`** — the retuned fold: `eta` (arity `(0,1)`) post-composes a face
    `δ_p` and grows the width, `mu` (arity `(2,1)`) post-composes a degeneracy `σ_p` and shrinks it, with `p` the
    left-whisker length.  Structural fold — it COMPUTES (the smokes are `rfl`).
  * **structural-fragment SOUNDNESS** (`monadMonotoneMapOf_eq_of_interchangeFreeStep`) — the fold reads only the
    spine, so every one of the eleven structural strict-2-category laws preserves it
    (`TwoCellStepInterchangeFree.spine_eq`).
  * ★ **the THREE monad laws are SOUND for the fold** — at the seed by `rfl`, and GENUINELY (positive width) by the
    shipped simplicial / commutation identities:
      - **left unit** via `snakeCollapseAtWidth` (`= composeMap_faceMap_degenMap`, `σ_p ∘ δ_p = id`),
      - **right unit** via `composeMap_faceMap_succ_degenMap` (`σ_p ∘ δ_{p+1} = id`),
      - **associativity** via `composeMap_degenMap_degenMap_commute` (`σ_j ∘ σ_i = σ_i ∘ σ_{j+1}`).
    This is the headline: the fold refuted for the adjunction is sound for the monad, and the discharging lemmas
    already exist.
  * the `MonadSaturatedCanonicalization` structure + `monadDecideSaturatedConvViaMonotoneMap` decision assembly.

Raw Lean 4 + Init; `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free (the model is plain
`List Nat`; the fold is structural; the law soundness is `rfl` or a shipped simplicial/commutation lemma).
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-! ## The retuned fold (relocated to `MonadSaturatedDeltaReps`)

The retuned Schanuel–Street monotone-map fold (`monadMonoStepAtom` / `monadMonotoneMapOf`), its generator smokes,
the structural-fragment soundness leg (`monadMonotoneMapOf_eq_of_interchangeFreeStep`), and the three monad-law
fold-soundness theorems (seed `rfl` + positive-width simplicial / commutation identities) are the conv-FREE carrier;
they are relocated (MONAD-R7 r4) to the bespoke-free deep bridge `MonadSaturatedDeltaReps` and imported from there,
so the survivor lane can fold conv-decoupled.  The `MonadSaturatedCanonicalization` struct + the decision assembly
below are abstract over ANY carrier and STAY here with the bespoke `MonadSaturatedTwoCellConv`. -/

/-! ## The Schanuel–Street monotone-map canonicalization + the decision modulo it

By Street / Mac Lane, the walking monad's hom-categories are Δ₊: a 2-cell is a MONOTONE MAP between finite
ordinals, and two 2-cells are saturated-equal exactly when their maps agree.  The canonicalization
(`monadMonotoneMapOf` with SOUNDNESS `mapEqOfConv` and COMPLETENESS `convOfMapEq`) is the genuine remaining
content; the decision assembly around it is shipped, zero-axiom. -/

/-- The **Schanuel–Street monotone-map canonical form**: a 2-cell of the walking monad is a monotone map between
finite ordinals, encoded as the weakly-increasing `List Nat` of its values.  Equality is `List Nat`'s zero-axiom
`DecidableEq`. -/
abbrev MonadCanonicalForm : Type := List Nat

/-- The walking monad's **saturated canonicalization** — the monotone-map normal form packaged with its two
invariance directions: `mapEqOfConv` (SOUND — saturated-convertible cells have equal maps, the three monad laws
being the simplicial identities) and `convOfMapEq` (COMPLETE — equal maps reconstruct a convertibility).  This is
the genuine remaining content ("the walking monad is Δ₊" mechanized); the decision below consumes it. -/
structure MonadSaturatedCanonicalization where
  /-- The monotone-map normal form of a saturated 2-cell. -/
  monotoneMapOf : {sourceMode targetMode : MonadMode} →
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode} →
    RawTwoCellExpr monadModeSignature sourcePath targetPath → MonadCanonicalForm
  /-- SOUNDNESS: saturated-convertible cells have equal monotone maps (the three monad laws are the simplicial
  identities — the NO-direction of the decision). -/
  mapEqOfConv : {sourceMode targetMode : MonadMode} →
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode} →
    {cellA cellB : RawTwoCellExpr monadModeSignature sourcePath targetPath} →
    MonadSaturatedTwoCellConv cellA cellB → monotoneMapOf cellA = monotoneMapOf cellB
  /-- COMPLETENESS: cells with equal monotone maps are saturated-convertible (the reconstruction — the
  YES-direction of the decision). -/
  convOfMapEq : {sourceMode targetMode : MonadMode} →
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode} →
    {cellA cellB : RawTwoCellExpr monadModeSignature sourcePath targetPath} →
    monotoneMapOf cellA = monotoneMapOf cellB → MonadSaturatedTwoCellConv cellA cellB

/-- ★ **Decide walking-monad saturated convertibility via the monotone map.**  Given the canonicalization, compare
the two cells' monotone maps by list equality: equal maps ⟹ `isTrue` (via `convOfMapEq`); unequal maps ⟹
`isFalse`, because `mapEqOfConv` (soundness) would force them equal.  Both branches discharged from the
canonicalization's two directions — the decision assembly is complete. -/
def monadDecideSaturatedConvViaMonotoneMap (canon : MonadSaturatedCanonicalization)
    {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
    (cellA cellB : RawTwoCellExpr monadModeSignature sourcePath targetPath) :
    Decidable (MonadSaturatedTwoCellConv cellA cellB) :=
  match (inferInstance : Decidable (canon.monotoneMapOf cellA = canon.monotoneMapOf cellB)) with
  | isTrue mapsEqual => isTrue (canon.convOfMapEq mapsEqual)
  | isFalse mapsDiffer => isFalse (fun conv => mapsDiffer (canon.mapEqOfConv conv))

/-- The walking monad's **saturated 2-cell word-problem interface**: saturated convertibility is decidable on
every parallel pair of free 2-cells. -/
abbrev MonadDecidableSaturatedTwoCellConvFor : Type :=
  {sourceMode targetMode : MonadMode} →
  {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode} →
  (cellA cellB : RawTwoCellExpr monadModeSignature sourcePath targetPath) →
  Decidable (MonadSaturatedTwoCellConv cellA cellB)

/-- ★ **The walking monad's saturated 2-cell word problem, modulo the canonicalization.**  Supplying the
Schanuel–Street monotone-map canonicalization inhabits the full saturated decision interface — it decides EVERY
parallel pair. -/
@[reducible] def monadSaturatedWordProblemModuloCanonicalization
    (canon : MonadSaturatedCanonicalization) : MonadDecidableSaturatedTwoCellConvFor :=
  fun cellA cellB => monadDecideSaturatedConvViaMonotoneMap canon cellA cellB

/-! ## Honesty markers -/

/-- **ESTABLISHED.**  The covariant monotone-map fold `monadMonotoneMapOf` — REFUTED as a canonicalization carrier
for the walking ADJUNCTION (`covariantMonotoneMapOf_notSound`) — is SOUND for the walking MONAD: the structural
fragment preserves it (`monadMonotoneMapOf_eq_of_interchangeFreeStep`), and each of the three monad laws holds in
the model, at the seed by `rfl` and at positive width by the shipped simplicial / commutation identities
(`monadMonotoneMapOf_whiskeredLeftUnit_via_simplicialIdentity`,
`monadMonotoneMapOf_rightUnit_via_succSimplicialIdentity`, `monadMonotoneMapOf_assoc_via_degenCommute`).  This is
the re-aiming the MonotoneMap quarantine anticipated: one object, one variance, the fold is the carrier.
`= true`. -/
def fxMonad_hasMonotoneMapFoldSoundOnLaws : Bool := true

/-- **Honesty marker.**  The full saturated DECISION is shipped MODULO the Schanuel–Street monotone-map
canonicalization (`MonadSaturatedCanonicalization`): the decision assembly
(`monadDecideSaturatedConvViaMonotoneMap`) is complete and zero-axiom.  The SOUNDNESS field `mapEqOfConv` is now
COMPLETE (`monadMonotoneMapOf_mapEqOfConv`, `WalkingMonad/MonadDeltaDecision`): the structural leg, the three
monad-law legs, the vcomp/whisker congruences, AND the Godement / `ofFull` interchange invariance
(`monadMonotoneMapOf_interchange` — the disjoint-window two-block commute, cap-free on Δ) are all discharged.  The
COMPLETENESS field `convOfMapEq` is now INHABITED: the EZ reconstruction `cell ≈ canon cell` is CLOSED for all five
`normalizeCell` cases.  The `vcomp` case (`monadNormalize_vcomp`, `WalkingMonad/MonadNormalizeVcomp`) combines the
2-cell half `wordMul_vcomp` (`fxMonad_hasVcompWordMultiplicativity`, zero-axiom) with the now-shipped DATA bridge
`canonCounts_vcomp : canonCounts (vcomp) = composeCounts (canonCounts, canonCounts)` — the pure `List Nat`
functoriality `countsOf ∘ composeMap = composeCounts ∘ countsOf` (`countsOf_composeMap`).  Hence
`monadNormalize : MonadNormalizesToCanon` is inhabited, `MonadSaturatedCanonicalization` is inhabited
(`monadSaturatedCanonicalization`), and the decision `monadSaturatedTwoCellDecision` is real and non-vacuous both
ways (`fxMonad_hasSaturatedWordProblemClosed`).  `= true`. -/
def fxMonad_hasMonotoneMapDecisionAssembled : Bool := true

end FX1Poly.Polygraph
