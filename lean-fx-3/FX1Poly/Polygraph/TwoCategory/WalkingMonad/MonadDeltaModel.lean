import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MonotoneMap
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.Spine
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadSaturatedConv

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

/-! ## The retuned fold: `eta ↦ face`, `mu ↦ degeneracy`, width = path length -/

/-- One fold step for the walking monad: `eta` (`0 ⇒ 1`, the unit) post-composes a face `δ_p` and grows the width
by one; `mu` (`2 ⇒ 1`, the multiplication) post-composes a degeneracy `σ_p` and shrinks the width by one.  The
position `p` is the left-whisker LENGTH (each `t` to the left is one ordinal position — no half-block, unlike the
adjunction's `blockOf`).  Any other arity leaves the map unchanged (never occurs at the eta/mu monad seed). -/
def monadMonoStepAtom {sourceMode targetMode : MonadMode}
    (state : Nat × List Nat) (atom : SpineAtom monadModeSignature sourceMode targetMode) :
    Nat × List Nat :=
  let position := atom.leftContext.length
  match atom.generatorDom.length, atom.generatorCod.length with
  | 0, 1 => (state.1 + 1, composeMap state.2 (faceMap position state.1))
  | 2, 1 => (state.1 - 1, composeMap state.2 (degenMap position (state.1 - 1)))
  | _, _ => state

/-- ★ The **Schanuel–Street monotone-map normal form** of a free 2-cell of the walking monad: fold the eta / mu
spine into the composite face / degeneracy map, starting from the identity on the source path LENGTH (the source
ordinal).  This is the candidate `monotoneMapOf` for `MonadSaturatedCanonicalization`.  Structural fold — it
COMPUTES. -/
def monadMonotoneMapOf {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
    (cell : RawTwoCellExpr monadModeSignature sourcePath targetPath) : List Nat :=
  (cell.spine.foldl monadMonoStepAtom (sourcePath.length, idMap sourcePath.length)).2

/-! ## Smoke: the fold COMPUTES the generators -/

/-- Smoke: the bare unit (an `eta` at the empty source, width `0`) folds to the empty face `[]`. -/
theorem monadMonotoneMapOf_unit : monadMonotoneMapOf monadUnitTwoCell = [] := rfl

/-- Smoke: the bare multiplication (a `mu`, source `t·t` of width `2`) folds to the degeneracy `σ_0 = [0, 0]`. -/
theorem monadMonotoneMapOf_mul : monadMonotoneMapOf monadMulTwoCell = [0, 0] := rfl

/-! ## Soundness leg 1: `monadMonotoneMapOf` is invariant under the interchange-free structural fragment -/

/-- `monadMonotoneMapOf` depends on the cell only through its spine (the boundary, hence the source length, is
fixed): equal spines give equal monotone maps. -/
theorem monadMonotoneMapOf_congr_of_spine_eq {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
    {cellOne cellTwo : RawTwoCellExpr monadModeSignature sourcePath targetPath}
    (spineEqual : cellOne.spine = cellTwo.spine) : monadMonotoneMapOf cellOne = monadMonotoneMapOf cellTwo := by
  show (cellOne.spine.foldl monadMonoStepAtom (sourcePath.length, idMap sourcePath.length)).2
    = (cellTwo.spine.foldl monadMonoStepAtom (sourcePath.length, idMap sourcePath.length)).2
  rw [spineEqual]

/-- ★ **Soundness of `monadMonotoneMapOf` under the interchange-free structural fragment**: every one of the
eleven structural strict-2-category laws (identity removal, re-association, whisker distribution / unit —
congruences included) preserves the monotone map, because each preserves the spine on the nose
(`TwoCellStepInterchangeFree.spine_eq`).  This is the structural-fragment leg of `mapEqOfConv`. -/
theorem monadMonotoneMapOf_eq_of_interchangeFreeStep {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
    {cellOne cellTwo : RawTwoCellExpr monadModeSignature sourcePath targetPath}
    (step : TwoCellStepInterchangeFree monadModeSignature cellOne cellTwo) :
    monadMonotoneMapOf cellOne = monadMonotoneMapOf cellTwo :=
  monadMonotoneMapOf_congr_of_spine_eq step.spine_eq

/-! ## Soundness leg 2: the three monad laws are SOUND for the fold

At the seed each law's two sides fold to EQUAL maps (`rfl`); the genuine content — that this is the simplicial
algebra, not a small-width accident — is exposed at POSITIVE width, where the fold genuinely composes faces /
degeneracies and the collapse IS a shipped simplicial / commutation identity. -/

/-- ★ **The LEFT-UNIT law is sound at the seed** — `monadMonotoneMapOf (mu ∘ (eta ▷ t)) = monadMonotoneMapOf id_t`
(both fold to `idMap 1 = [0]`). -/
theorem monadMonotoneMapOf_leftUnit_eq_id :
    monadMonotoneMapOf monadLeftUnitCell = monadMonotoneMapOf monadIdTCell := rfl

/-- ★ **The RIGHT-UNIT law is sound at the seed** — `monadMonotoneMapOf (mu ∘ (t ◁ eta)) = monadMonotoneMapOf id_t`
(both fold to `idMap 1 = [0]`). -/
theorem monadMonotoneMapOf_rightUnit_eq_id :
    monadMonotoneMapOf monadRightUnitCell = monadMonotoneMapOf monadIdTCell := rfl

/-- ★ **The ASSOCIATIVITY law is sound at the seed** — `monadMonotoneMapOf (mu ∘ (mu ▷ t)) = monadMonotoneMapOf
(mu ∘ (t ◁ mu))` (both fold to `[0, 0, 0]`, at the non-trivial width `3`). -/
theorem monadMonotoneMapOf_assoc_eq :
    monadMonotoneMapOf monadAssocLeftCell = monadMonotoneMapOf monadAssocRightCell := rfl

/-- ★★ **The LEFT-UNIT law collapses GENUINELY via the simplicial identity `σ_p ∘ δ_p = id`.**  Whiskering the
left-unit composite by `t` lifts its width to `2`; the fold then computes `composeMap (composeMap (idMap 2)
(faceMap 1 2)) (degenMap 1 2)` — a face `δ_1` then a degeneracy `σ_1` at the shifted position `1` — which equals
`idMap 2` by `snakeCollapseAtWidth 1 2`, i.e. by the simplicial identity `composeMap_faceMap_degenMap` at the
NON-trivial position `1`.  The honest witness that the unit law's collapse is the simplicial identity, holding at
positive width, exactly where the covariant fold was REFUTED for the adjunction. -/
theorem monadMonotoneMapOf_whiskeredLeftUnit_via_simplicialIdentity :
    monadMonotoneMapOf (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT monadLeftUnitCell)
      = idMap 2 := by
  show composeMap (composeMap (idMap 2) (faceMap 1 2)) (degenMap 1 2) = idMap 2
  exact snakeCollapseAtWidth 1 2

/-- The whiskered identity on `t` (at the same `t` context) also folds to `idMap 2` — so the whiskered LEFT-UNIT
law `t ◁ (mu ∘ (eta ▷ t)) ≈ t ◁ id_t` holds in the model at width `2`, matching
`MonadSaturatedTwoCellConv.whiskerLeftCongr _ MonadSaturatedTwoCellConv.leftUnit`. -/
theorem monadMonotoneMapOf_whiskeredIdT_eq :
    monadMonotoneMapOf (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT monadIdTCell)
      = idMap 2 := rfl

/-- ★ **The whiskered LEFT-UNIT law holds in the model at positive width** — the genuine, non-vacuous manifestation
that the covariant fold is SOUND for the walking monad's unit law. -/
theorem monadMonotoneMapOf_whiskeredLeftUnit :
    monadMonotoneMapOf (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT monadLeftUnitCell)
      = monadMonotoneMapOf (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT monadIdTCell) :=
  monadMonotoneMapOf_whiskeredLeftUnit_via_simplicialIdentity.trans monadMonotoneMapOf_whiskeredIdT_eq.symm

/-- ★★ **The RIGHT-UNIT law collapses GENUINELY via the second simplicial identity `σ_p ∘ δ_{p+1} = id`.**  At the
seed the fold computes `composeMap (composeMap (idMap 1) (faceMap 1 1)) (degenMap 0 1)` — a face `δ_1` (one above
the repeated value) then a degeneracy `σ_0` — which equals `idMap 1` by `composeMap_faceMap_succ_degenMap 0 1`,
the OTHER adjacent face–degeneracy simplicial identity.  The right-unit law is the second simplicial relation, as
the left-unit is the first. -/
theorem monadMonotoneMapOf_rightUnit_via_succSimplicialIdentity :
    monadMonotoneMapOf monadRightUnitCell = idMap 1 := by
  show composeMap (faceMap 1 1) (degenMap 0 1) = idMap 1
  exact composeMap_faceMap_succ_degenMap 0 1

/-- ★★ **The ASSOCIATIVITY law is the degeneracy–degeneracy commutation `σ_j ∘ σ_i = σ_i ∘ σ_{j+1}`.**  At the
width-`3` seed the two associativity composites fold to `composeMap (composeMap (idMap 3) (degenMap 0 2))
(degenMap 0 1)` and `composeMap (composeMap (idMap 3) (degenMap 1 2)) (degenMap 0 1)`; stripping the leading
identity (`composeMap_idMap_eq`) these are `composeMap (degenMap 0 2) (degenMap 0 1)` and
`composeMap (degenMap 1 2) (degenMap 0 1)`, equal by `composeMap_degenMap_degenMap_commute 0 0 1`.  So the monad's
associativity IS the codegeneracy relation of Δ₊ — the third and last monad law read off the simplicial algebra. -/
theorem monadMonotoneMapOf_assoc_via_degenCommute :
    monadMonotoneMapOf monadAssocLeftCell = monadMonotoneMapOf monadAssocRightCell := by
  show composeMap (degenMap 0 2) (degenMap 0 1) = composeMap (degenMap 1 2) (degenMap 0 1)
  exact composeMap_degenMap_degenMap_commute 0 0 1 (Nat.le_refl 0) (Nat.lt_succ_self 0)

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
(`monadDecideSaturatedConvViaMonotoneMap`) is complete and zero-axiom, and the structural leg plus the three
monad-law soundness legs are shipped, but the FULL residual — `mapEqOfConv` under an ARBITRARY whisker context
(threading the shipped simplicial / commutation identities through the fold's block algebra at every position and
width) together with the Godement / disjoint-whisker EXCHANGE invariance, and the COMPLETENESS `convOfMapEq`
(every cell reconstructs to its map's EZ epi-then-mono staircase) — is the genuine remaining "walking monad is
Δ₊" content, the same block-scale bookkeeping the adjunction's matching route required.  `= false`. -/
def fxMonad_hasMonotoneMapDecisionAssembled : Bool := false

end FX1Poly.Polygraph
