import FX1Poly.Polygraph.Computad.MonadSeed
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.Model
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.Spine
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MonotoneMap

/-! # WalkingMonad/MonadSaturatedDeltaReps — the bespoke-free DEEP saturated-Δ representatives bridge

MONAD-R7 r4 (the deep-stratum relocation) collects the pure-bespoke saturated-Δ chain's conv-FREE lower stratum
into this bridge, so the SURVIVOR files (the idempotent reps, the Gen twins) can consume the walking-monad skeleton
(the law-composite cells, the monotone-map engine, the canonical words) WITHOUT importing the bespoke
`MonadSaturatedTwoCellConv` inductive.  Everything here is `RawTwoCellExpr` / `List Nat` / `Nat` combinatorics over
the already-bespoke-free monad seed (`Computad/MonadSeed`) and free-2-cell substrate (`FreeTwoCell/Model`); the
bridge imports NO file carrying the saturated-convertibility inductive, so a survivor importing only this bridge is
provably conv-decoupled.  This is the DEEP companion to the shallow `MonadSaturatedSkeletonReps` (the embed
stratum); the two together carry the whole conv-FREE skeleton the r3 layer banked.

## What this file ships (relocated VERBATIM from the chain, names / namespace / meaning preserved)

  * the unit / multiplication free 2-cells (`monadUnitTwoCell` / `monadMulTwoCell`) and the three law composites
    (`monadLeftUnitCell` / `monadRightUnitCell` / `monadAssocLeftCell` / `monadAssocRightCell` / `monadIdTCell`),
    relocated from `MonadSaturatedConv` — the RHS/LHS representatives the saturated relation's law constructors
    quote (`MonadSaturatedConv` now imports this bridge for exactly these, single home, no duplication).
  * the retuned Schanuel–Street monotone-map fold (`monadMonoStepAtom` / `monadMonotoneMapOf`) with its generator
    smokes, the structural-fragment soundness leg (`monadMonotoneMapOf_eq_of_interchangeFreeStep`), and the three
    monad-law fold-soundness theorems (seed `rfl` + positive-width simplicial / commutation identities), relocated
    from `MonadDeltaModel` — the conv-FREE carrier the survivor lane folds through (the `MonadSaturatedCanonicalization`
    struct + `monadDecideSaturatedConvViaMonotoneMap` decision assembly STAY in `MonadDeltaModel`, abstract over any
    carrier).

Raw Lean 4 + Init; `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free (RawTwoCellExpr
constructors, no proposition).  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-! ## The unit / multiplication as free 2-cells + the three law composites -/

/-- The seed's UNIT embeds as a free 2-cell `id_point ⇒ t`. -/
def monadUnitTwoCell :
    RawTwoCellExpr monadModeSignature (ModalityPath.nil (graph := monadGraph) MonadMode.point) monadT :=
  RawTwoCellExpr.gen MonadTwoCell.eta

/-- The seed's MULTIPLICATION embeds as a free 2-cell `t·t ⇒ t`. -/
def monadMulTwoCell :
    RawTwoCellExpr monadModeSignature monadTThenT monadT :=
  RawTwoCellExpr.gen MonadTwoCell.mu

/-- The **left-unit composite** `mu ∘ (eta ▷ t)` — the unit whiskered on the right by `t`, then the
multiplication.  A 2-cell `t ⇒ t`; the left-unit law asserts it is `id_t`. -/
def monadLeftUnitCell : RawTwoCellExpr monadModeSignature monadT monadT :=
  RawTwoCellExpr.vcomp
    (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT monadUnitTwoCell)
    monadMulTwoCell

/-- The **right-unit composite** `mu ∘ (t ◁ eta)` — the unit whiskered on the left by `t`, then the
multiplication.  A 2-cell `t ⇒ t`; the right-unit law asserts it is `id_t`. -/
def monadRightUnitCell : RawTwoCellExpr monadModeSignature monadT monadT :=
  RawTwoCellExpr.vcomp
    (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT monadUnitTwoCell)
    monadMulTwoCell

/-- The **left-associativity composite** `mu ∘ (mu ▷ t)` — multiply the first two `t`'s, then multiply the
result with the third.  A 2-cell `t·t·t ⇒ t`. -/
def monadAssocLeftCell : RawTwoCellExpr monadModeSignature monadTThenTThenT monadT :=
  RawTwoCellExpr.vcomp
    (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT monadMulTwoCell)
    monadMulTwoCell

/-- The **right-associativity composite** `mu ∘ (t ◁ mu)` — multiply the last two `t`'s, then multiply the first
with the result.  A 2-cell `t·t·t ⇒ t` (the source `t·(t·t)` is DEFINITIONALLY `(t·t)·t`). -/
def monadAssocRightCell : RawTwoCellExpr monadModeSignature monadTThenTThenT monadT :=
  RawTwoCellExpr.vcomp
    (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT monadMulTwoCell)
    monadMulTwoCell

/-- The identity 2-cell on `t` (the RHS of both unit laws). -/
def monadIdTCell : RawTwoCellExpr monadModeSignature monadT monadT :=
  RawTwoCellExpr.id (signature := monadModeSignature) monadT

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

end FX1Poly.Polygraph
