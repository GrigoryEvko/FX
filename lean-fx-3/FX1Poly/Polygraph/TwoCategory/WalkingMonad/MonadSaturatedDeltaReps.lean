import FX1Poly.Polygraph.Computad.MonadSeed
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.Model
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.Spine
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MonotoneMap
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadSaturatedSkeletonReps

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

/-! ## The monotone-fold ENGINE (block/offset threading), relocated from `MonadMonotoneEngine` -/


/-! ## The fold engine -/

/-- Fold the monotone-map step `monadMonoStepAtom` over a spine atom list — the spine-list-level engine
underlying `monadMonotoneMapOf`. -/
def monadMonoProcessSpine {sourceMode targetMode : MonadMode}
    (state : Nat × List Nat)
    (atoms : List (SpineAtom monadModeSignature sourceMode targetMode)) : Nat × List Nat :=
  atoms.foldl monadMonoStepAtom state

/-- Run the monotone-map fold over ONE cell's spine from a given state (its contribution alone, empty tail) — the
per-block fold unit the context decomposition peels. -/
def monadRunMonoCell {overallSource overallTarget localSource localTarget : MonadMode}
    (state : Nat × List Nat)
    (leftAcc : ModalityPath monadModeSignature.graph overallSource localSource)
    (rightAcc : ModalityPath monadModeSignature.graph localTarget overallTarget)
    {localDom localCod : ModalityPath monadModeSignature.graph localSource localTarget}
    (cell : RawTwoCellExpr monadModeSignature localDom localCod) : Nat × List Nat :=
  monadMonoProcessSpine state (cell.spineDiff leftAcc rightAcc [])

/-- ★ **The fold-decomposition over a `spineDiff` difference-list.**  Folding `monadMonoStepAtom` over
`cell.spineDiff leftAcc rightAcc rest` equals running the cell alone (`monadRunMonoCell`) then over `rest`.
Structural recursion on the cell (generator / identity definitional; vcomp peels each factor; the whiskerings
recurse under shifted accumulators). -/
theorem monadMonoProcessSpine_spineDiff {overallSource overallTarget : MonadMode} :
    {localSource localTarget : MonadMode} →
    (leftAcc : ModalityPath monadModeSignature.graph overallSource localSource) →
    (rightAcc : ModalityPath monadModeSignature.graph localTarget overallTarget) →
    {localDom localCod : ModalityPath monadModeSignature.graph localSource localTarget} →
    (cell : RawTwoCellExpr monadModeSignature localDom localCod) →
    (state : Nat × List Nat) →
    (rest : List (SpineAtom monadModeSignature overallSource overallTarget)) →
    monadMonoProcessSpine state (cell.spineDiff leftAcc rightAcc rest)
      = monadMonoProcessSpine (monadRunMonoCell state leftAcc rightAcc cell) rest
  | _, _, _, _, _, _, .gen _, _, _ => rfl
  | _, _, _, _, _, _, .id _, _, _ => rfl
  | _, _, leftAcc, rightAcc, _, _, .vcomp cellLeft cellRight, state, rest => by
      show monadMonoProcessSpine state
          (cellLeft.spineDiff leftAcc rightAcc (cellRight.spineDiff leftAcc rightAcc rest))
        = monadMonoProcessSpine (monadRunMonoCell state leftAcc rightAcc (RawTwoCellExpr.vcomp cellLeft cellRight)) rest
      rw [monadMonoProcessSpine_spineDiff leftAcc rightAcc cellLeft state (cellRight.spineDiff leftAcc rightAcc rest),
        monadMonoProcessSpine_spineDiff leftAcc rightAcc cellRight (monadRunMonoCell state leftAcc rightAcc cellLeft) rest]
      congr 1
      show monadRunMonoCell (monadRunMonoCell state leftAcc rightAcc cellLeft) leftAcc rightAcc cellRight
        = monadMonoProcessSpine state (cellLeft.spineDiff leftAcc rightAcc (cellRight.spineDiff leftAcc rightAcc []))
      rw [monadMonoProcessSpine_spineDiff leftAcc rightAcc cellLeft state (cellRight.spineDiff leftAcc rightAcc [])]
      rfl
  | _, _, leftAcc, rightAcc, _, _, .whiskerLeft oneCell body, state, rest =>
      monadMonoProcessSpine_spineDiff (composePath leftAcc oneCell) rightAcc body state rest
  | _, _, leftAcc, rightAcc, _, _, .whiskerRight oneCell body, state, rest =>
      monadMonoProcessSpine_spineDiff leftAcc (composePath oneCell rightAcc) body state rest

/-- Running a vertical composite is running the first factor then the second. -/
theorem monadRunMonoCell_vcomp {overallSource overallTarget localSource localTarget : MonadMode}
    (state : Nat × List Nat)
    (leftAcc : ModalityPath monadModeSignature.graph overallSource localSource)
    (rightAcc : ModalityPath monadModeSignature.graph localTarget overallTarget)
    {oneCellF oneCellG oneCellH : ModalityPath monadModeSignature.graph localSource localTarget}
    (cellLeft : RawTwoCellExpr monadModeSignature oneCellF oneCellG)
    (cellRight : RawTwoCellExpr monadModeSignature oneCellG oneCellH) :
    monadRunMonoCell state leftAcc rightAcc (RawTwoCellExpr.vcomp cellLeft cellRight)
      = monadRunMonoCell (monadRunMonoCell state leftAcc rightAcc cellLeft) leftAcc rightAcc cellRight :=
  monadMonoProcessSpine_spineDiff leftAcc rightAcc cellLeft state (cellRight.spineDiff leftAcc rightAcc [])

/-- Running a left-whiskered cell shifts the left accumulator by the whisker (definitional). -/
theorem monadRunMonoCell_whiskerLeft {overallSource overallTarget localSource localMiddle localTarget : MonadMode}
    (state : Nat × List Nat)
    (leftAcc : ModalityPath monadModeSignature.graph overallSource localSource)
    (rightAcc : ModalityPath monadModeSignature.graph localTarget overallTarget)
    (oneCell : ModalityPath monadModeSignature.graph localSource localMiddle)
    {oneCellG oneCellH : ModalityPath monadModeSignature.graph localMiddle localTarget}
    (body : RawTwoCellExpr monadModeSignature oneCellG oneCellH) :
    monadRunMonoCell state leftAcc rightAcc (RawTwoCellExpr.whiskerLeft oneCell body)
      = monadRunMonoCell state (composePath leftAcc oneCell) rightAcc body := rfl

/-- Running a right-whiskered cell shifts the right accumulator by the whisker (definitional). -/
theorem monadRunMonoCell_whiskerRight {overallSource overallTarget localSource localMiddle localTarget : MonadMode}
    (state : Nat × List Nat)
    (leftAcc : ModalityPath monadModeSignature.graph overallSource localSource)
    (rightAcc : ModalityPath monadModeSignature.graph localTarget overallTarget)
    (oneCell : ModalityPath monadModeSignature.graph localMiddle localTarget)
    {oneCellF oneCellG : ModalityPath monadModeSignature.graph localSource localMiddle}
    (body : RawTwoCellExpr monadModeSignature oneCellF oneCellG) :
    monadRunMonoCell state leftAcc rightAcc (RawTwoCellExpr.whiskerRight oneCell body)
      = monadRunMonoCell state leftAcc (composePath oneCell rightAcc) body := rfl

/-- ★ **Right-context irrelevance.**  `monadMonoStepAtom` reads only the LEFT whisker context (its position) and
the generator arity, never the right context; so `monadRunMonoCell` gives the same result under any right
accumulator — dropping half the Godement / disjoint-whisker context shift for free. -/
theorem monadRunMonoCell_rightContext_irrelevant {overallSource overallTarget : MonadMode} :
    {localSource localTarget : MonadMode} →
    {localDom localCod : ModalityPath monadModeSignature.graph localSource localTarget} →
    (cell : RawTwoCellExpr monadModeSignature localDom localCod) →
    (state : Nat × List Nat) →
    (leftAcc : ModalityPath monadModeSignature.graph overallSource localSource) →
    (rightAccOne rightAccTwo : ModalityPath monadModeSignature.graph localTarget overallTarget) →
    monadRunMonoCell state leftAcc rightAccOne cell = monadRunMonoCell state leftAcc rightAccTwo cell
  | _, _, _, _, .gen _, _, _, _, _ => rfl
  | _, _, _, _, .id _, _, _, _, _ => rfl
  | _, _, _, _, .vcomp cellLeft cellRight, state, leftAcc, rightAccOne, rightAccTwo => by
      rw [monadRunMonoCell_vcomp, monadRunMonoCell_vcomp,
          monadRunMonoCell_rightContext_irrelevant cellLeft state leftAcc rightAccOne rightAccTwo]
      exact monadRunMonoCell_rightContext_irrelevant cellRight _ leftAcc rightAccOne rightAccTwo
  | _, _, _, _, .whiskerLeft oneCell body, state, leftAcc, rightAccOne, rightAccTwo => by
      rw [monadRunMonoCell_whiskerLeft, monadRunMonoCell_whiskerLeft]
      exact monadRunMonoCell_rightContext_irrelevant body state (composePath leftAcc oneCell) rightAccOne rightAccTwo
  | _, _, _, _, .whiskerRight oneCell body, state, leftAcc, rightAccOne, rightAccTwo => by
      rw [monadRunMonoCell_whiskerRight, monadRunMonoCell_whiskerRight]
      exact monadRunMonoCell_rightContext_irrelevant body state leftAcc
        (composePath oneCell rightAccOne) (composePath oneCell rightAccTwo)

/-! ## The length-width invariant -/

/-- The width effect of an `eta` (`0 ⇒ 1`) on the length: `(leftLen + 0 + rightLen) + 1 = leftLen + 1 + rightLen`. -/
theorem monadEtaWidthShift (leftLen rightLen : Nat) :
    leftLen + 0 + rightLen + 1 = leftLen + 1 + rightLen := by
  rw [Nat.add_zero]
  exact Nat.add_right_comm leftLen rightLen 1

/-- The width effect of a `mu` (`2 ⇒ 1`) on the length: `(leftLen + 2 + rightLen) - 1 = leftLen + 1 + rightLen`.
No truncation bites — the source has the two t's, so the length is `≥ 2` before the merge. -/
theorem monadMuWidthShift (leftLen rightLen : Nat) :
    leftLen + 2 + rightLen - 1 = leftLen + 1 + rightLen := by
  rw [Nat.add_right_comm leftLen 2 rightLen]
  show leftLen + rightLen + 1 = leftLen + 1 + rightLen
  exact Nat.add_right_comm leftLen rightLen 1

/-- The length-width invariant at a GENERATOR — split out with FREE boundary paths so casing on the generator is
propext-free. -/
theorem monadRunMonoCell_width_gen {overallSource overallTarget sourceMode targetMode : MonadMode}
    {generatorDom generatorCod : ModalityPath monadModeSignature.graph sourceMode targetMode}
    (generator : MonadTwoCell generatorDom generatorCod)
    (width : Nat) (map : List Nat)
    (leftAcc : ModalityPath monadModeSignature.graph overallSource sourceMode)
    (rightAcc : ModalityPath monadModeSignature.graph targetMode overallTarget)
    (hwidth : width = leftAcc.length + generatorDom.length + rightAcc.length) :
    (monadRunMonoCell (width, map) leftAcc rightAcc (RawTwoCellExpr.gen generator)).1
      = leftAcc.length + generatorCod.length + rightAcc.length := by
  cases generator with
  | eta =>
      show width + 1 = leftAcc.length + monadT.length + rightAcc.length
      rw [hwidth]
      show leftAcc.length + 0 + rightAcc.length + 1 = leftAcc.length + 1 + rightAcc.length
      exact monadEtaWidthShift leftAcc.length rightAcc.length
  | mu =>
      show width - 1 = leftAcc.length + monadT.length + rightAcc.length
      rw [hwidth]
      show leftAcc.length + 2 + rightAcc.length - 1 = leftAcc.length + 1 + rightAcc.length
      exact monadMuWidthShift leftAcc.length rightAcc.length

/-- ★ **The length-width invariant.**  Given the running width equals the current 1-cell length
(`leftAcc · localDom · rightAcc`), running the cell lands the width at the codomain 1-cell length
(`leftAcc · localCod · rightAcc`).  Structural recursion: a generator steps the width by the eta / mu `±1` length
change; a vertical composite threads the invariant; the whiskerings shift the length additively. -/
theorem monadRunMonoCell_width {overallSource overallTarget : MonadMode} :
    {localSource localTarget : MonadMode} →
    {localDom localCod : ModalityPath monadModeSignature.graph localSource localTarget} →
    (cell : RawTwoCellExpr monadModeSignature localDom localCod) →
    (width : Nat) → (map : List Nat) →
    (leftAcc : ModalityPath monadModeSignature.graph overallSource localSource) →
    (rightAcc : ModalityPath monadModeSignature.graph localTarget overallTarget) →
    width = leftAcc.length + localDom.length + rightAcc.length →
    (monadRunMonoCell (width, map) leftAcc rightAcc cell).1
      = leftAcc.length + localCod.length + rightAcc.length
  | _, _, _, _, .gen generator, width, map, leftAcc, rightAcc, hwidth =>
      monadRunMonoCell_width_gen generator width map leftAcc rightAcc hwidth
  | _, _, _, _, .id _, _, _, _, _, hwidth => hwidth
  | _, _, _, _, .vcomp cellLeft cellRight, width, map, leftAcc, rightAcc, hwidth => by
      rw [monadRunMonoCell_vcomp]
      exact monadRunMonoCell_width cellRight _ _ leftAcc rightAcc
        (monadRunMonoCell_width cellLeft width map leftAcc rightAcc hwidth)
  | _, _, _, _, .whiskerLeft oneCell body, width, map, leftAcc, rightAcc, hwidth => by
      rename_i bodyDom bodyCod
      rw [monadRunMonoCell_whiskerLeft,
          monadRunMonoCell_width body width map (composePath leftAcc oneCell) rightAcc (by
            rw [hwidth, ModalityPath.length_composePath oneCell bodyDom,
                ModalityPath.length_composePath leftAcc oneCell,
                Nat.add_assoc leftAcc.length oneCell.length bodyDom.length]),
          ModalityPath.length_composePath leftAcc oneCell,
          ModalityPath.length_composePath oneCell bodyCod,
          Nat.add_assoc leftAcc.length oneCell.length bodyCod.length]
  | _, _, _, _, .whiskerRight oneCell body, width, map, leftAcc, rightAcc, hwidth => by
      rename_i bodyDom bodyCod
      rw [monadRunMonoCell_whiskerRight,
          monadRunMonoCell_width body width map leftAcc (composePath oneCell rightAcc) (by
            rw [hwidth, ModalityPath.length_composePath bodyDom oneCell,
                ModalityPath.length_composePath oneCell rightAcc,
                ← Nat.add_assoc leftAcc.length bodyDom.length oneCell.length,
                Nat.add_assoc (leftAcc.length + bodyDom.length) oneCell.length rightAcc.length]),
          ModalityPath.length_composePath oneCell rightAcc,
          ModalityPath.length_composePath bodyCod oneCell,
          ← Nat.add_assoc leftAcc.length bodyCod.length oneCell.length,
          Nat.add_assoc (leftAcc.length + bodyCod.length) oneCell.length rightAcc.length]

/-- `monadMonotoneMapOf` IS the `.2` of `monadRunMonoCell` from the source-length identity state at empty
accumulators (definitional bridge). -/
theorem monadMonotoneMapOf_eq_runMonoCell {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadModeSignature.graph sourceMode targetMode}
    (cell : RawTwoCellExpr monadModeSignature sourcePath targetPath) :
    monadMonotoneMapOf cell
      = (monadRunMonoCell (sourcePath.length, idMap sourcePath.length)
          (identityPath sourceMode) (identityPath targetMode) cell).2 := rfl

/-! ## The three monad laws GENUINELY at an arbitrary left-whisker context

Each law composite, whiskered by an ARBITRARY 1-cell `W`, folds to the identity map (unit laws) or to a common
map (associativity) at the SHIFTED position `W.length` and width `W.length + k`.  The discharging lemma is the
shipped ∀-general simplicial / commutation identity at those shifted arguments — the concrete meaning of "the law
at context is the same lemma at shifted arguments, no variance apparatus". -/

/-- The whiskered source length `W · t` is `W.length + 1`. -/
theorem monadWhiskerT_length (leftWhisker : ModalityPath monadGraph MonadMode.point MonadMode.point) :
    (composePath leftWhisker monadT).length = leftWhisker.length + 1 :=
  ModalityPath.length_composePath leftWhisker monadT

/-- The whiskered source length `W · t·t·t` is `W.length + 3`. -/
theorem monadWhiskerTTT_length (leftWhisker : ModalityPath monadGraph MonadMode.point MonadMode.point) :
    (composePath leftWhisker monadTThenTThenT).length = leftWhisker.length + 3 :=
  ModalityPath.length_composePath leftWhisker monadTThenTThenT

/-- ★★ **The LEFT-UNIT law folds to the identity at an ARBITRARY left-whisker context.**  `whiskerLeft W (mu ∘
(eta ▷ t))` folds to `idMap (W.length + 1)`: the fold post-composes a face `δ_{W.length}` then a degeneracy
`σ_{W.length}` at width `W.length + 1`, collapsing by `snakeCollapseAtWidth W.length (W.length + 1)` — the
simplicial identity `σ_p ∘ δ_p = id` at the shifted position `p = W.length`, holding at EVERY `W`. -/
theorem monadMonotoneMapOf_whiskeredLeftUnit_atContext
    (leftWhisker : ModalityPath monadGraph MonadMode.point MonadMode.point) :
    monadMonotoneMapOf (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) leftWhisker monadLeftUnitCell)
      = idMap (leftWhisker.length + 1) := by
  show composeMap (composeMap (idMap (composePath leftWhisker monadT).length)
        (faceMap leftWhisker.length (composePath leftWhisker monadT).length))
      (degenMap leftWhisker.length (composePath leftWhisker monadT).length)
    = idMap (leftWhisker.length + 1)
  rw [snakeCollapseAtWidth leftWhisker.length (composePath leftWhisker monadT).length, monadWhiskerT_length]

/-- The whiskered identity on `t` folds to `idMap (W.length + 1)` at the same context. -/
theorem monadMonotoneMapOf_whiskeredIdT_atContext
    (leftWhisker : ModalityPath monadGraph MonadMode.point MonadMode.point) :
    monadMonotoneMapOf (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) leftWhisker monadIdTCell)
      = idMap (leftWhisker.length + 1) := by
  show idMap (composePath leftWhisker monadT).length = idMap (leftWhisker.length + 1)
  rw [monadWhiskerT_length]

/-- ★ **The LEFT-UNIT law is sound for the fold at an ARBITRARY left-whisker context** — the genuine,
non-vacuous manifestation that the covariant fold is sound for the walking monad's unit law, at every position. -/
theorem monadMonotoneMapOf_whiskeredLeftUnit_sound
    (leftWhisker : ModalityPath monadGraph MonadMode.point MonadMode.point) :
    monadMonotoneMapOf (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) leftWhisker monadLeftUnitCell)
      = monadMonotoneMapOf (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) leftWhisker monadIdTCell) :=
  (monadMonotoneMapOf_whiskeredLeftUnit_atContext leftWhisker).trans
    (monadMonotoneMapOf_whiskeredIdT_atContext leftWhisker).symm

/-- ★★ **The RIGHT-UNIT law folds to the identity at an ARBITRARY left-whisker context.**  `whiskerLeft W (mu ∘
(t ◁ eta))` folds to `idMap (W.length + 1)`: the fold post-composes a face `δ_{W.length+1}` then a degeneracy
`σ_{W.length}` at width `W.length + 1`, collapsing by `composeMap_faceMap_succ_degenMap W.length (W.length + 1)` —
the OTHER adjacent simplicial identity `σ_p ∘ δ_{p+1} = id` at the shifted position, holding at EVERY `W`. -/
theorem monadMonotoneMapOf_whiskeredRightUnit_atContext
    (leftWhisker : ModalityPath monadGraph MonadMode.point MonadMode.point) :
    monadMonotoneMapOf (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) leftWhisker monadRightUnitCell)
      = idMap (leftWhisker.length + 1) := by
  show composeMap (composeMap (idMap (composePath leftWhisker monadT).length)
        (faceMap (composePath leftWhisker monadT).length (composePath leftWhisker monadT).length))
      (degenMap leftWhisker.length (composePath leftWhisker monadT).length)
    = idMap (leftWhisker.length + 1)
  rw [monadWhiskerT_length]
  have idPrefix : composeMap (idMap (leftWhisker.length + 1)) (faceMap (leftWhisker.length + 1) (leftWhisker.length + 1))
      = faceMap (leftWhisker.length + 1) (leftWhisker.length + 1) := by
    have collapseId := composeMap_idMap_eq (faceMap (leftWhisker.length + 1) (leftWhisker.length + 1))
    rw [faceMap_length (leftWhisker.length + 1) (leftWhisker.length + 1)] at collapseId
    exact collapseId
  rw [idPrefix, composeMap_faceMap_succ_degenMap leftWhisker.length (leftWhisker.length + 1)]

/-- ★ **The RIGHT-UNIT law is sound for the fold at an ARBITRARY left-whisker context.** -/
theorem monadMonotoneMapOf_whiskeredRightUnit_sound
    (leftWhisker : ModalityPath monadGraph MonadMode.point MonadMode.point) :
    monadMonotoneMapOf (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) leftWhisker monadRightUnitCell)
      = monadMonotoneMapOf (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) leftWhisker monadIdTCell) :=
  (monadMonotoneMapOf_whiskeredRightUnit_atContext leftWhisker).trans
    (monadMonotoneMapOf_whiskeredIdT_atContext leftWhisker).symm

/-- ★ **The ASSOCIATIVITY law is sound for the fold at an ARBITRARY left-whisker context** — both associativity
composites `whiskerLeft W (mu ∘ (mu ▷ t))` and `whiskerLeft W (mu ∘ (t ◁ mu))` fold at width `W.length + 3` to the
two orders of a double codegeneracy, equal by `composeMap_degenMap_degenMap_commute W.length W.length
(W.length + 1)` — the codegeneracy relation `σ_j ∘ σ_i = σ_i ∘ σ_{j+1}` at the shifted position, holding at every
`W`.  The RIGHT composite's inner `mu` fires at position `(W·t).length`, the LEFT composite's at `W.length`; the
`W·t` length collapse and the σσ commutation reconcile them. -/
theorem monadMonotoneMapOf_whiskeredAssoc_sound
    (leftWhisker : ModalityPath monadGraph MonadMode.point MonadMode.point) :
    monadMonotoneMapOf (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) leftWhisker monadAssocLeftCell)
      = monadMonotoneMapOf (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) leftWhisker monadAssocRightCell) := by
  show composeMap (composeMap (idMap (composePath leftWhisker monadTThenTThenT).length)
        (degenMap leftWhisker.length ((composePath leftWhisker monadTThenTThenT).length - 1)))
      (degenMap leftWhisker.length ((composePath leftWhisker monadTThenTThenT).length - 1 - 1))
    = composeMap (composeMap (idMap (composePath leftWhisker monadTThenTThenT).length)
        (degenMap (composePath leftWhisker monadT).length ((composePath leftWhisker monadTThenTThenT).length - 1)))
      (degenMap leftWhisker.length ((composePath leftWhisker monadTThenTThenT).length - 1 - 1))
  rw [monadWhiskerTTT_length, monadWhiskerT_length]
  show composeMap (composeMap (idMap (leftWhisker.length + 3)) (degenMap leftWhisker.length (leftWhisker.length + 2)))
        (degenMap leftWhisker.length (leftWhisker.length + 1))
    = composeMap (composeMap (idMap (leftWhisker.length + 3)) (degenMap (leftWhisker.length + 1) (leftWhisker.length + 2)))
        (degenMap leftWhisker.length (leftWhisker.length + 1))
  have idPrefixLeft : composeMap (idMap (leftWhisker.length + 3)) (degenMap leftWhisker.length (leftWhisker.length + 2))
      = degenMap leftWhisker.length (leftWhisker.length + 2) := by
    have collapse := composeMap_idMap_eq (degenMap leftWhisker.length (leftWhisker.length + 2))
    rw [degenMap_length leftWhisker.length (leftWhisker.length + 2)] at collapse
    exact collapse
  have idPrefixRight : composeMap (idMap (leftWhisker.length + 3)) (degenMap (leftWhisker.length + 1) (leftWhisker.length + 2))
      = degenMap (leftWhisker.length + 1) (leftWhisker.length + 2) := by
    have collapse := composeMap_idMap_eq (degenMap (leftWhisker.length + 1) (leftWhisker.length + 2))
    rw [degenMap_length (leftWhisker.length + 1) (leftWhisker.length + 2)] at collapse
    exact collapse
  rw [idPrefixLeft, idPrefixRight]
  exact composeMap_degenMap_degenMap_commute leftWhisker.length leftWhisker.length (leftWhisker.length + 1)
    (Nat.le_refl leftWhisker.length) (Nat.lt_succ_self leftWhisker.length)

/-! ## Non-vacuity witnesses: the fold separates and identifies genuine parallel pairs -/

/-- A cell on the parallel boundary `t·t ⇒ t·t`: multiply the two t's then re-split via the unit whiskered on the
right — `mu` followed by `eta ▷ t`.  Genuinely distinct from the identity. -/
def monadMergeThenUnitRight : RawTwoCellExpr monadModeSignature monadTThenT monadTThenT :=
  RawTwoCellExpr.vcomp monadMulTwoCell
    (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT monadUnitTwoCell)

/-- The identity 2-cell on `t·t` folds to `idMap 2 = [0, 1]`. -/
theorem monadMonotoneMapOf_idTThenT :
    monadMonotoneMapOf (RawTwoCellExpr.id (signature := monadModeSignature) monadTThenT) = [0, 1] := rfl

/-- `mu ∘ (eta ▷ t)` on `t·t ⇒ t·t` folds to `[1, 1]` — the merge-to-`0` then include-into-the-second map. -/
theorem monadMonotoneMapOf_mergeThenUnitRight :
    monadMonotoneMapOf monadMergeThenUnitRight = [1, 1] := rfl

/-- ★ **Non-vacuity — SEPARATION.**  The identity on `t·t` and `mu ∘ (eta ▷ t)` are a PARALLEL pair (`t·t ⇒ t·t`)
the fold DISTINGUISHES — `[0, 1] ≠ [1, 1]` — so any monotone-map decision correctly rules them non-convertible.
Witnesses that the fold is not constant on a hom-set. -/
theorem monadMonotoneMapOf_separates_idTThenT_mergeThenUnitRight :
    monadMonotoneMapOf (RawTwoCellExpr.id (signature := monadModeSignature) monadTThenT)
      ≠ monadMonotoneMapOf monadMergeThenUnitRight := by
  rw [monadMonotoneMapOf_idTThenT, monadMonotoneMapOf_mergeThenUnitRight]
  intro contra
  injection contra with headEq _
  exact Nat.noConfusion headEq

/-- ★ **Non-vacuity — IDENTIFICATION.**  The left-unit composite and the identity on `t` are a parallel pair
(`t ⇒ t`) the fold IDENTIFIES — both `[0]` — and they ARE saturated-convertible (`leftUnit`).  Together with the
separation witness this shows the intended monotone-map decision is non-trivial: it separates genuinely-distinct
2-cells and identifies law-equal ones. -/
theorem monadMonotoneMapOf_identifies_leftUnit_idT :
    monadMonotoneMapOf monadLeftUnitCell = monadMonotoneMapOf monadIdTCell :=
  monadMonotoneMapOf_leftUnit_eq_id

/-! ## Honesty markers -/

/-- **ESTABLISHED.**  The monotone-fold ENGINE for the walking monad is shipped: the fold-decomposition
(`monadMonoProcessSpine_spineDiff`), the vcomp / whisker / right-context laws, the length-width invariant
(`monadRunMonoCell_width`), and — the headline — the three monad laws sound for the fold at an ARBITRARY
left-whisker context (`monadMonotoneMapOf_whiskeredLeftUnit_sound`, `…RightUnit_sound`, `…Assoc_sound`), each via
the shipped ∀-general simplicial / commutation identity at the shifted position `W.length`.  This is the
block/offset threading the arbitrary-context soundness leg needs, made concrete for the covariant carrier that the
adjunction's variance flip forbids.  `= true`. -/
def fxMonad_hasMonotoneMapEngineAndLawsAtContext : Bool := true

/-- **Honesty marker — `mapEqOfConv` is now COMPLETE; the SOLE residual is completeness `convOfMapEq`.**  The engine,
the laws-at-context, the whisker-shift FACTORIZATION (`monadMonotoneMapOf_vcomp` + the two vcomp-congruence cases),
and the whisker embedding (`MonadWhiskerEmbedding`, the two whisker-congruence cases) were shipped; the LAST owed
case of `mapEqOfConv` — the Godement / `ofFull` interchange invariance — is now DISCHARGED in
`WalkingMonad/MonadDeltaDecision` (`monadMonotoneMapOf_interchange`, via the DISJOINT-WINDOW two-block commute
`embedLocalMap_disjointCommute`: cap-free on Δ, the f-region and g-region blocks commute with the width-delta shift
absorbed by the region split).  Hence the full soundness leg `monadMonotoneMapOf_mapEqOfConv` is COMPLETE and
zero-axiom.  What remains toward inhabiting `MonadSaturatedCanonicalization` is EXACTLY the COMPLETENESS `convOfMapEq`
— the EZ reconstruction: every cell is convertible (under the three monad laws) to the canonical word of its monotone
map.  The eta/mu WORD builder (`wordFromCounts`) + section are shipped, and the normalization `cell ≈ canon cell`
is now CLOSED for all five cases: the `vcomp` case (`monadNormalize_vcomp`, `WalkingMonad/MonadNormalizeVcomp`)
combines the 2-cell half `wordMul_vcomp` (`fxMonad_hasVcompWordMultiplicativity`, zero-axiom) with the now-shipped
DATA bridge `canonCounts_vcomp : canonCounts (vcomp) = composeCounts (canonCounts, canonCounts)` — the pure
`List Nat` functoriality `countsOf ∘ composeMap = composeCounts ∘ countsOf` (`countsOf_composeMap`, base-shifted
structural induction: leading-run head, mid-suffix-shift tail).  Hence `monadNormalize : MonadNormalizesToCanon` is
inhabited, `MonadSaturatedCanonicalization` is inhabited (`monadSaturatedCanonicalization`), and BOTH the
mapEqOfConv half (`fxMonad_hasMapEqOfConvComplete = true`) and the completeness half are now closed —
`fxMonad_hasMonotoneMapDecisionAssembled` / `fxMonad_hasSaturatedWordProblemClosed` are `true`.  `= true`. -/
def fxMonad_hasFullMapEqOfConvAndCompleteness : Bool := true


/-! ## The map-FACTORIZATION stratum, relocated from `MonadMapFactorization` -/


/-! ## The fold lands in a genuine Δ₊ morphism -/

/-- The `mapsInto` invariant at a GENERATOR — split out with FREE boundary paths so casing on the generator is
propext-free.  The `eta` case is `cupPreservesMapsInto` (a face never escapes the grown ordinal); the `mu` case is
`internalCapPreservesMapsInto`, which needs the degeneracy to be INTERNAL (`p < w - 1`) — furnished by the
length-width precondition (`w = leftAcc.length + 2 + rightAcc.length`, so `leftAcc.length < w - 1`). -/
theorem monadRunMonoCell_mapsInto_gen {overallSource overallTarget sourceMode targetMode : MonadMode}
    {generatorDom generatorCod : ModalityPath monadModeSignature.graph sourceMode targetMode}
    (generator : MonadTwoCell generatorDom generatorCod)
    (width : Nat) (map : List Nat)
    (leftAcc : ModalityPath monadModeSignature.graph overallSource sourceMode)
    (rightAcc : ModalityPath monadModeSignature.graph targetMode overallTarget)
    (hwidth : width = leftAcc.length + generatorDom.length + rightAcc.length)
    (hmap : mapsInto map width) :
    mapsInto (monadRunMonoCell (width, map) leftAcc rightAcc (RawTwoCellExpr.gen generator)).2
      (monadRunMonoCell (width, map) leftAcc rightAcc (RawTwoCellExpr.gen generator)).1 := by
  cases generator with
  | eta =>
      show mapsInto (composeMap map (faceMap leftAcc.length width)) (width + 1)
      exact cupPreservesMapsInto leftAcc.length width map hmap
  | mu =>
      show mapsInto (composeMap map (degenMap leftAcc.length (width - 1))) (width - 1)
      -- Rewrite `width - 1` to its `+`-normal form up front (avoids truncated-subtraction lemmas).
      have hwidthPred : width - 1 = leftAcc.length + 1 + rightAcc.length := by
        rw [hwidth]; exact monadMuWidthShift leftAcc.length rightAcc.length
      rw [hwidthPred]
      have hinternal : leftAcc.length < leftAcc.length + 1 + rightAcc.length :=
        Nat.lt_of_lt_of_le (Nat.lt_succ_self leftAcc.length)
          (Nat.le_add_right (leftAcc.length + 1) rightAcc.length)
      have hmapSucc : mapsInto map (leftAcc.length + 1 + rightAcc.length + 1) := by
        have hsucc : leftAcc.length + 1 + rightAcc.length + 1 = width := by
          rw [hwidth]
          show leftAcc.length + 1 + rightAcc.length + 1 = leftAcc.length + 2 + rightAcc.length
          rw [Nat.add_right_comm leftAcc.length 2 rightAcc.length,
              Nat.add_right_comm leftAcc.length 1 rightAcc.length]
        rw [hsucc]; exact hmap
      exact internalCapPreservesMapsInto leftAcc.length (leftAcc.length + 1 + rightAcc.length)
        map hmapSucc hinternal

/-- ★ **The monad's covariant fold lands every free 2-cell in a genuine Δ₊ morphism.**  Given the running width
tracks the current 1-cell length, the running map maps INTO the running width — no out-of-range junk.  Structural
recursion: a generator via `monadRunMonoCell_mapsInto_gen`, a vertical composite threads through both factors (the
intermediate width supplied by `monadRunMonoCell_width`), the whiskerings recurse under shifted accumulators.
Contrast the adjunction, whose boundary cap breaks this very invariant (`counitMonotoneMap_notMapsInto`); the
monad has no boundary cap, so the covariant fold is junk-free everywhere. -/
theorem monadRunMonoCell_mapsInto {overallSource overallTarget : MonadMode} :
    {localSource localTarget : MonadMode} →
    {localDom localCod : ModalityPath monadModeSignature.graph localSource localTarget} →
    (cell : RawTwoCellExpr monadModeSignature localDom localCod) →
    (width : Nat) → (map : List Nat) →
    (leftAcc : ModalityPath monadModeSignature.graph overallSource localSource) →
    (rightAcc : ModalityPath monadModeSignature.graph localTarget overallTarget) →
    width = leftAcc.length + localDom.length + rightAcc.length →
    mapsInto map width →
    mapsInto (monadRunMonoCell (width, map) leftAcc rightAcc cell).2
      (monadRunMonoCell (width, map) leftAcc rightAcc cell).1
  | _, _, _, _, .gen generator, width, map, leftAcc, rightAcc, hwidth, hmap =>
      monadRunMonoCell_mapsInto_gen generator width map leftAcc rightAcc hwidth hmap
  | _, _, _, _, .id _, _, _, _, _, _, hmap => hmap
  | _, _, _, _, .vcomp cellLeft cellRight, width, map, leftAcc, rightAcc, hwidth, hmap => by
      rw [monadRunMonoCell_vcomp]
      exact monadRunMonoCell_mapsInto cellRight _ _ leftAcc rightAcc
        (monadRunMonoCell_width cellLeft width map leftAcc rightAcc hwidth)
        (monadRunMonoCell_mapsInto cellLeft width map leftAcc rightAcc hwidth hmap)
  | _, _, _, _, .whiskerLeft oneCell body, width, map, leftAcc, rightAcc, hwidth, hmap => by
      rename_i bodyDom _
      rw [monadRunMonoCell_whiskerLeft]
      exact monadRunMonoCell_mapsInto body width map (composePath leftAcc oneCell) rightAcc (by
        rw [hwidth, ModalityPath.length_composePath oneCell bodyDom,
            ModalityPath.length_composePath leftAcc oneCell,
            Nat.add_assoc leftAcc.length oneCell.length bodyDom.length]) hmap
  | _, _, _, _, .whiskerRight oneCell body, width, map, leftAcc, rightAcc, hwidth, hmap => by
      rename_i bodyDom _
      rw [monadRunMonoCell_whiskerRight]
      exact monadRunMonoCell_mapsInto body width map leftAcc (composePath oneCell rightAcc) (by
        rw [hwidth, ModalityPath.length_composePath bodyDom oneCell,
            ModalityPath.length_composePath oneCell rightAcc,
            ← Nat.add_assoc leftAcc.length bodyDom.length oneCell.length,
            Nat.add_assoc (leftAcc.length + bodyDom.length) oneCell.length rightAcc.length]) hmap

/-! ## The running map's length is the starting map's length (the map thread preserves length) -/

/-- The fold never changes the map's LENGTH: each step post-composes a same-length factor
(`faceMap`/`degenMap` both have length matching the incoming width), so the running map keeps the starting map's
length.  The domain-width bookkeeping the factorization's associativity side condition needs. -/
theorem monadRunMonoCell_map_length {overallSource overallTarget : MonadMode} :
    {localSource localTarget : MonadMode} →
    {localDom localCod : ModalityPath monadModeSignature.graph localSource localTarget} →
    (cell : RawTwoCellExpr monadModeSignature localDom localCod) →
    (state : Nat × List Nat) →
    (leftAcc : ModalityPath monadModeSignature.graph overallSource localSource) →
    (rightAcc : ModalityPath monadModeSignature.graph localTarget overallTarget) →
    (monadRunMonoCell state leftAcc rightAcc cell).2.length = state.2.length
  | _, _, _, _, .gen generator, state, _, _ => by cases generator <;> exact composeMap_length _ _
  | _, _, _, _, .id _, _, _, _ => rfl
  | _, _, _, _, .vcomp cellLeft cellRight, state, leftAcc, rightAcc => by
      rw [monadRunMonoCell_vcomp, monadRunMonoCell_map_length cellRight _ leftAcc rightAcc,
          monadRunMonoCell_map_length cellLeft state leftAcc rightAcc]
  | _, _, _, _, .whiskerLeft oneCell body, state, leftAcc, rightAcc => by
      rw [monadRunMonoCell_whiskerLeft]
      exact monadRunMonoCell_map_length body state (composePath leftAcc oneCell) rightAcc
  | _, _, _, _, .whiskerRight oneCell body, state, leftAcc, rightAcc => by
      rw [monadRunMonoCell_whiskerRight]
      exact monadRunMonoCell_map_length body state leftAcc (composePath oneCell rightAcc)

/-! ## The incoming map post-composes: the factorization -/

/-- The factorization at a GENERATOR — split out with FREE boundary paths so casing on the generator is
propext-free.  From the identity state the first fold step is exactly the face / degeneracy factor
(`composeMap (idMap width) factor = factor` by `composeMap_idMap_eq`), so the general-state result post-composes
the incoming map onto it. -/
theorem monadRunMonoCell_mapFactor_gen {overallSource overallTarget sourceMode targetMode : MonadMode}
    {generatorDom generatorCod : ModalityPath monadModeSignature.graph sourceMode targetMode}
    (generator : MonadTwoCell generatorDom generatorCod)
    (state : Nat × List Nat)
    (leftAcc : ModalityPath monadModeSignature.graph overallSource sourceMode)
    (rightAcc : ModalityPath monadModeSignature.graph targetMode overallTarget)
    (hwidth : state.1 = leftAcc.length + generatorDom.length + rightAcc.length) :
    (monadRunMonoCell state leftAcc rightAcc (RawTwoCellExpr.gen generator)).2
      = composeMap state.2
          (monadRunMonoCell (state.1, idMap state.1) leftAcc rightAcc (RawTwoCellExpr.gen generator)).2 := by
  cases generator with
  | eta =>
      show composeMap state.2 (faceMap leftAcc.length state.1)
        = composeMap state.2 (composeMap (idMap state.1) (faceMap leftAcc.length state.1))
      have hcollapse : composeMap (idMap state.1) (faceMap leftAcc.length state.1)
          = faceMap leftAcc.length state.1 := by
        have hc := composeMap_idMap_eq (faceMap leftAcc.length state.1)
        rw [faceMap_length leftAcc.length state.1] at hc
        exact hc
      rw [hcollapse]
  | mu =>
      show composeMap state.2 (degenMap leftAcc.length (state.1 - 1))
        = composeMap state.2 (composeMap (idMap state.1) (degenMap leftAcc.length (state.1 - 1)))
      have hsucc : state.1 - 1 + 1 = state.1 := by
        have hwidthPred : state.1 - 1 = leftAcc.length + 1 + rightAcc.length := by
          rw [hwidth]; exact monadMuWidthShift leftAcc.length rightAcc.length
        rw [hwidthPred, hwidth]
        show leftAcc.length + 1 + rightAcc.length + 1 = leftAcc.length + 2 + rightAcc.length
        rw [Nat.add_right_comm leftAcc.length 2 rightAcc.length,
            Nat.add_right_comm leftAcc.length 1 rightAcc.length]
      have hcollapse : composeMap (idMap state.1) (degenMap leftAcc.length (state.1 - 1))
          = degenMap leftAcc.length (state.1 - 1) := by
        have hc := composeMap_idMap_eq (degenMap leftAcc.length (state.1 - 1))
        rw [degenMap_length leftAcc.length (state.1 - 1), hsucc] at hc
        exact hc
      rw [hcollapse]

/-- ★ **The factorization: the incoming map post-composes onto the cell's local map.**  Running the fold from state
`(w, m)` gives the SAME map as running from the identity state `(w, idMap w)`, left-composed with `m`.  The width
thread is independent of the map, so both runs meet the SAME sequence of face / degeneracy factors; the incoming
map accumulates by `composeMap`, associating out by `composeMap_assoc` (its in-range side condition supplied by
`monadRunMonoCell_mapsInto`).  Carries the length-width precondition (needed at each `mu`).  This is the vcomp /
whisker CONGRUENCE-case engine the honesty marker named as `mapEqOfConv`'s first ingredient. -/
theorem monadRunMonoCell_mapFactor {overallSource overallTarget : MonadMode} :
    {localSource localTarget : MonadMode} →
    {localDom localCod : ModalityPath monadModeSignature.graph localSource localTarget} →
    (cell : RawTwoCellExpr monadModeSignature localDom localCod) →
    (state : Nat × List Nat) →
    (leftAcc : ModalityPath monadModeSignature.graph overallSource localSource) →
    (rightAcc : ModalityPath monadModeSignature.graph localTarget overallTarget) →
    state.1 = leftAcc.length + localDom.length + rightAcc.length →
    mapsInto state.2 state.1 →
    (monadRunMonoCell state leftAcc rightAcc cell).2
      = composeMap state.2 (monadRunMonoCell (state.1, idMap state.1) leftAcc rightAcc cell).2
  | _, _, _, _, .gen generator, state, leftAcc, rightAcc, hwidth, _ =>
      monadRunMonoCell_mapFactor_gen generator state leftAcc rightAcc hwidth
  | _, _, _, _, .id _, state, _, _, _, hmap => (composeMap_idMap_right state.2 state.1 hmap).symm
  | _, _, _, _, .vcomp cellLeft cellRight, state, leftAcc, rightAcc, hwidth, hmap => by
      have hS1w : (monadRunMonoCell state leftAcc rightAcc cellLeft).1
          = leftAcc.length + _ + rightAcc.length :=
        monadRunMonoCell_width cellLeft state.1 state.2 leftAcc rightAcc hwidth
      have hT1w : (monadRunMonoCell (state.1, idMap state.1) leftAcc rightAcc cellLeft).1
          = leftAcc.length + _ + rightAcc.length :=
        monadRunMonoCell_width cellLeft state.1 (idMap state.1) leftAcc rightAcc hwidth
      have hS1into : mapsInto (monadRunMonoCell state leftAcc rightAcc cellLeft).2
          (monadRunMonoCell state leftAcc rightAcc cellLeft).1 :=
        monadRunMonoCell_mapsInto cellLeft state.1 state.2 leftAcc rightAcc hwidth hmap
      have hT1into : mapsInto (monadRunMonoCell (state.1, idMap state.1) leftAcc rightAcc cellLeft).2
          (monadRunMonoCell (state.1, idMap state.1) leftAcc rightAcc cellLeft).1 :=
        monadRunMonoCell_mapsInto cellLeft state.1 (idMap state.1) leftAcc rightAcc hwidth
          (idMap_mapsInto state.1)
      have hS1map : (monadRunMonoCell state leftAcc rightAcc cellLeft).2
          = composeMap state.2 (monadRunMonoCell (state.1, idMap state.1) leftAcc rightAcc cellLeft).2 :=
        monadRunMonoCell_mapFactor cellLeft state leftAcc rightAcc hwidth hmap
      have hwidthEq : (monadRunMonoCell state leftAcc rightAcc cellLeft).1
          = (monadRunMonoCell (state.1, idMap state.1) leftAcc rightAcc cellLeft).1 := hS1w.trans hT1w.symm
      have hT1len : (monadRunMonoCell (state.1, idMap state.1) leftAcc rightAcc cellLeft).2.length
          = (idMap state.1).length :=
        monadRunMonoCell_map_length cellLeft (state.1, idMap state.1) leftAcc rightAcc
      rw [monadRunMonoCell_vcomp, monadRunMonoCell_vcomp,
          monadRunMonoCell_mapFactor cellRight (monadRunMonoCell state leftAcc rightAcc cellLeft)
            leftAcc rightAcc hS1w hS1into,
          monadRunMonoCell_mapFactor cellRight
            (monadRunMonoCell (state.1, idMap state.1) leftAcc rightAcc cellLeft)
            leftAcc rightAcc hT1w hT1into,
          hS1map, hwidthEq]
      exact composeMap_assoc state.2 _ _ (by rw [hT1len, idMap_length]; exact hmap)
  | _, _, _, _, .whiskerLeft oneCell body, state, leftAcc, rightAcc, hwidth, hmap => by
      rename_i bodyDom _
      rw [monadRunMonoCell_whiskerLeft, monadRunMonoCell_whiskerLeft]
      exact monadRunMonoCell_mapFactor body state (composePath leftAcc oneCell) rightAcc (by
        rw [hwidth, ModalityPath.length_composePath oneCell bodyDom,
            ModalityPath.length_composePath leftAcc oneCell,
            Nat.add_assoc leftAcc.length oneCell.length bodyDom.length]) hmap
  | _, _, _, _, .whiskerRight oneCell body, state, leftAcc, rightAcc, hwidth, hmap => by
      rename_i bodyDom _
      rw [monadRunMonoCell_whiskerRight, monadRunMonoCell_whiskerRight]
      exact monadRunMonoCell_mapFactor body state leftAcc (composePath oneCell rightAcc) (by
        rw [hwidth, ModalityPath.length_composePath bodyDom oneCell,
            ModalityPath.length_composePath oneCell rightAcc,
            ← Nat.add_assoc leftAcc.length bodyDom.length oneCell.length,
            Nat.add_assoc (leftAcc.length + bodyDom.length) oneCell.length rightAcc.length]) hmap

/-! ## Consequence: the vertical-composition HOMOMORPHISM + the two vcomp-congruence cases of `mapEqOfConv`

The factorization says the running map post-composes; specialized to the whole-cell fold from the identity state,
it gives the clean statement that `monadMonotoneMapOf` is a FUNCTOR on vertical composition — the map of a vertical
composite is the `composeMap` of the two maps.  The two vcomp-congruence cases of `mapEqOfConv`
(`vcompCongrLeft` / `vcompCongrRight`) are then immediate `congrArg`s. -/

/-- The run-level vcomp homomorphism at an ARBITRARY well-formed state: running `α ⊟ β` post-composes the run of
`α` onto the run of `β` started from `α`'s output width's identity.  Proved by `monadRunMonoCell_vcomp` (peel `α`)
then `monadRunMonoCell_mapFactor` (β's incoming map post-composes), with the intermediate width / in-range facts
from `monadRunMonoCell_width` / `monadRunMonoCell_mapsInto`.  Stated with the state / accumulators GENERAL so the
whole-cell corollary instantiates it at the identity state without any `identityPath`-graph unification friction. -/
theorem monadRunMonoCell_vcomp_map {overallSource overallTarget localSource localTarget : MonadMode}
    {oneCellF oneCellG oneCellH : ModalityPath monadGraph localSource localTarget}
    (cellAlpha : RawTwoCellExpr monadModeSignature oneCellF oneCellG)
    (cellBeta : RawTwoCellExpr monadModeSignature oneCellG oneCellH)
    (state : Nat × List Nat)
    (leftAcc : ModalityPath monadGraph overallSource localSource)
    (rightAcc : ModalityPath monadGraph localTarget overallTarget)
    (hwidth : state.1 = leftAcc.length + oneCellF.length + rightAcc.length)
    (hmap : mapsInto state.2 state.1) :
    (monadRunMonoCell state leftAcc rightAcc (RawTwoCellExpr.vcomp cellAlpha cellBeta)).2
      = composeMap (monadRunMonoCell state leftAcc rightAcc cellAlpha).2
          (monadRunMonoCell ((monadRunMonoCell state leftAcc rightAcc cellAlpha).1,
              idMap (monadRunMonoCell state leftAcc rightAcc cellAlpha).1)
            leftAcc rightAcc cellBeta).2 := by
  rw [monadRunMonoCell_vcomp]
  exact monadRunMonoCell_mapFactor cellBeta (monadRunMonoCell state leftAcc rightAcc cellAlpha)
    leftAcc rightAcc (monadRunMonoCell_width cellAlpha state.1 state.2 leftAcc rightAcc hwidth)
    (monadRunMonoCell_mapsInto cellAlpha state.1 state.2 leftAcc rightAcc hwidth hmap)

/-- ★ **The vertical-composition homomorphism.**  `monadMonotoneMapOf (α ⊟ β) = composeMap (map α) (map β)` — the
fold is a FUNCTOR on vertical composition, the whole-cell instance of `monadRunMonoCell_vcomp_map` at the identity
state (width `oneCellF.length`), with `α`'s output width pinned to the middle 1-cell length so `β`'s identity-state
run IS `monadMonotoneMapOf β`. -/
theorem monadMonotoneMapOf_vcomp {sourceMode targetMode : MonadMode}
    {oneCellF oneCellG oneCellH : ModalityPath monadGraph sourceMode targetMode}
    (cellAlpha : RawTwoCellExpr monadModeSignature oneCellF oneCellG)
    (cellBeta : RawTwoCellExpr monadModeSignature oneCellG oneCellH) :
    monadMonotoneMapOf (RawTwoCellExpr.vcomp cellAlpha cellBeta)
      = composeMap (monadMonotoneMapOf cellAlpha) (monadMonotoneMapOf cellBeta) := by
  have hpre : oneCellF.length = 0 + oneCellF.length + 0 := by rw [Nat.add_zero, Nat.zero_add]
  have key := monadRunMonoCell_vcomp_map cellAlpha cellBeta (oneCellF.length, idMap oneCellF.length)
      (identityPath (graph := monadModeSignature.graph) sourceMode)
      (identityPath (graph := monadModeSignature.graph) targetMode)
      hpre (idMap_mapsInto oneCellF.length)
  have hSw : (monadRunMonoCell (oneCellF.length, idMap oneCellF.length)
        (identityPath (graph := monadModeSignature.graph) sourceMode)
        (identityPath (graph := monadModeSignature.graph) targetMode) cellAlpha).1 = oneCellG.length := by
    rw [monadRunMonoCell_width cellAlpha oneCellF.length (idMap oneCellF.length)
          (identityPath (graph := monadModeSignature.graph) sourceMode)
          (identityPath (graph := monadModeSignature.graph) targetMode) hpre]
    show 0 + oneCellG.length + 0 = oneCellG.length
    rw [Nat.add_zero, Nat.zero_add]
  refine (monadMonotoneMapOf_eq_runMonoCell (RawTwoCellExpr.vcomp cellAlpha cellBeta)).trans
    (key.trans ?_)
  rw [hSw]
  rfl

/-- ★ **`mapEqOfConv`, LEFT-vcomp-congruence case.**  Maps agreeing on the left factor give equal composite maps —
immediate from the vcomp homomorphism. -/
theorem monadMonotoneMapOf_vcompCongrLeft {sourceMode targetMode : MonadMode}
    {oneCellF oneCellG oneCellH : ModalityPath monadGraph sourceMode targetMode}
    {cellAlpha cellAlpha' : RawTwoCellExpr monadModeSignature oneCellF oneCellG}
    (cellBeta : RawTwoCellExpr monadModeSignature oneCellG oneCellH)
    (hmap : monadMonotoneMapOf cellAlpha = monadMonotoneMapOf cellAlpha') :
    monadMonotoneMapOf (RawTwoCellExpr.vcomp cellAlpha cellBeta)
      = monadMonotoneMapOf (RawTwoCellExpr.vcomp cellAlpha' cellBeta) := by
  rw [monadMonotoneMapOf_vcomp, monadMonotoneMapOf_vcomp, hmap]

/-- ★ **`mapEqOfConv`, RIGHT-vcomp-congruence case.**  Maps agreeing on the right factor give equal composite maps
— immediate from the vcomp homomorphism.  This is the case the factorization was named for: the incoming map
post-composes, so replacing the right factor by a map-equal one leaves the composite unchanged. -/
theorem monadMonotoneMapOf_vcompCongrRight {sourceMode targetMode : MonadMode}
    {oneCellF oneCellG oneCellH : ModalityPath monadGraph sourceMode targetMode}
    (cellAlpha : RawTwoCellExpr monadModeSignature oneCellF oneCellG)
    {cellBeta cellBeta' : RawTwoCellExpr monadModeSignature oneCellG oneCellH}
    (hmap : monadMonotoneMapOf cellBeta = monadMonotoneMapOf cellBeta') :
    monadMonotoneMapOf (RawTwoCellExpr.vcomp cellAlpha cellBeta)
      = monadMonotoneMapOf (RawTwoCellExpr.vcomp cellAlpha cellBeta') := by
  rw [monadMonotoneMapOf_vcomp, monadMonotoneMapOf_vcomp, hmap]

/-! ## Honesty marker -/

/-- **ESTABLISHED.**  The map-factorization ENGINE is shipped: the fold lands every free 2-cell in a genuine Δ₊
morphism (`monadRunMonoCell_mapsInto` — every `mu` an INTERNAL degeneracy, the fragment the adjunction's boundary
cap escaped), the map length is fold-invariant (`monadRunMonoCell_map_length`), the incoming map post-composes
(`monadRunMonoCell_mapFactor`), and — the consequence — `monadMonotoneMapOf` is a FUNCTOR on vertical composition
(`monadMonotoneMapOf_vcomp`), discharging the TWO vcomp-congruence cases of `mapEqOfConv`
(`monadMonotoneMapOf_vcompCongrLeft` / `…Right`).  This is the "whisker-shift FACTORIZATION" the
`fxMonad_hasFullMapEqOfConvAndCompleteness` honesty marker named as `mapEqOfConv`'s first ingredient, now
delivered zero-axiom.  The remaining `mapEqOfConv` ingredient (a-i) — the two WHISKER-congruence cases — is now
ALSO shipped in `WalkingMonad/MonadWhiskerEmbedding` (`monadMonotoneMapOf_whiskerLeftCongr` / `_whiskerRightCongr`,
via the ordinal-sum embedding crux `monadRunMonoCell_localEmbed`), so `mapEqOfConv` now needs only the `ofFull`
(Godement) case (a-ii).  `= true`. -/
def fxMonad_hasMapFactorizationAndVcompCongruence : Bool := true


/-! ## The whisker-EMBEDDING fold-support stratum, relocated from `MonadWhiskerEmbedding` -/


/-! ## The embedding-algebra identities (each proved pointwise by `listExtById` + `embedRegionSplit`) -/

/-- The embedding of the IDENTITY local map is the identity — `id_L ⊕ id_M ⊕ id_R = id_{L+M+R}`. -/
theorem embedLocalMap_idMap (leftLen midLen rightLen : Nat) :
    embedLocalMap leftLen midLen rightLen (idMap midLen) = idMap (leftLen + midLen + rightLen) := by
  apply listExtById
  · rw [embedLocalMap_length, idMap_length, idMap_length]
  · intro position hposEmbed
    rw [embedLocalMap_length, idMap_length] at hposEmbed
    have hpos : position < leftLen + midLen + rightLen := hposEmbed
    rw [monotoneMapGet_idMap (leftLen + midLen + rightLen) position hpos]
    rcases embedRegionSplit leftLen midLen rightLen position hpos with hleft | ⟨offset, hoff, rfl⟩ | ⟨offset, hoff, rfl⟩
    · exact embedLocalMap_get_left leftLen midLen rightLen (idMap midLen) position hleft
    · rw [embedLocalMap_get_mid leftLen midLen rightLen (idMap midLen) offset (by rw [idMap_length]; exact hoff),
          monotoneMapGet_idMap midLen offset hoff]
    · have hright := embedLocalMap_get_right leftLen midLen rightLen (idMap midLen) offset hoff
      rw [idMap_length] at hright; exact hright

/-- The FACE decomposition — `δ_L : [L+R] → [L+R+1]` (a `mu`-free `eta` fold from context `L`) is the embedding of
the EMPTY local map: `faceMap L (L+R) = embedLocalMap L 1 R []`. -/
theorem faceMap_eq_embedLocalMap (leftLen rightLen : Nat) :
    faceMap leftLen (leftLen + rightLen) = embedLocalMap leftLen 1 rightLen [] := by
  apply listExtById
  · rw [faceMap_length, embedLocalMap_length]; show leftLen + rightLen = leftLen + 0 + rightLen
    rw [Nat.add_zero]
  · intro position hposFace
    rw [faceMap_length] at hposFace
    have hpos : position < leftLen + 0 + rightLen := by rw [Nat.add_zero]; exact hposFace
    rcases embedRegionSplit leftLen 0 rightLen position hpos with hleft | ⟨offset, hoff, _⟩ | ⟨offset, hoff, rfl⟩
    · show monotoneMapGet (faceFrom 0 leftLen (leftLen + rightLen)) position
        = monotoneMapGet (embedLocalMap leftLen 1 rightLen []) position
      rw [faceFrom_get_lt 0 leftLen (leftLen + rightLen) position hleft hposFace, Nat.zero_add,
          embedLocalMap_get_left leftLen 1 rightLen [] position hleft]
    · exact absurd hoff (Nat.not_lt_zero offset)
    · have hbound : leftLen + 0 + offset < leftLen + rightLen := by
        rw [Nat.add_zero]; exact Nat.add_lt_add_left hoff leftLen
      have hR : monotoneMapGet (embedLocalMap leftLen 1 rightLen []) (leftLen + 0 + offset)
          = leftLen + 1 + offset := embedLocalMap_get_right leftLen 1 rightLen [] offset hoff
      show monotoneMapGet (faceFrom 0 leftLen (leftLen + rightLen)) (leftLen + 0 + offset)
        = monotoneMapGet (embedLocalMap leftLen 1 rightLen []) (leftLen + 0 + offset)
      rw [hR, faceFrom_get_ge 0 leftLen (leftLen + rightLen) (leftLen + 0 + offset)
            (Nat.le_trans (Nat.le_add_right leftLen 0) (Nat.le_add_right (leftLen + 0) offset)) hbound, Nat.zero_add,
          Nat.add_zero]
      show leftLen + offset + 1 = leftLen + 1 + offset
      rw [Nat.add_right_comm]

/-- The DEGENERACY decomposition — `σ_L : [L+2+R] → [L+1+R]` (a `mu` fold from context `L`) is the embedding of
the merge local map `[0, 0]` (the bare `mu`'s map): `degenMap L (L+1+R) = embedLocalMap L 1 R [0, 0]`. -/
theorem degenMap_eq_embedLocalMap (leftLen rightLen : Nat) :
    degenMap leftLen (leftLen + 1 + rightLen) = embedLocalMap leftLen 1 rightLen [0, 0] := by
  have hlenEq : leftLen + 1 + rightLen + 1 = leftLen + 2 + rightLen := by
    rw [Nat.add_right_comm (leftLen + 1) rightLen 1]
  have hLltN : leftLen < leftLen + 1 + rightLen :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self leftLen) (Nat.le_add_right (leftLen + 1) rightLen)
  apply listExtById
  · rw [degenMap_length, embedLocalMap_length]; exact hlenEq
  · intro position hposDegen
    rw [degenMap_length] at hposDegen
    have hpos : position < leftLen + 2 + rightLen := hlenEq ▸ hposDegen
    show monotoneMapGet (degenFrom 0 leftLen (leftLen + 1 + rightLen)) position
      = monotoneMapGet (embedLocalMap leftLen 1 rightLen [0, 0]) position
    rcases embedRegionSplit leftLen 2 rightLen position hpos with hleft | ⟨offset, hoff, rfl⟩ | ⟨offset, hoff, rfl⟩
    · rw [degenFrom_get_le 0 leftLen (leftLen + 1 + rightLen) position (Nat.le_of_lt hleft)
            (Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le hleft (Nat.le_of_lt hLltN))), Nat.zero_add,
          embedLocalMap_get_left leftLen 1 rightLen [0, 0] position hleft]
    · rw [embedLocalMap_get_mid leftLen 1 rightLen [0, 0] offset hoff]
      have hzero : monotoneMapGet [0, 0] offset = 0 := by
        rcases offset with _ | _ | offset''
        · rfl
        · rfl
        · exact absurd hoff (Nat.not_lt.mpr (Nat.le_add_left 2 offset''))
      rw [hzero, Nat.add_zero]
      rcases offset with _ | _ | offset''
      · show monotoneMapGet (degenFrom 0 leftLen (leftLen + 1 + rightLen)) leftLen = leftLen
        rw [degenFrom_get_le 0 leftLen (leftLen + 1 + rightLen) leftLen (Nat.le_refl _)
              (Nat.lt_succ_of_lt hLltN), Nat.zero_add]
      · show monotoneMapGet (degenFrom 0 leftLen (leftLen + 1 + rightLen)) (leftLen + 1) = leftLen
        rw [degenFrom_get_succ 0 leftLen (leftLen + 1 + rightLen) leftLen (Nat.le_refl _) hLltN, Nat.zero_add]
      · exact absurd hoff (Nat.not_lt.mpr (Nat.le_add_left 2 offset''))
    · have hR : monotoneMapGet (embedLocalMap leftLen 1 rightLen [0, 0]) (leftLen + 2 + offset)
          = leftLen + 1 + offset := embedLocalMap_get_right leftLen 1 rightLen [0, 0] offset hoff
      rw [hR]
      show monotoneMapGet (degenFrom 0 leftLen (leftLen + 1 + rightLen)) (leftLen + 2 + offset)
        = leftLen + 1 + offset
      have hposEq : leftLen + 2 + offset = (leftLen + 1 + offset) + 1 := by
        rw [Nat.add_right_comm (leftLen + 1) offset 1]
      rw [hposEq, degenFrom_get_succ 0 leftLen (leftLen + 1 + rightLen) (leftLen + 1 + offset)
            (Nat.le_trans (Nat.le_add_right leftLen 1) (Nat.le_add_right (leftLen + 1) offset))
            (by rw [Nat.add_assoc leftLen 1 rightLen, Nat.add_assoc leftLen 1 offset];
                exact Nat.add_lt_add_left (Nat.add_lt_add_left hoff 1) leftLen), Nat.zero_add]

/-- ★ **Composition-functoriality of the embedding** (the `vcomp` case).  Embedding a `composeMap` is the
`composeMap` of the embeddings — `id_L ⊕ (g∘f) ⊕ id_R = (id_L ⊕ g ⊕ id_R) ∘ (id_L ⊕ f ⊕ id_R)` — when `f` lands
in `g`'s domain.  Proved pointwise by `listExtById` + `embedRegionSplit`. -/
theorem embedLocalMap_composeMap (leftLen rightLen midLen : Nat) (first second : List Nat)
    (hrange : mapsInto first second.length) :
    embedLocalMap leftLen midLen rightLen (composeMap first second)
      = composeMap (embedLocalMap leftLen second.length rightLen first)
          (embedLocalMap leftLen midLen rightLen second) := by
  apply listExtById
  · rw [embedLocalMap_length, composeMap_length, composeMap_length, embedLocalMap_length]
  · intro position hposEmbed
    rw [embedLocalMap_length, composeMap_length] at hposEmbed
    have hpos : position < leftLen + first.length + rightLen := hposEmbed
    have hposFirst : position < (embedLocalMap leftLen second.length rightLen first).length := by
      rw [embedLocalMap_length]; exact hpos
    rw [composeMap_get (embedLocalMap leftLen second.length rightLen first)
          (embedLocalMap leftLen midLen rightLen second) position hposFirst]
    rcases embedRegionSplit leftLen first.length rightLen position hpos with hleft | ⟨offset, hoff, rfl⟩ | ⟨offset, hoff, rfl⟩
    · rw [embedLocalMap_get_left leftLen midLen rightLen (composeMap first second) position hleft,
          embedLocalMap_get_left leftLen second.length rightLen first position hleft,
          embedLocalMap_get_left leftLen midLen rightLen second position hleft]
    · rw [embedLocalMap_get_mid leftLen midLen rightLen (composeMap first second) offset
            (by rw [composeMap_length]; exact hoff),
          composeMap_get first second offset hoff,
          embedLocalMap_get_mid leftLen second.length rightLen first offset hoff,
          embedLocalMap_get_mid leftLen midLen rightLen second (monotoneMapGet first offset) (hrange offset hoff)]
    · have hL : monotoneMapGet (embedLocalMap leftLen midLen rightLen (composeMap first second))
          (leftLen + first.length + offset) = leftLen + midLen + offset := by
        rw [← composeMap_length first second]
        exact embedLocalMap_get_right leftLen midLen rightLen (composeMap first second) offset hoff
      rw [hL, embedLocalMap_get_right leftLen second.length rightLen first offset hoff,
          embedLocalMap_get_right leftLen midLen rightLen second offset hoff]

/-- ★ **Nesting-associativity of the embedding** (the whisker case).  Embedding an already-embedded map by an
OUTER context is embedding the innermost map by the COMBINED context: the ordinal sums associate.  Both whisker
cases instantiate it (left whisker with `rightInner = 0`, right whisker with `leftInner = 0`).  Proved pointwise
by nested `embedRegionSplit`. -/
theorem embedLocalMap_nest (leftOuter leftInner midInner rightInner rightOuter : Nat) (inner : List Nat) :
    embedLocalMap leftOuter (leftInner + midInner + rightInner) rightOuter
        (embedLocalMap leftInner midInner rightInner inner)
      = embedLocalMap (leftOuter + leftInner) midInner (rightInner + rightOuter) inner := by
  have hInnerLen : (embedLocalMap leftInner midInner rightInner inner).length
      = leftInner + inner.length + rightInner := embedLocalMap_length leftInner midInner rightInner inner
  apply listExtById
  · rw [embedLocalMap_length, embedLocalMap_length, embedLocalMap_length,
        ← Nat.add_assoc leftOuter (leftInner + inner.length) rightInner,
        ← Nat.add_assoc leftOuter leftInner inner.length,
        Nat.add_assoc (leftOuter + leftInner + inner.length) rightInner rightOuter]
  · intro position hposEmbed
    rw [embedLocalMap_length, hInnerLen] at hposEmbed
    have hposL : position < leftOuter + (leftInner + inner.length + rightInner) + rightOuter := hposEmbed
    rcases embedRegionSplit leftOuter (leftInner + inner.length + rightInner) rightOuter position hposL with
        hL1 | ⟨middleOffset, hmidO, rfl⟩ | ⟨rightO, hrightO, rfl⟩
    · -- LEFT of the outer prefix
      rw [embedLocalMap_get_left leftOuter (leftInner + midInner + rightInner) rightOuter
            (embedLocalMap leftInner midInner rightInner inner) position hL1,
          embedLocalMap_get_left (leftOuter + leftInner) midInner (rightInner + rightOuter) inner position
            (Nat.lt_of_lt_of_le hL1 (Nat.le_add_right leftOuter leftInner))]
    · -- MIDDLE: inside the inner embedding — sub-split by the inner regions
      have hmidOlen : middleOffset < (embedLocalMap leftInner midInner rightInner inner).length :=
        hInnerLen.symm ▸ hmidO
      rw [embedLocalMap_get_mid leftOuter (leftInner + midInner + rightInner) rightOuter
            (embedLocalMap leftInner midInner rightInner inner) middleOffset hmidOlen]
      rcases embedRegionSplit leftInner inner.length rightInner middleOffset hmidO with
          hiL | ⟨j, hj, rfl⟩ | ⟨k, hk, rfl⟩
      · -- inner LEFT: middleOffset < leftInner ; both are the identity value  leftOuter + middleOffset
        rw [embedLocalMap_get_left leftInner midInner rightInner inner middleOffset hiL,
            embedLocalMap_get_left (leftOuter + leftInner) midInner (rightInner + rightOuter) inner
              (leftOuter + middleOffset) (Nat.add_lt_add_left hiL leftOuter)]
      · -- inner MIDDLE: middleOffset = leftInner + j, j < inner.length
        rw [embedLocalMap_get_mid leftInner midInner rightInner inner j hj,
            show leftOuter + (leftInner + j) = (leftOuter + leftInner) + j from
              (Nat.add_assoc leftOuter leftInner j).symm,
            embedLocalMap_get_mid (leftOuter + leftInner) midInner (rightInner + rightOuter) inner j hj,
            Nat.add_assoc leftOuter leftInner (monotoneMapGet inner j)]
      · -- inner RIGHT: middleOffset = leftInner + inner.length + k, k < rightInner
        rw [embedLocalMap_get_right leftInner midInner rightInner inner k hk]
        have hposEq : leftOuter + (leftInner + inner.length + k)
            = (leftOuter + leftInner) + inner.length + k := by
          rw [← Nat.add_assoc leftOuter (leftInner + inner.length) k,
              ← Nat.add_assoc leftOuter leftInner inner.length]
        rw [hposEq, embedLocalMap_get_right (leftOuter + leftInner) midInner (rightInner + rightOuter) inner k
              (Nat.lt_of_lt_of_le hk (Nat.le_add_right rightInner rightOuter)),
            ← Nat.add_assoc leftOuter (leftInner + midInner) k, ← Nat.add_assoc leftOuter leftInner midInner]
    · -- RIGHT of the outer suffix: position = leftOuter + innerLen + rightO
      have hL : monotoneMapGet (embedLocalMap leftOuter (leftInner + midInner + rightInner) rightOuter
            (embedLocalMap leftInner midInner rightInner inner))
            (leftOuter + (leftInner + inner.length + rightInner) + rightO)
          = leftOuter + (leftInner + midInner + rightInner) + rightO := by
        rw [← hInnerLen]
        exact embedLocalMap_get_right leftOuter (leftInner + midInner + rightInner) rightOuter
          (embedLocalMap leftInner midInner rightInner inner) rightO hrightO
      rw [hL]
      have hposEq : leftOuter + (leftInner + inner.length + rightInner) + rightO
          = (leftOuter + leftInner) + inner.length + (rightInner + rightO) := by
        rw [← Nat.add_assoc leftOuter (leftInner + inner.length) rightInner,
            ← Nat.add_assoc leftOuter leftInner inner.length,
            Nat.add_assoc (leftOuter + leftInner + inner.length) rightInner rightO]
      rw [hposEq, embedLocalMap_get_right (leftOuter + leftInner) midInner (rightInner + rightOuter) inner
            (rightInner + rightO) (Nat.add_lt_add_left hrightO rightInner),
          ← Nat.add_assoc leftOuter (leftInner + midInner) rightInner,
          ← Nat.add_assoc leftOuter leftInner midInner,
          Nat.add_assoc (leftOuter + leftInner + midInner) rightInner rightO]

/-! ## The whole-cell map length + codomain (the vcomp side conditions) -/

/-- The whole-cell monotone map has the source 1-cell's length as its domain. -/
theorem monadMonotoneMapOf_length {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadModeSignature.graph sourceMode targetMode}
    (cell : RawTwoCellExpr monadModeSignature sourcePath targetPath) :
    (monadMonotoneMapOf cell).length = sourcePath.length := by
  rw [monadMonotoneMapOf_eq_runMonoCell,
      monadRunMonoCell_map_length cell (sourcePath.length, idMap sourcePath.length)
        (identityPath (graph := monadModeSignature.graph) sourceMode) (identityPath (graph := monadModeSignature.graph) targetMode)]
  exact idMap_length sourcePath.length

/-- The whole-cell monotone map lands in the target 1-cell's length (a genuine Δ₊ codomain). -/
theorem monadMonotoneMapOf_mapsInto {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadModeSignature.graph sourceMode targetMode}
    (cell : RawTwoCellExpr monadModeSignature sourcePath targetPath) :
    mapsInto (monadMonotoneMapOf cell) targetPath.length := by
  have hwidth : sourcePath.length
      = (identityPath (graph := monadModeSignature.graph) sourceMode).length + sourcePath.length + (identityPath (graph := monadModeSignature.graph) targetMode).length := by
    show sourcePath.length = 0 + sourcePath.length + 0
    rw [Nat.add_zero, Nat.zero_add]
  have hmaps := monadRunMonoCell_mapsInto cell sourcePath.length (idMap sourcePath.length)
    (identityPath (graph := monadModeSignature.graph) sourceMode) (identityPath (graph := monadModeSignature.graph) targetMode) hwidth (idMap_mapsInto sourcePath.length)
  have hw1 : (monadRunMonoCell (sourcePath.length, idMap sourcePath.length)
      (identityPath (graph := monadModeSignature.graph) sourceMode) (identityPath (graph := monadModeSignature.graph) targetMode) cell).1 = targetPath.length := by
    rw [monadRunMonoCell_width cell sourcePath.length (idMap sourcePath.length)
          (identityPath (graph := monadModeSignature.graph) sourceMode) (identityPath (graph := monadModeSignature.graph) targetMode) hwidth]
    show 0 + targetPath.length + 0 = targetPath.length
    rw [Nat.add_zero, Nat.zero_add]
  rw [hw1] at hmaps
  rw [monadMonotoneMapOf_eq_runMonoCell]
  exact hmaps

/-! ## The generator embed case -/

/-- The generator case of the embedding lemma — `eta` folds to the FACE decomposition of the empty map, `mu` to
the DEGENERACY decomposition of `[0, 0]`.  Split off with FREE boundary paths so casing on the generator is
propext-free. -/
theorem monadRunMonoCell_localEmbed_gen {overallSource overallTarget sourceMode targetMode : MonadMode}
    {generatorDom generatorCod : ModalityPath monadModeSignature.graph sourceMode targetMode}
    (generator : MonadTwoCell generatorDom generatorCod)
    (leftAcc : ModalityPath monadModeSignature.graph overallSource sourceMode)
    (rightAcc : ModalityPath monadModeSignature.graph targetMode overallTarget) :
    (monadRunMonoCell (leftAcc.length + generatorDom.length + rightAcc.length,
        idMap (leftAcc.length + generatorDom.length + rightAcc.length)) leftAcc rightAcc
        (RawTwoCellExpr.gen generator)).2
      = embedLocalMap leftAcc.length generatorCod.length rightAcc.length
          (monadMonotoneMapOf (RawTwoCellExpr.gen generator)) := by
  cases generator with
  | eta =>
      show composeMap (idMap (leftAcc.length + 0 + rightAcc.length))
          (faceMap leftAcc.length (leftAcc.length + 0 + rightAcc.length))
        = embedLocalMap leftAcc.length 1 rightAcc.length []
      have hstep : composeMap (idMap (leftAcc.length + 0 + rightAcc.length))
          (faceMap leftAcc.length (leftAcc.length + 0 + rightAcc.length))
          = faceMap leftAcc.length (leftAcc.length + 0 + rightAcc.length) := by
        have hc := composeMap_idMap_eq (faceMap leftAcc.length (leftAcc.length + 0 + rightAcc.length))
        rw [faceMap_length leftAcc.length (leftAcc.length + 0 + rightAcc.length)] at hc
        exact hc
      rw [hstep]
      show faceMap leftAcc.length (leftAcc.length + rightAcc.length) = embedLocalMap leftAcc.length 1 rightAcc.length []
      exact faceMap_eq_embedLocalMap leftAcc.length rightAcc.length
  | mu =>
      show composeMap (idMap (leftAcc.length + 2 + rightAcc.length))
          (degenMap leftAcc.length (leftAcc.length + 2 + rightAcc.length - 1))
        = embedLocalMap leftAcc.length 1 rightAcc.length [0, 0]
      rw [monadMuWidthShift leftAcc.length rightAcc.length]
      have hstep : composeMap (idMap (leftAcc.length + 2 + rightAcc.length))
          (degenMap leftAcc.length (leftAcc.length + 1 + rightAcc.length))
          = degenMap leftAcc.length (leftAcc.length + 1 + rightAcc.length) := by
        have hc := composeMap_idMap_eq (degenMap leftAcc.length (leftAcc.length + 1 + rightAcc.length))
        rw [degenMap_length leftAcc.length (leftAcc.length + 1 + rightAcc.length),
            show leftAcc.length + 1 + rightAcc.length + 1 = leftAcc.length + 2 + rightAcc.length from by
              rw [Nat.add_right_comm (leftAcc.length + 1) rightAcc.length 1]] at hc
        exact hc
      rw [hstep]
      exact degenMap_eq_embedLocalMap leftAcc.length rightAcc.length

/-! ## The crux: the fold run at any context is the ordinal-sum embedding of the cell's local map -/

/-- ★ **The whisker-embedding crux.**  Running the monotone fold over a free 2-cell from the identity state at
accumulators `leftAcc / rightAcc` yields the ORDINAL-SUM EMBEDDING of the cell's LOCAL map (`monadMonotoneMapOf`)
into the `leftAcc.length`-prefixed, `rightAcc.length`-suffixed context.  Structural induction: generators are the
face / degeneracy decompositions, `vcomp` is composition-functoriality (`embedLocalMap_composeMap`), the
whiskerings are nesting-associativity (`embedLocalMap_nest`) — the ordinal-sum functor `W ⊗ -` on Δ₊. -/
theorem monadRunMonoCell_localEmbed {overallSource overallTarget : MonadMode} :
    {localSource localTarget : MonadMode} →
    {localDom localCod : ModalityPath monadModeSignature.graph localSource localTarget} →
    (cell : RawTwoCellExpr monadModeSignature localDom localCod) →
    (width : Nat) →
    (leftAcc : ModalityPath monadModeSignature.graph overallSource localSource) →
    (rightAcc : ModalityPath monadModeSignature.graph localTarget overallTarget) →
    width = leftAcc.length + localDom.length + rightAcc.length →
    (monadRunMonoCell (width, idMap width) leftAcc rightAcc cell).2
      = embedLocalMap leftAcc.length localCod.length rightAcc.length (monadMonotoneMapOf cell)
  | _, _, _, _, .gen generator, width, leftAcc, rightAcc, hw => by
      subst hw
      exact monadRunMonoCell_localEmbed_gen generator leftAcc rightAcc
  | _, _, _, _, .id path, width, leftAcc, rightAcc, hw => by
      subst hw
      show idMap (leftAcc.length + path.length + rightAcc.length)
        = embedLocalMap leftAcc.length path.length rightAcc.length (monadMonotoneMapOf (RawTwoCellExpr.id path))
      rw [show monadMonotoneMapOf (RawTwoCellExpr.id path) = idMap path.length from rfl, embedLocalMap_idMap]
  | _, _, _, oneCellH, .vcomp cellLeft cellRight, width, leftAcc, rightAcc, hw => by
      have hrange : mapsInto (monadMonotoneMapOf cellLeft) (monadMonotoneMapOf cellRight).length := by
        rw [monadMonotoneMapOf_length cellRight]; exact monadMonotoneMapOf_mapsInto cellLeft
      rw [monadRunMonoCell_vcomp_map cellLeft cellRight (width, idMap width) leftAcc rightAcc hw
            (idMap_mapsInto width),
          monadRunMonoCell_localEmbed cellLeft width leftAcc rightAcc hw,
          monadRunMonoCell_localEmbed cellRight
            (monadRunMonoCell (width, idMap width) leftAcc rightAcc cellLeft).1 leftAcc rightAcc
            (monadRunMonoCell_width cellLeft width (idMap width) leftAcc rightAcc hw),
          monadMonotoneMapOf_vcomp cellLeft cellRight,
          embedLocalMap_composeMap leftAcc.length rightAcc.length oneCellH.length
            (monadMonotoneMapOf cellLeft) (monadMonotoneMapOf cellRight) hrange,
          monadMonotoneMapOf_length cellRight]
  | _, _, _, _, .whiskerLeft oneCell body, width, leftAcc, rightAcc, hw => by
      rename_i sourceMode targetMode middleMode oneCellG oneCellH
      have hwBody : width = (composePath leftAcc oneCell).length + oneCellG.length + rightAcc.length := by
        rw [hw, ModalityPath.length_composePath oneCell oneCellG, ModalityPath.length_composePath leftAcc oneCell,
            Nat.add_assoc leftAcc.length oneCell.length oneCellG.length]
      have hMap : monadMonotoneMapOf (RawTwoCellExpr.whiskerLeft oneCell body)
          = embedLocalMap oneCell.length oneCellH.length 0 (monadMonotoneMapOf body) := by
        have hwMap : (composePath oneCell oneCellG).length = oneCell.length + oneCellG.length
            + (identityPath (graph := monadModeSignature.graph) targetMode).length := by
          show (composePath oneCell oneCellG).length = oneCell.length + oneCellG.length + 0
          rw [ModalityPath.length_composePath oneCell oneCellG, Nat.add_zero]
        rw [monadMonotoneMapOf_eq_runMonoCell (RawTwoCellExpr.whiskerLeft oneCell body),
            monadRunMonoCell_whiskerLeft, composePath_identityPath_left]
        exact monadRunMonoCell_localEmbed body (composePath oneCell oneCellG).length oneCell
          (identityPath (graph := monadModeSignature.graph) targetMode) hwMap
      rw [monadRunMonoCell_whiskerLeft,
          monadRunMonoCell_localEmbed body width (composePath leftAcc oneCell) rightAcc hwBody,
          ModalityPath.length_composePath leftAcc oneCell, hMap,
          ModalityPath.length_composePath oneCell oneCellH]
      have hnest := embedLocalMap_nest leftAcc.length oneCell.length oneCellH.length 0 rightAcc.length
        (monadMonotoneMapOf body)
      rw [Nat.add_zero, Nat.zero_add] at hnest
      exact hnest.symm
  | _, _, _, _, .whiskerRight oneCell body, width, leftAcc, rightAcc, hw => by
      rename_i sourceMode targetMode middleMode oneCellF oneCellG
      have hwBody : width = leftAcc.length + oneCellF.length + (composePath oneCell rightAcc).length := by
        rw [hw, ModalityPath.length_composePath oneCellF oneCell, ModalityPath.length_composePath oneCell rightAcc,
            ← Nat.add_assoc leftAcc.length oneCellF.length oneCell.length,
            Nat.add_assoc (leftAcc.length + oneCellF.length) oneCell.length rightAcc.length]
      have hMap : monadMonotoneMapOf (RawTwoCellExpr.whiskerRight oneCell body)
          = embedLocalMap 0 oneCellG.length oneCell.length (monadMonotoneMapOf body) := by
        have hwMap : (composePath oneCellF oneCell).length
            = (identityPath (graph := monadModeSignature.graph) sourceMode).length + oneCellF.length
              + (composePath oneCell (identityPath (graph := monadModeSignature.graph) targetMode)).length := by
          rw [ModalityPath.length_composePath oneCellF oneCell,
              ModalityPath.length_composePath oneCell (identityPath (graph := monadModeSignature.graph) targetMode)]
          show oneCellF.length + oneCell.length = 0 + oneCellF.length + (oneCell.length + 0)
          rw [Nat.zero_add, Nat.add_zero]
        rw [monadMonotoneMapOf_eq_runMonoCell (RawTwoCellExpr.whiskerRight oneCell body),
            monadRunMonoCell_whiskerRight]
        have hkey := monadRunMonoCell_localEmbed body (composePath oneCellF oneCell).length
          (identityPath (graph := monadModeSignature.graph) sourceMode)
          (composePath oneCell (identityPath (graph := monadModeSignature.graph) targetMode)) hwMap
        rw [ModalityPath.length_composePath oneCell
              (identityPath (graph := monadModeSignature.graph) targetMode)] at hkey
        exact hkey
      rw [monadRunMonoCell_whiskerRight,
          monadRunMonoCell_localEmbed body width leftAcc (composePath oneCell rightAcc) hwBody,
          ModalityPath.length_composePath oneCell rightAcc, hMap,
          ModalityPath.length_composePath oneCellG oneCell]
      have hnest := embedLocalMap_nest leftAcc.length 0 oneCellG.length oneCell.length rightAcc.length
        (monadMonotoneMapOf body)
      rw [Nat.add_zero, Nat.zero_add] at hnest
      exact hnest.symm

/-! ## The top-level whisker embeddings + the two WHISKER-congruence cases of `mapEqOfConv` -/

/-- ★ **The LEFT-whisker embedding.**  `monadMonotoneMapOf (whiskerLeft W body)` is the ordinal sum `id_[W] ⊕ (map
body)` — the whole-cell instance of the crux at `leftAcc = W`, `rightAcc = identity`. -/
theorem monadMonotoneMapOf_whiskerLeft {sourceMode middleMode targetMode : MonadMode}
    (oneCell : ModalityPath monadModeSignature.graph sourceMode middleMode)
    {oneCellG oneCellH : ModalityPath monadModeSignature.graph middleMode targetMode}
    (body : RawTwoCellExpr monadModeSignature oneCellG oneCellH) :
    monadMonotoneMapOf (RawTwoCellExpr.whiskerLeft oneCell body)
      = embedLocalMap oneCell.length oneCellH.length 0 (monadMonotoneMapOf body) := by
  have hwMap : (composePath oneCell oneCellG).length = oneCell.length + oneCellG.length
      + (identityPath (graph := monadModeSignature.graph) targetMode).length := by
    show (composePath oneCell oneCellG).length = oneCell.length + oneCellG.length + 0
    rw [ModalityPath.length_composePath oneCell oneCellG, Nat.add_zero]
  rw [monadMonotoneMapOf_eq_runMonoCell (RawTwoCellExpr.whiskerLeft oneCell body),
      monadRunMonoCell_whiskerLeft, composePath_identityPath_left]
  exact monadRunMonoCell_localEmbed body (composePath oneCell oneCellG).length oneCell
    (identityPath (graph := monadModeSignature.graph) targetMode) hwMap

/-- ★ **The RIGHT-whisker embedding.**  `monadMonotoneMapOf (whiskerRight W body)` is the ordinal sum `(map body) ⊕
id_[W]` — the whole-cell instance of the crux at `leftAcc = identity`, `rightAcc = W`. -/
theorem monadMonotoneMapOf_whiskerRight {sourceMode middleMode targetMode : MonadMode}
    {oneCellF oneCellG : ModalityPath monadModeSignature.graph sourceMode middleMode}
    (oneCell : ModalityPath monadModeSignature.graph middleMode targetMode)
    (body : RawTwoCellExpr monadModeSignature oneCellF oneCellG) :
    monadMonotoneMapOf (RawTwoCellExpr.whiskerRight oneCell body)
      = embedLocalMap 0 oneCellG.length oneCell.length (monadMonotoneMapOf body) := by
  have hwMap : (composePath oneCellF oneCell).length
      = (identityPath (graph := monadModeSignature.graph) sourceMode).length + oneCellF.length
        + (composePath oneCell (identityPath (graph := monadModeSignature.graph) targetMode)).length := by
    rw [ModalityPath.length_composePath oneCellF oneCell,
        ModalityPath.length_composePath oneCell (identityPath (graph := monadModeSignature.graph) targetMode)]
    show oneCellF.length + oneCell.length = 0 + oneCellF.length + (oneCell.length + 0)
    rw [Nat.zero_add, Nat.add_zero]
  rw [monadMonotoneMapOf_eq_runMonoCell (RawTwoCellExpr.whiskerRight oneCell body),
      monadRunMonoCell_whiskerRight]
  have hkey := monadRunMonoCell_localEmbed body (composePath oneCellF oneCell).length
    (identityPath (graph := monadModeSignature.graph) sourceMode)
    (composePath oneCell (identityPath (graph := monadModeSignature.graph) targetMode)) hwMap
  rw [ModalityPath.length_composePath oneCell
        (identityPath (graph := monadModeSignature.graph) targetMode)] at hkey
  exact hkey

/-- ★ **`mapEqOfConv`, LEFT-whisker-congruence case.**  Body maps agreeing give equal whiskered maps — a `congrArg`
of the left-whisker embedding. -/
theorem monadMonotoneMapOf_whiskerLeftCongr {sourceMode middleMode targetMode : MonadMode}
    (oneCell : ModalityPath monadModeSignature.graph sourceMode middleMode)
    {oneCellG oneCellH : ModalityPath monadModeSignature.graph middleMode targetMode}
    {body body' : RawTwoCellExpr monadModeSignature oneCellG oneCellH}
    (hmap : monadMonotoneMapOf body = monadMonotoneMapOf body') :
    monadMonotoneMapOf (RawTwoCellExpr.whiskerLeft oneCell body)
      = monadMonotoneMapOf (RawTwoCellExpr.whiskerLeft oneCell body') := by
  rw [monadMonotoneMapOf_whiskerLeft, monadMonotoneMapOf_whiskerLeft, hmap]

/-- ★ **`mapEqOfConv`, RIGHT-whisker-congruence case.**  Body maps agreeing give equal whiskered maps — a
`congrArg` of the right-whisker embedding. -/
theorem monadMonotoneMapOf_whiskerRightCongr {sourceMode middleMode targetMode : MonadMode}
    {oneCellF oneCellG : ModalityPath monadModeSignature.graph sourceMode middleMode}
    (oneCell : ModalityPath monadModeSignature.graph middleMode targetMode)
    {body body' : RawTwoCellExpr monadModeSignature oneCellF oneCellG}
    (hmap : monadMonotoneMapOf body = monadMonotoneMapOf body') :
    monadMonotoneMapOf (RawTwoCellExpr.whiskerRight oneCell body)
      = monadMonotoneMapOf (RawTwoCellExpr.whiskerRight oneCell body') := by
  rw [monadMonotoneMapOf_whiskerRight, monadMonotoneMapOf_whiskerRight, hmap]

/-! ## Honesty marker -/

/-- **ESTABLISHED.**  The WHISKER-EMBEDDING is shipped: the fold of a whiskered free 2-cell run at any context is
the ORDINAL-SUM embedding of the cell's local map (`monadRunMonoCell_localEmbed`), so the two top-level whiskerings
embed the body's map (`monadMonotoneMapOf_whiskerLeft` / `_whiskerRight`), discharging the two WHISKER-congruence
cases of `mapEqOfConv` (`monadMonotoneMapOf_whiskerLeftCongr` / `_whiskerRightCongr`), zero-axiom.  Combined with
the shipped vcomp-congruence and the three law legs, `mapEqOfConv` now needs ONLY the `ofFull` (Godement /
interchange) case — the disjoint-window two-block commute, cap-free hence unconditional on Δ.  `= true`. -/
def fxMonad_hasWhiskerEmbeddingAndCongruence : Bool := true


end FX1Poly.Polygraph
