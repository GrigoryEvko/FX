import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadDeltaModel

/-! # WalkingMonad — the monotone-fold ENGINE: block/offset threading for the covariant Δ₊ fold

`WalkingMonad/MonadDeltaModel` ships the retuned fold `monadMonotoneMapOf` (eta ↦ face, mu ↦ degeneracy, width =
path LENGTH) with the three monad-law soundness legs at the SEED and at one whiskered width.  This file builds the
**fold-decomposition engine** the arbitrary-context soundness leg (`mapEqOfConv`) needs — the monad twin of the
walking-adjunction's `runMonoCell` block algebra (`WalkingAdjunction/MonotoneMap`), but STRICTLY SIMPLER:

  * the width is the plain path LENGTH, not `blockOf` — no `±2`-block arithmetic, no truncated-subtraction
    underflow (each eta is `+1`, each mu is `-1` on the length, and the source has `≥ 2` t's whenever a mu fires),
  * there is ONE variance, so the covariant fold IS the sound carrier (`covariantMonotoneMapOf_notSound` refuted
    it for the adjunction; it holds here).

## What this file ships (each piece zero-axiom)

  * **`monadMonoProcessSpine` / `monadRunMonoCell`** — the spine-list fold engine and the per-cell fold unit.
  * **`monadMonoProcessSpine_spineDiff`** — the fold-decomposition: folding over `cell.spineDiff` equals running
    the cell alone then the tail (structural recursion; whiskerings recurse under shifted accumulators).
  * **`monadRunMonoCell_vcomp` / `_whiskerLeft` / `_whiskerRight` / `_rightContext_irrelevant`** — the peel /
    shift / irrelevance laws (the whiskerings are `rfl`; right-context irrelevance drops half the Godement shift).
  * ★ **`monadRunMonoCell_width`** — the **length-width invariant**: the running width tracks the current 1-cell
    LENGTH `leftAcc · dom · rightAcc → leftAcc · cod · rightAcc` through every step.  Cleaner than the adjunction's
    `blockOf` invariant — no block halving, no underflow side-condition.
  * ★ **the three monad laws GENUINELY at an ARBITRARY left-whisker context** — `whiskerLeft W (leftUnit)`,
    `whiskerLeft W (rightUnit)`, `whiskerLeft W (assoc)` fold equal at EVERY whisker `W`, via the shipped ∀-general
    simplicial / commutation identities at the SHIFTED position `W.length` and width `W.length + k`.  This is the
    headline "strictly easier than the adjunction": the law at context is the SAME shipped lemma at shifted
    arguments — no variance apparatus, because there is one variance.
  * **non-vacuity witnesses** — a parallel pair the fold SEPARATES (`id` vs `mu ∘ (t ◁ eta)` on `t·t ⇒ t·t`, maps
    `[0,1] ≠ [1,1]`) and a parallel pair it IDENTIFIES (the law-equal `leftUnit ≈ id_t`, both `[0]`).

Raw Lean 4 + Init; `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.  Per-declaration
`#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph

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
has FOUR of five cases closed plus the `vcomp` case's 2-cell half — the VERTICAL word multiplicativity
`wordMul_vcomp` (`WalkingMonad/MonadWordVcomp`, `fxMonad_hasVcompWordMultiplicativity`, zero-axiom, via the
`wordMul_hcomp` block split + free interchange + `wordGadgetCollapse` per-block merge).  The SOLE remaining residual
is the DATA bridge `canonCounts (vcomp) = composeCounts (canonCounts, canonCounts)` (`countsOf ∘ composeMap =
composeCounts ∘ countsOf`), the analog of the shipped whisker bridges `canonCounts_whiskerLeft/Right`, whose
base-shifted induction (leading-run head, mid-suffix-shift tail) is the named residual.  So
`MonadSaturatedCanonicalization` is NOT yet inhabited and `fxMonad_hasMonotoneMapDecisionAssembled` stays `false`.
This flag (mapEqOfConv AND completeness) stays `false` because completeness is still owed; the mapEqOfConv half is
marked complete by `fxMonad_hasMapEqOfConvComplete = true`.  `= false`. -/
def fxMonad_hasFullMapEqOfConvAndCompleteness : Bool := false

end FX1Poly.Polygraph
