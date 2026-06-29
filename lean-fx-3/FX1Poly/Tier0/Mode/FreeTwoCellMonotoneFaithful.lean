import FX1Poly.Tier0.Mode.FreeTwoCellMonotoneMap

/-! # mode-9 keystone (YES-direction) — the Eilenberg–Zilber STAIRCASE: realizing a monotone map as a 2-cell

`FreeTwoCellMonotoneMap` ships the Schanuel–Street monotone-map MODEL (`monotoneMapOf` : free 2-cell → `List Nat`)
and the SOUNDNESS / refutation half (distinct maps ⟹ not saturated-convertible, modulo the Godement residual).
This file is the CONVERSE — the **reconstruction**: read a monotone map back as a canonical 2-cell (the
Eilenberg–Zilber degeneracies-then-faces STAIRCASE) and show every cell with that map converts to it.

## The setting (honest scoping)

The clean, variance-uniform hom-category of the seed walking adjunction is `base ⟶ base`.  Every such 1-cell is
forced to alternate `left · right · left · right · …`, so it IS the canonical word `(L·R)^width = leftRightPow
width` of block-width `width`; the keystone there is exactly `Adj(+,+)|_{base} ≅ Δ₊` with NO variance flip (the
`Adj(−,−) ≅ Δ₊^op` flip only bites at mode `tip`, which this file does not touch).  We build the EZ staircase in
this hom-category.

## What this file ships (each piece zero-axiom)

  * **`leftRightPow`** + its arithmetic (`blockOf_leftRightPow` : the canonical width-`w` word has block-width
    `w`; `leftRightPow_add` : the words compose additively).  These pin the source/target ordinals of a staircase.
  * ★ **`canonicalFaceStep` / `canonicalDegenStep`** — the EZ staircase STEPS: a single cup (unit) / cap (counit)
    whiskered to block position `leftBlocks` at total width `leftBlocks + rightBlocks` (+1 for the cap), with the
    boundary cast to clean `leftRightPow` words.  Their **REALIZATION** (`monotoneMapOf_canonicalFaceStep` :
    `monotoneMapOf (canonicalFaceStep …) = faceMap …`; `…DegenStep` : `… = degenMap …`) is the genuine
    "the map directly gives the staircase step" content — proved by computing the `runMonoCell` fold, with no
    node-id / union-find blindness.
  * **`canonicalIdentityCell`** + its realization (`monotoneMapOf_canonicalIdentityCell = idMap width`).

  * the **reconstruction RESIDUAL** named precisely (`StaircaseReconstructs`) and the **corollary skeleton**:
    given the residual (every cell converts to the canonical staircase of its own map), equal monotone maps give
    saturated convertibility — the shape of `AdjunctionSaturatedCanonicalization.convOfMapEq`.

## The relation: `SaturatedTwoCellConv`, not bare `TwoCellConvFull`

`monotoneMapOf` COLLAPSES the snake (the simplicial identity `σ_i ∘ δ_i = id`), which is sound ONLY where the
adjunction TRIANGLE identities hold — i.e. for `SaturatedTwoCellConv` (`= TwoCellConvFull` + the two triangles),
NOT for the bare free `TwoCellConvFull` (where unit/counit are free generators with no triangle relation, so the
snake is provably NOT convertible to the identity — `adjunctionSeedLeftSnake_not_conv_id`).  Hence the
reconstruction's target — and the keystone `convOfMapEq` — is `SaturatedTwoCellConv`.

Raw Lean 4 + Init; every declaration `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Tier0

/-! ## The canonical width-`w` word `(L·R)^w` at mode `base` and its block-width arithmetic -/

/-- The canonical block-width-`width` 1-cell of the seed adjunction at mode `base`: the alternating word
`(left · right)^width`.  Every `base ⟶ base` 1-cell is forced to this shape, so it is the canonical ordinal the
monotone-map model's source / target widths name. -/
def leftRightPow : Nat → ModalityPath adjunctionGraph AdjunctionMode.base AdjunctionMode.base
  | 0 => ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base
  | width + 1 => composePath adjunctionLeftThenRight (leftRightPow width)

/-- One more `L·R` block adds two to the word length. -/
theorem leftRightPow_length_succ (width : Nat) :
    (leftRightPow (width + 1)).length = (leftRightPow width).length + 2 := by
  simp only [leftRightPow]
  rw [ModalityPath.length_composePath]
  exact Nat.add_comm adjunctionLeftThenRight.length (leftRightPow width).length

/-- ★ The canonical width-`width` word has block-width exactly `width` (its `blockOf` recovers the width). -/
theorem blockOf_leftRightPow (width : Nat) : blockOf (leftRightPow width).length = width := by
  induction width with
  | zero => simp only [leftRightPow]; rfl
  | succ count ih => rw [leftRightPow_length_succ, blockOf_add_two, ih]

/-- ★ The canonical words compose additively: `(L·R)^a · (L·R)^b = (L·R)^(a+b)` — block-widths add, the unital
monoid of canonical ordinals. -/
theorem leftRightPow_add (leftCount rightCount : Nat) :
    composePath (leftRightPow leftCount) (leftRightPow rightCount) = leftRightPow (leftCount + rightCount) := by
  induction leftCount with
  | zero => simp only [leftRightPow, Nat.zero_add]; rfl
  | succ count ih =>
      rw [leftRightPow, composePath_assoc, ih, Nat.succ_add, ← leftRightPow]

/-- Smoke: the single block `(L·R)^1` is exactly `adjunctionLeftThenRight`. -/
theorem leftRightPow_one : leftRightPow 1 = adjunctionLeftThenRight := by
  simp only [leftRightPow]
  exact composePath_identityPath_right adjunctionLeftThenRight

/-! ## The EZ staircase steps: a single whiskered cup (face) / cap (degeneracy)

The Eilenberg–Zilber staircase steps.  A CUP (the unit `η : id ⇒ L·R`) whiskered to block position `leftBlocks`
post-composes the FACE `δ_leftBlocks` and grows the width by one; a CAP (the counit `ε : R·L ⇒ id`) post-composes
the DEGENERACY `σ_leftBlocks` and shrinks it.  These two `runMonoCell` reductions read the staircase step off the
generator DIRECTLY — the headline of the monotone route: the map gives the step, no node-id reconstruction. -/

/-- One fold step at the bare UNIT generator: the cup post-composes the FACE at the block position of the left
context (`monoStepAtom`'s `(0,2)` arity branch).  Definitional. -/
theorem runMonoCell_adjunctionUnit_snd {overallSource overallTarget : AdjunctionMode}
    (state : Nat × List Nat)
    (leftAcc : ModalityPath adjunctionModeSignature.graph overallSource AdjunctionMode.base)
    (rightAcc : ModalityPath adjunctionModeSignature.graph AdjunctionMode.base overallTarget) :
    (runMonoCell state leftAcc rightAcc adjunctionUnitTwoCell).2
      = composeMap state.2 (faceMap (blockOf leftAcc.length) state.1) := rfl

/-- One fold step at the bare COUNIT generator: the cap post-composes the DEGENERACY at the block position,
shrinking the width by one (`monoStepAtom`'s `(2,0)` arity branch).  Definitional. -/
theorem runMonoCell_adjunctionCounit_snd {overallSource overallTarget : AdjunctionMode}
    (state : Nat × List Nat)
    (leftAcc : ModalityPath adjunctionModeSignature.graph overallSource AdjunctionMode.tip)
    (rightAcc : ModalityPath adjunctionModeSignature.graph AdjunctionMode.tip overallTarget) :
    (runMonoCell state leftAcc rightAcc adjunctionCounitTwoCell).2
      = composeMap state.2 (degenMap (blockOf leftAcc.length) (state.1 - 1)) := rfl

/-- The **raw face staircase step**: the cup (unit) whiskered into block position `leftBlocks` of a width
`leftBlocks + rightBlocks` word — `(L·R)^leftBlocks ◁ ((L·R)^rightBlocks ▷ η)`.  Its monotone map is the face
`δ_leftBlocks`. -/
def rawFaceStep (leftBlocks rightBlocks : Nat) :=
  RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature) (leftRightPow leftBlocks)
    (RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature) (leftRightPow rightBlocks)
      adjunctionUnitTwoCell)

/-- ★ **REALIZATION of the face step.**  `monotoneMapOf (rawFaceStep leftBlocks rightBlocks) =
faceMap leftBlocks (leftBlocks + rightBlocks)` — the cup at block position `leftBlocks` in width
`leftBlocks + rightBlocks` folds to exactly the face `δ_leftBlocks`.  Computed by the `runMonoCell` fold: the
whiskerings shift the accumulators, the unit reads off `faceMap` at `blockOf leftContext.length = leftBlocks`,
and the running identity is absorbed by `composeMap_idMap_eq`. -/
theorem monotoneMapOf_rawFaceStep (leftBlocks rightBlocks : Nat) :
    monotoneMapOf (rawFaceStep leftBlocks rightBlocks) = faceMap leftBlocks (leftBlocks + rightBlocks) := by
  have hsrc : blockOf (composePath (leftRightPow leftBlocks) (leftRightPow rightBlocks)).length
      = leftBlocks + rightBlocks := by rw [leftRightPow_add]; exact blockOf_leftRightPow _
  unfold rawFaceStep
  rw [monotoneMapOf_eq_runMonoCell, runMonoCell_whiskerLeft, runMonoCell_whiskerRight,
      runMonoCell_adjunctionUnit_snd]
  show composeMap (idMap (blockOf (composePath (leftRightPow leftBlocks) (leftRightPow rightBlocks)).length))
        (faceMap (blockOf (leftRightPow leftBlocks).length)
          (blockOf (composePath (leftRightPow leftBlocks) (leftRightPow rightBlocks)).length))
      = faceMap leftBlocks (leftBlocks + rightBlocks)
  rw [hsrc, blockOf_leftRightPow leftBlocks]
  have hcollapse := composeMap_idMap_eq (faceMap leftBlocks (leftBlocks + rightBlocks))
  rw [faceMap_length] at hcollapse
  exact hcollapse

/-! ## The dual EZ staircase step: a single whiskered cap (degeneracy)

The dual of the cup.  The cap (counit `ε : R·L ⇒ id`) sits at a block boundary of `(L·R)^n`, removing one `R·L`;
its monotone map is the degeneracy `σ`.  Mode bookkeeping is intrinsic: at `base` the counit is whiskered by a
single `left` on the left and a single `right` on the right so its `R·L` aligns with a block click.  The source
word is again forced to a canonical `leftRightPow`, computed by `degenStepSource_eq`. -/

/-- `singleLeft · singleRight = L·R` — two single modalities compose to one canonical block (definitional). -/
theorem composePath_singleLeft_singleRight :
    composePath (singletonModalityPath AdjunctionModality.left) (singletonModalityPath AdjunctionModality.right)
      = adjunctionLeftThenRight := rfl

/-- `R·L = singleRight · singleLeft` — the counit's source decomposes into the two single modalities. -/
theorem adjunctionRightThenLeft_eq :
    adjunctionRightThenLeft
      = composePath (singletonModalityPath AdjunctionModality.right) (singletonModalityPath AdjunctionModality.left) :=
  rfl

/-- `left · (right · rest) = (L·R) · rest` — a `left·right` pair at the head collapses to one canonical block. -/
theorem composePath_singleLeft_then_singleRight {targetMode : AdjunctionMode}
    (rest : ModalityPath adjunctionGraph AdjunctionMode.base targetMode) :
    composePath (singletonModalityPath AdjunctionModality.left)
        (composePath (singletonModalityPath AdjunctionModality.right) rest)
      = composePath adjunctionLeftThenRight rest := by
  rw [← composePath_assoc, composePath_singleLeft_singleRight]

/-- `blockOf` of the canonical word extended by a single `left` is the same block-width (the dangling `left` opens
no new block) — the cap's whisker-position lemma. -/
theorem blockOf_leftRightPow_succ_odd (width : Nat) :
    blockOf ((leftRightPow width).length + 1) = width := by
  induction width with
  | zero => simp only [leftRightPow]; rfl
  | succ count ih =>
      rw [leftRightPow_length_succ, Nat.add_right_comm (leftRightPow count).length 2 1,
          blockOf_add_two, ih]

/-- The cap's left whisker context `(L·R)^width · left` has block position `width`. -/
theorem blockOf_leftContext (width : Nat) :
    blockOf (composePath (leftRightPow width) (singletonModalityPath AdjunctionModality.left)).length = width := by
  rw [ModalityPath.length_composePath]
  exact blockOf_leftRightPow_succ_odd width

/-- ★ **The cap source word is canonical.**  `(L·R)^lb · left · (R·L) · right · (L·R)^rb = (L·R)^(lb + rb + 2)` —
the cap's source 1-cell is forced to the canonical word of block-width `lb + rb + 2`.  Pure path algebra: flatten
by associativity, collapse each `left · right` to one block (`composePath_singleLeft_singleRight`), and re-fold to
`leftRightPow`. -/
theorem degenStepSource_eq (leftBlocks rightBlocks : Nat) :
    composePath (composePath (leftRightPow leftBlocks) (singletonModalityPath AdjunctionModality.left))
      (composePath adjunctionRightThenLeft
        (composePath (singletonModalityPath AdjunctionModality.right) (leftRightPow rightBlocks)))
      = leftRightPow (leftBlocks + (rightBlocks + 1) + 1) := by
  rw [composePath_assoc, adjunctionRightThenLeft_eq, composePath_assoc,
      composePath_singleLeft_then_singleRight, composePath_singleLeft_then_singleRight,
      ← leftRightPow, ← leftRightPow, leftRightPow_add]
  rfl

/-- The **raw degeneracy staircase step**: the cap (counit) whiskered to block position `leftBlocks` of a width
`leftBlocks + rightBlocks + 2` word — `((L·R)^leftBlocks · left) ◁ ((right · (L·R)^rightBlocks) ▷ ε)`.  Its
monotone map is the degeneracy `σ_leftBlocks`. -/
def rawDegenStep (leftBlocks rightBlocks : Nat) :=
  RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature)
    (composePath (leftRightPow leftBlocks) (singletonModalityPath AdjunctionModality.left))
    (RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature)
      (composePath (singletonModalityPath AdjunctionModality.right) (leftRightPow rightBlocks))
      adjunctionCounitTwoCell)

/-- ★ **REALIZATION of the degeneracy step.**  `monotoneMapOf (rawDegenStep leftBlocks rightBlocks) =
degenMap leftBlocks (leftBlocks + (rightBlocks + 1))` — the cap at block position `leftBlocks` in source width
`leftBlocks + rightBlocks + 2` folds to exactly the degeneracy `σ_leftBlocks`.  Computed by the `runMonoCell`
fold: the counit reads off `degenMap` at `blockOf leftContext.length = leftBlocks` shrinking the width by one
(`degenStepSource_eq` pins the source width), and the running identity is absorbed by `composeMap_idMap_eq`. -/
theorem monotoneMapOf_rawDegenStep (leftBlocks rightBlocks : Nat) :
    monotoneMapOf (rawDegenStep leftBlocks rightBlocks)
      = degenMap leftBlocks (leftBlocks + (rightBlocks + 1)) := by
  have hsrc : blockOf (composePath (composePath (leftRightPow leftBlocks)
        (singletonModalityPath AdjunctionModality.left))
      (composePath adjunctionRightThenLeft
        (composePath (singletonModalityPath AdjunctionModality.right) (leftRightPow rightBlocks)))).length
      = leftBlocks + (rightBlocks + 1) + 1 := by
    rw [degenStepSource_eq]; exact blockOf_leftRightPow _
  unfold rawDegenStep
  rw [monotoneMapOf_eq_runMonoCell, runMonoCell_whiskerLeft, runMonoCell_whiskerRight,
      runMonoCell_adjunctionCounit_snd]
  show composeMap (idMap (blockOf (composePath (composePath (leftRightPow leftBlocks)
          (singletonModalityPath AdjunctionModality.left))
        (composePath adjunctionRightThenLeft
          (composePath (singletonModalityPath AdjunctionModality.right) (leftRightPow rightBlocks)))).length))
        (degenMap (blockOf (composePath (leftRightPow leftBlocks)
            (singletonModalityPath AdjunctionModality.left)).length)
          (blockOf (composePath (composePath (leftRightPow leftBlocks)
              (singletonModalityPath AdjunctionModality.left))
            (composePath adjunctionRightThenLeft
              (composePath (singletonModalityPath AdjunctionModality.right) (leftRightPow rightBlocks)))).length - 1))
      = degenMap leftBlocks (leftBlocks + (rightBlocks + 1))
  rw [hsrc, blockOf_leftContext leftBlocks,
      show leftBlocks + (rightBlocks + 1) + 1 - 1 = leftBlocks + (rightBlocks + 1) from Nat.succ_sub_one _]
  have hcollapse := composeMap_idMap_eq (degenMap leftBlocks (leftBlocks + (rightBlocks + 1)))
  rw [degenMap_length] at hcollapse
  exact hcollapse

/-! ## The identity staircase (the empty word's canonical cell) -/

/-- The **canonical identity 2-cell** at block-width `width`: the identity on the canonical word `(L·R)^width`.
Its monotone map is `idMap width`. -/
def canonicalIdentityCell (width : Nat) :
    RawTwoCellExpr adjunctionModeSignature (leftRightPow width) (leftRightPow width) :=
  RawTwoCellExpr.id (signature := adjunctionModeSignature) (leftRightPow width)

/-- The monotone map of any identity 2-cell is the identity map at the boundary block-width. -/
theorem monotoneMapOf_id {sourceMode targetMode : AdjunctionMode}
    (path : ModalityPath adjunctionGraph sourceMode targetMode) :
    monotoneMapOf (RawTwoCellExpr.id (signature := adjunctionModeSignature) path)
      = idMap (blockOf path.length) := rfl

/-- ★ **REALIZATION of the identity staircase.**  `monotoneMapOf (canonicalIdentityCell width) = idMap width`. -/
theorem monotoneMapOf_canonicalIdentityCell (width : Nat) :
    monotoneMapOf (canonicalIdentityCell width) = idMap width := by
  show monotoneMapOf (RawTwoCellExpr.id (signature := adjunctionModeSignature) (leftRightPow width)) = idMap width
  rw [monotoneMapOf_id, blockOf_leftRightPow]

/-! ## ★ The reconstruction RESIDUAL and the `convOfMapEq` reduction

The genuine YES-direction crux is `AdjunctionSaturatedCanonicalization.convOfMapEq`: cells with equal monotone
maps are saturated-convertible.  This section names the residual PRECISELY — a `CanonicalStaircaseData`: a
choice of canonical staircase cell per cell, depending only on the monotone map (`canonRespectsMap`), to which
every cell is saturated-convertible (`reconstructs`) — and PROVES the reduction: such data yields `convOfMapEq`
in full (glued by saturated symmetry + transitivity).  Constructing the data (the EZ epi-then-mono staircase of
an arbitrary map, plus the cell-level reconstruction past the spine quotient via whisker functoriality and the
triangle identities) is what remains; the concrete staircase STEPS above (`monotoneMapOf_rawFaceStep`,
`monotoneMapOf_canonicalIdentityCell`) are its building blocks. -/

/-- The **reconstruction residual** as data: a canonical staircase cell per cell that (1) depends only on the
monotone map and (2) is saturated-convertible to its source cell.  This is exactly what the keystone's
`convOfMapEq` needs — packaged so the reduction below is a one-line glue. -/
structure CanonicalStaircaseData where
  /-- The canonical staircase cell of a 2-cell (in the same hom-set). -/
  canonicalCellOf : {sourceMode targetMode : AdjunctionMode} →
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode} →
    RawTwoCellExpr adjunctionModeSignature sourcePath targetPath →
    RawTwoCellExpr adjunctionModeSignature sourcePath targetPath
  /-- The canonical cell depends ONLY on the monotone map (equal maps ⟹ equal canonical cells). -/
  canonRespectsMap : {sourceMode targetMode : AdjunctionMode} →
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode} →
    (cellA cellB : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) →
    monotoneMapOf cellA = monotoneMapOf cellB → canonicalCellOf cellA = canonicalCellOf cellB
  /-- Every cell is saturated-convertible to its canonical staircase (the cell-level reconstruction). -/
  reconstructs : {sourceMode targetMode : AdjunctionMode} →
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode} →
    (cell : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) →
    SaturatedTwoCellConv cell (canonicalCellOf cell)

/-- ★ **The reconstruction reduction.**  A `CanonicalStaircaseData` yields the keystone's COMPLETENESS direction
`convOfMapEq`: cells with equal monotone maps are saturated-convertible.  Glue: `cellA ≈ canon(cellA) = canon(cellB)
≈ cellB` — reconstruction of each side, the canonical cells equal because the maps are (`canonRespectsMap`),
threaded by saturated transitivity and symmetry.  So closing the residual `CanonicalStaircaseData` closes the whole
YES-direction. -/
theorem convOfMapEq_of_canonicalStaircase (data : CanonicalStaircaseData)
    {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    (cellA cellB : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath)
    (hmap : monotoneMapOf cellA = monotoneMapOf cellB) :
    SaturatedTwoCellConv cellA cellB :=
  SaturatedTwoCellConv.trans (data.reconstructs cellA)
    (SaturatedTwoCellConv.trans
      (data.canonRespectsMap cellA cellB hmap ▸ SaturatedTwoCellConv.refl (data.canonicalCellOf cellA))
      (SaturatedTwoCellConv.symm (data.reconstructs cellB)))

/-- ★ **From staircase data to the full keystone.**  A `CanonicalStaircaseData` together with the SOUNDNESS
direction `mapEqOfConv` (the sibling's Godement residual) assembles the complete
`AdjunctionSaturatedCanonicalization` — the Schanuel–Street "free adjunction" decision.  This pins exactly how the
two residuals compose into the keystone. -/
def canonicalizationOfStaircaseData (data : CanonicalStaircaseData)
    (mapEqOfConv : {sourceMode targetMode : AdjunctionMode} →
      {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode} →
      {cellA cellB : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath} →
      SaturatedTwoCellConv cellA cellB → monotoneMapOf cellA = monotoneMapOf cellB) :
    AdjunctionSaturatedCanonicalization where
  monotoneMapOf := monotoneMapOf
  mapEqOfConv := mapEqOfConv
  convOfMapEq := fun hmap => convOfMapEq_of_canonicalStaircase data _ _ hmap

/-! ## Honesty markers -/

/-- **★ ESTABLISHED — BOTH EZ staircase STEPS realize their generators, plus the identity.**  The two
Eilenberg–Zilber staircase steps are realized zero-axiom: the cup `rawFaceStep leftBlocks rightBlocks` (whiskered
to block position `leftBlocks` at width `leftBlocks + rightBlocks`) realizes the FACE `δ_leftBlocks`
(`monotoneMapOf_rawFaceStep`), and the cap `rawDegenStep leftBlocks rightBlocks` realizes the DEGENERACY
`σ_leftBlocks` (`monotoneMapOf_rawDegenStep`) — the complete EZ generator set (faces + degeneracies) at the cell
level.  The identity staircase realizes `idMap` (`monotoneMapOf_canonicalIdentityCell`).  These are the concrete
"the map gives the staircase step" building blocks of `canonicalCellOf` — and the headline of the monotone route:
the map reads off the step directly, no node-id / union-find reconstruction.  `= true`. -/
def fxMode_hasSaturatedMonotoneMapStaircaseStep : Bool := true

/-- **★ ESTABLISHED — the faithfulness RESIDUAL is reduced to canonical-staircase DATA.**  The keystone's
COMPLETENESS direction `convOfMapEq` (equal maps ⟹ saturated-convertible) is reduced, zero-axiom, to a single
residual `CanonicalStaircaseData` by `convOfMapEq_of_canonicalStaircase` (saturated symm/trans glue), and the
full `AdjunctionSaturatedCanonicalization` is assembled from that data plus the soundness residual by
`canonicalizationOfStaircaseData`.  So the remaining YES-direction work is exactly: build `canonicalCellOf` (the
EZ epi-then-mono staircase of an arbitrary monotone map from the shipped `rankList`/`imageList` factorization) and
its per-cell `reconstructs` (induction on the cell via whisker functoriality + the triangle identities).  `= true`. -/
def fxMode_hasSaturatedMonotoneMapFaithfulnessReduction : Bool := true

/-- **Honesty marker — the faithfulness reconstruction itself is NOT yet closed.**  (Distinct name from the
sibling's `fxMode_hasSaturatedMonotoneMapFaithfulness`, which this file imports and leaves `= false`.)
`CanonicalStaircaseData` is not yet a constructed term: the EZ staircase of an ARBITRARY monotone map (decomposing
`rankList`/`imageList` into single degeneracy / face steps with matching `leftRightPow` boundaries) and the
cell-level `reconstructs` (the induction pushing every cell to its staircase past the spine quotient) remain.  The
concrete staircase steps + the reduction above are the honest partial; the full YES-direction stays `= false`. -/
def fxMode_hasMonotoneRouteFaithfulnessReconstructed : Bool := false

end FX1Poly.Tier0
