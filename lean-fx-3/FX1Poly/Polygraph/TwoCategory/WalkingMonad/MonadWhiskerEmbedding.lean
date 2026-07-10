import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadMapFactorization
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadSaturatedSkeletonReps

/-! # WalkingMonad — the WHISKER-EMBEDDING: the fold of a whiskered cell is the ORDINAL-SUM embedding of its map

`WalkingMonad/MonadMapFactorization` shipped the vertical-composition homomorphism `monadMonotoneMapOf_vcomp`,
discharging the two vcomp-congruence cases of `mapEqOfConv`.  The two WHISKER-congruence cases
(`whiskerLeftCongr` / `whiskerRightCongr`) carry a sub-derivation `MonadSaturatedTwoCellConv body body'`, so they
need a lemma making `monadMonotoneMapOf (whiskerLeft W body)` a FUNCTION of `monadMonotoneMapOf body`.  In Δ₊ that
function is the ORDINAL SUM `id_[W] + (map body)`: whiskering by a 1-cell `W` on the left prefixes `W.length`
untouched identity wires and shifts the body's map up by `W.length`; whiskering on the right appends `W.length`
identity wires at the top.

## What this file ships (each piece zero-axiom)

  * **`embedLocalMap`** — the ordinal-sum embedding `id_L ⊕ localMap ⊕ id_R` (via the cons-only
    `ascendingPrepend` / `shiftPrepend`, no `++`, propext-safe), with its length + three region-wise value
    characterizations.  RELOCATED to the bespoke-free `MonadSaturatedSkeletonReps` bridge (single home) and
    imported here; the bridge lets the KZ order model consume this embedding conv-decoupled.
  * ★ **`monadRunMonoCell_localEmbed`** — the crux: the fold of any free 2-cell run at accumulators
    `leftAcc / rightAcc` from the identity state IS `embedLocalMap leftAcc.length bodyCod.length rightAcc.length`
    applied to the cell's LOCAL map (`monadMonotoneMapOf`).  Structural induction on the cell: generators are the
    face / degeneracy decompositions, `vcomp` is `embedLocalMap`'s composition-functoriality, the whiskerings are
    `embedLocalMap`'s nesting-associativity.
  * ★ **`monadMonotoneMapOf_whiskerLeft` / `_whiskerRight`** — the two top-level specializations: the whiskered
    cell's map is the ordinal-sum embedding of the body's map.
  * ★ **`monadMonotoneMapOf_whiskerLeftCongr` / `_whiskerRightCongr`** — the two WHISKER-congruence cases of
    `mapEqOfConv`, immediate `congrArg`s of the embeddings.

Raw Lean 4 + Init; `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free (cons-only lists,
pointwise `listExtById`, hand arithmetic).  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph

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
