import FX1Poly.Polygraph.TwoCategory.Amalgam.DeciderReseat
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWallFreePathInversion
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWallFreeCellConverse
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFinestPairs

/-! # Polygraph/TwoCategory/Amalgam/PushoutWallFreeCellInvert — the wall-free CELL converse `wallFreeCellInvert`:
the generator reseat crux + the four-case structural recursion (WP-AMALG-2 r12, the cell-converse round)

The r11 ledger (`PushoutWallFreeCellConverse.lean`) shipped the CLEAN structural prerequisites of the cell converse
(`wallFreeMiddleOfCell`, the wall-free / wall-count bridge) and scoped the full four-case `wallFreeCellInvert` — and
especially the generator `gen` case (the CONVERSE of `interpretWordFrom_map`) — as cast-heavy LABOR to r12.  This
file closes the FORWARD cell converse.

## The generator reseat crux `wallFreeGenInvert` (the CONVERSE of `interpretWordFrom_map`)

A pushout 2-generator (a retagged monad `eta` / `mu`) at a wall-free boundary reconstructs its MONAD 2-generator at
the `pathInvert` boundary.  The reseat index is `retractRightTwoGen` (the offset is `0` because the involution
component has no 2-generators, so `embedRightTwoGen ∘ retractRightTwoGen = id`).  The interpreter conjuncts are the
converse of `RealCoprojection`'s `interpretWordFrom_map`: from the pushout interpretation of the retagged word, the
monad interpretation of the original word is recovered — and its path pre-image is pinned to `pathInvert` through
the shipped `mapPath_inclRight_pathInvert` + `mapPath_inclRight_injective`.  The dependent-Sigma extraction is made
propext-safe by the WORD-route projection (`pushoutPathWord ∘ .snd`) BEFORE `Option.some.inj` — the `reseatInterp`
technique of `MonadReseat.lean`.

## The four-case structural recursion `wallFreeCellInvert`

`id` / `vcomp` are cast-free (the middle 1-cell's wall-freeness supplied by `wallFreeMiddleOfCell`); `gen` is the
crux; the two whisker cases thread `pathInvert_composePath` through one `castBoundary`, byte-for-byte the shape of
`MapCell.lean`'s `mapCellAlong`.

Raw Lean 4 + Init.  STRUCTURAL on the cell / path / word.  Per-declaration `#assert_no_axioms` gated in the audit
twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The monad single-mode singleton -/

/-- Every mode of the walking-monad computad is `monadOnlyMode` — `monadComputad.modeCount = 1`, a singleton, so an
index `⟨0, _⟩` is `monadOnlyMode` by `Fin`-proof-irrelevance and any `⟨count + 1, _⟩` is absurd (`Nat.not_lt_zero`).
Propext-free (`Fin.mk` casing, NOT `Fin.cases`).  The monad-side analogue of `pushoutModeUnique`. -/
theorem monadModeUnique (mode : Fin monadComputad.modeCount) : mode = monadOnlyMode :=
  match mode with
  | ⟨0, _⟩ => rfl
  | ⟨count + 1, isLt⟩ => False.elim (Nat.not_lt_zero count (Nat.lt_of_succ_lt_succ isLt))

/-! ## The 2-generator retract (the converse of `embedRightTwoGen`, offset `0`) -/

/-- The **2-generator retract** — a pushout 2-generator index `pIndex` retracts to the monad 2-generator index of the
same `.val`.  The bound holds because the pushout 2-generator count equals the monad's (the involution component has
no 2-generators, `0 + monadComputad.twoCellGenerators.length`), definitionally.  The converse of `embedRightTwoGen`
with the collapsed offset `0`. -/
def retractRightTwoGen (pIndex : Fin involutionMonadPushout.twoCellGenerators.length) :
    Fin monadComputad.twoCellGenerators.length :=
  ⟨pIndex.val, pIndex.isLt⟩

/-- The retract is a section of `embedRightTwoGen` — `embedRightTwoGen ∘ retractRightTwoGen = id` on pushout
2-generator indices, because the offset `involutionComputad.twoCellGenerators.length = 0` collapses (`Nat.zero_add`,
`Fin.ext`). -/
theorem embedRight_retractRight (pIndex : Fin involutionMonadPushout.twoCellGenerators.length) :
    embedRightTwoGen involutionComputad monadComputad involutionMonadSameModes (retractRightTwoGen pIndex)
      = pIndex :=
  Fin.ext (Nat.zero_add pIndex.val)

/-- The pushout 2-generator at `pIndex` is the retag of the monad 2-generator at `retractRightTwoGen pIndex` —
`congrArg get` on the section `embedRight_retractRight`, then `pushoutTwoGenGetRight`. -/
theorem pushoutGetRetract (pIndex : Fin involutionMonadPushout.twoCellGenerators.length) :
    involutionMonadPushout.twoCellGenerators.get pIndex
      = retagRightTwoGen involutionComputad monadComputad involutionMonadSameModes
          (monadComputad.twoCellGenerators.get (retractRightTwoGen pIndex)) :=
  (congrArg (involutionMonadPushout.twoCellGenerators.get ·) (embedRight_retractRight pIndex).symm).trans
    (pushoutTwoGenGetRight involutionComputad monadComputad involutionMonadSameModes (retractRightTwoGen pIndex))

/-- The pushout 2-generator's stored `lhs` word is the `embedRightLetter`-retag of the retracted monad
2-generator's `lhs` word — `congrArg lhs` on `pushoutGetRetract` (the retag's `lhs` field is defeq the map). -/
theorem pushoutGetLhsWord (pIndex : Fin involutionMonadPushout.twoCellGenerators.length) :
    (involutionMonadPushout.twoCellGenerators.get pIndex).lhs
      = (monadComputad.twoCellGenerators.get (retractRightTwoGen pIndex)).lhs.map
          (embedRightLetter involutionComputad monadComputad involutionMonadSameModes) :=
  congrArg ComputadTwoGen.lhs (pushoutGetRetract pIndex)

/-- The pushout 2-generator's stored `rhs` word is the `embedRightLetter`-retag of the retracted monad
2-generator's `rhs` word. -/
theorem pushoutGetRhsWord (pIndex : Fin involutionMonadPushout.twoCellGenerators.length) :
    (involutionMonadPushout.twoCellGenerators.get pIndex).rhs
      = (monadComputad.twoCellGenerators.get (retractRightTwoGen pIndex)).rhs.map
          (embedRightLetter involutionComputad monadComputad involutionMonadSameModes) :=
  congrArg ComputadTwoGen.rhs (pushoutGetRetract pIndex)

/-! ## The interpreter converse (the propext-safe extraction) -/

/-- ★★★ **THE INTERPRETER CONVERSE.**  If the PUSHOUT interpreter reads the right-retagged monad word to a wall-free
boundary `pushoutBoundary`, then the MONAD interpreter reads the original monad word to `pathInvert pushoutBoundary`.
The converse of `interpretWordFrom_map`: the pushout interpretation equals the `mapPath`-image of the monad
interpretation, so the monad interpretation is `some` at a single-mode target (`monadModeUnique`), whose path
pre-image reads (via the WORD projection `pushoutPathWord ∘ .snd`, propext-safe) to `pushoutBoundary` under
`mapPath inclRight` — and `mapPath_inclRight_pathInvert` + `mapPath_inclRight_injective` pin it to
`pathInvert pushoutBoundary`. -/
theorem monadInterpOfPushoutInterp
    (word : List (Fin monadComputad.modalityGenerators.length))
    (pushoutBoundary : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode)
    (wf : pathWallFree pushoutBoundary)
    (hpush : involutionMonadPushout.interpretWordFrom monadPushMode
        (word.map (embedRightLetter involutionComputad monadComputad involutionMonadSameModes))
      = some ⟨monadPushMode, pushoutBoundary⟩) :
    monadComputad.interpretWordFrom monadOnlyMode word
      = some ⟨monadOnlyMode, pathInvert pushoutBoundary wf⟩ := by
  have mapEq := interpretWordFrom_map (inclusionRight involutionComputad monadComputad involutionMonadSameModes)
    (inclusionRight_onModes_injective involutionComputad monadComputad involutionMonadSameModes)
    monadOnlyMode word
  -- combine: the monad interpretation, mapped forward, equals the pushout interpretation (= some boundary)
  have hmapped := mapEq.symm.trans hpush
  cases hX : monadComputad.interpretWordFrom monadOnlyMode word with
  | none =>
      rw [hX] at hmapped
      dsimp only [Option.map_none] at hmapped
      cases hmapped
  | some xSig =>
      obtain ⟨xMode, xPath⟩ := xSig
      -- pin the single-mode target FIRST, so the mapped path's target reads `monadPushMode`
      have xModeEq : xMode = monadOnlyMode := monadModeUnique xMode
      subst xModeEq
      rw [hX] at hmapped
      -- word projection: extract the non-dependent boundary-word equality (propext-safe)
      have projected := congrArg (Option.map (fun sig => pushoutPathWord sig.snd)) hmapped
      dsimp only [Option.map_some] at projected
      have wordEq := Option.some.inj projected
      have pathEq : mapPath (inclusionRight involutionComputad monadComputad involutionMonadSameModes) xPath
          = pushoutBoundary :=
        pushoutPathWord_injective _ _ wordEq
      have xPathEq : xPath = pathInvert pushoutBoundary wf :=
        mapPath_inclRight_injective _ _
          (pathEq.trans (mapPath_inclRight_pathInvert pushoutBoundary wf).symm)
      subst xPathEq
      rfl

/-! ## The generator reseat crux -/

/-- ★★★ **THE GENERATOR RESEAT CRUX.**  A pushout 2-generator at a wall-free boundary reconstructs its MONAD
2-generator at the `pathInvert` boundary — the CONVERSE of `interpretWordFrom_map`.  The index is
`retractRightTwoGen generator.val`; the two interpreter conjuncts are `monadInterpOfPushoutInterp` applied to the
generator's stored `lhs` / `rhs` words (rewritten from the pushout 2-generator table by `pushoutGetRetract`).  NO
2-cell equality is decided.  This is the r11-scoped `gen` case, delivered.  The boundary modes are universally
quantified (the whisker case of `wallFreeCellInvert` supplies an existential middle mode); both collapse to
`monadPushMode` by the singleton `pushoutModeUnique` (`subst`, propext-free), after which the monadPushMode-specific
`monadInterpOfPushoutInterp` fires. -/
def wallFreeGenInvert
    {sourceMode targetMode : Fin involutionMonadPushout.modeCount}
    {sourcePath targetPath : ModalityPath involutionMonadPushout.toModeGraph sourceMode targetMode}
    (generator : involutionMonadPushout.ReconstructedTwoCell sourcePath targetPath)
    (wfS : pathWallFree sourcePath) (wfT : pathWallFree targetPath) :
    monadComputad.ReconstructedTwoCell (pathInvert sourcePath wfS) (pathInvert targetPath wfT) := by
  obtain rfl := pushoutModeUnique sourceMode
  obtain rfl := pushoutModeUnique targetMode
  exact ⟨retractRightTwoGen generator.val,
    monadInterpOfPushoutInterp
      (monadComputad.twoCellGenerators.get (retractRightTwoGen generator.val)).lhs sourcePath wfS
      (pushoutGetLhsWord generator.val ▸ generator.property.1),
    monadInterpOfPushoutInterp
      (monadComputad.twoCellGenerators.get (retractRightTwoGen generator.val)).rhs targetPath wfT
      (pushoutGetRhsWord generator.val ▸ generator.property.2)⟩

/-! ## Truth probes — the crux fires on the reconstructed monad unit and multiplication -/

/-- The **pushout monad multiplication** — reconstructed 2-generator index `1` at the boundary `(t·t, t)`: the
interpreter sends the retagged `lhs = [t, t]` to `t·t` and `rhs = [t]` to `t`, both by `rfl`. -/
def pushoutMonadMult :
    involutionMonadPushout.ReconstructedTwoCell
      (composePath monadPushTPath monadPushTPath) monadPushTPath :=
  ⟨⟨1, by decide⟩, ⟨rfl, rfl⟩⟩

/-- ★★ **TRUTH PROBE (unit).**  Inverting the pushout monad unit (`pushoutMonadUnit`, index `0`, at the wall-free
boundary `(id, t)`) lands at monad 2-generator index `0` (the monad `eta`) — a genuine `rfl` reduction. -/
theorem wallFreeGenInvert_unit_index :
    (wallFreeGenInvert pushoutMonadUnit True.intro monadPushTPath_wallFree).val.val = 0 := rfl

/-- ★★ **TRUTH PROBE (multiplication).**  Inverting the pushout monad multiplication (`pushoutMonadMult`, index `1`,
at the wall-free boundary `(t·t, t)`) lands at monad 2-generator index `1` (the monad `mu`) — a genuine `rfl`
reduction.  The recon's hand-worked `mu` firing, machine-checked. -/
theorem wallFreeGenInvert_mult_index :
    (wallFreeGenInvert pushoutMonadMult tRunTwoWallFree monadPushTPath_wallFree).val.val = 1 := rfl

/-! ## The wall-free split / join lemmas (the whisker-case ingredients) -/

/-- ★★ **Wall-freeness SPLITS over path composition** — a wall-free composite forces both factors wall-free.
STRUCTURAL on the first path (`composePath` recurses on the first, so the head letter's tag comes from the composite's
first conjunct and the tail recurses); NO wall-count arithmetic, NO `Nat.add_eq_zero` (propext-free).  The ingredient
the whisker cases of `wallFreeCellInvert` need to descend into the frame and the core. -/
theorem pathWallFree_composePath_split :
    {sourceMode middleMode targetMode : Fin involutionMonadPushout.modeCount} →
    (first : ModalityPath involutionMonadPushout.toModeGraph sourceMode middleMode) →
    (second : ModalityPath involutionMonadPushout.toModeGraph middleMode targetMode) →
    pathWallFree (composePath first second) →
    pathWallFree first ∧ pathWallFree second
  | _, _, _, .nil _, _second, wf => ⟨True.intro, wf⟩
  | _, _, _, .cons _letter rest, second, wf =>
      let restSplit := pathWallFree_composePath_split rest second wf.2
      ⟨⟨wf.1, restSplit.1⟩, restSplit.2⟩

/-- ★★ **Wall-freeness JOINS over path composition** — two wall-free factors give a wall-free composite (the converse
of the split).  STRUCTURAL on the first path.  Cheap; feeds the backward round-trip. -/
theorem pathWallFree_composePath_join :
    {sourceMode middleMode targetMode : Fin involutionMonadPushout.modeCount} →
    (first : ModalityPath involutionMonadPushout.toModeGraph sourceMode middleMode) →
    (second : ModalityPath involutionMonadPushout.toModeGraph middleMode targetMode) →
    pathWallFree first → pathWallFree second →
    pathWallFree (composePath first second)
  | _, _, _, .nil _, _second, _wfFirst, wfSecond => wfSecond
  | _, _, _, .cons _letter rest, second, wfFirst, wfSecond =>
      ⟨wfFirst.1, pathWallFree_composePath_join rest second wfFirst.2 wfSecond⟩

/-! ## The monad-side boundary-word homomorphism + `pathInvert_composePath` -/

/-- `List.map` distributes over `++`, reproved by hand (structural `congrArg`) so it is propext-free — the core
`List.map_append` leaks `propext`.  The concatenation law `pathInvert_composePath`'s word route needs. -/
theorem mapAppendDistrib {Source Target : Type} (mapper : Source → Target) :
    (listFirst listSecond : List Source) →
    (listFirst ++ listSecond).map mapper = listFirst.map mapper ++ listSecond.map mapper
  | [], _listSecond => rfl
  | head :: tailFirst, listSecond => congrArg (mapper head :: ·) (mapAppendDistrib mapper tailFirst listSecond)

/-- ★ **`monadPathWord` is a MONOID HOMOMORPHISM** — the boundary word of a monad path composite is the concatenation
of the boundary words (structural on the first path, `congrArg`).  The monad analogue of `pushoutPathWord_composePath`,
the word-level engine of `pathInvert_composePath`. -/
theorem monadPathWord_composePath :
    {sourceMode middleMode targetMode : Fin monadComputad.modeCount} →
    (first : ModalityPath monadComputad.toModeGraph sourceMode middleMode) →
    (second : ModalityPath monadComputad.toModeGraph middleMode targetMode) →
    monadPathWord (composePath first second) = monadPathWord first ++ monadPathWord second
  | _, _, _, .nil _, _second => rfl
  | _, _, _, .cons letter rest, second =>
      congrArg (letter.val :: ·) (monadPathWord_composePath rest second)

/-- ★★★ **`pathInvert` DISTRIBUTES over path composition** — inverting a wall-free composite is the composite of the
inverted factors.  Proved on the WORD route: `monadPathWord_injective` reduces the path equality to a monad-word
equality, `mapEmbedRight_injective` to its `embedRightLetter`-retag, which `monadEmbedInvert_word` (both factors) +
`monadPathWord_composePath` + `pushoutPathWord_composePath` fold to the same pushout boundary word.  No `castBoundary`,
no middle-mode `Eq.rec` (the pushout middle mode never enters — `pathInvert`'s output is fixed endo).  The dependent
plumbing lemma the two whisker cases of `wallFreeCellInvert` thread through `castBoundary`. -/
theorem pathInvert_composePath
    {sourceMode middleMode targetMode : Fin involutionMonadPushout.modeCount}
    (first : ModalityPath involutionMonadPushout.toModeGraph sourceMode middleMode)
    (second : ModalityPath involutionMonadPushout.toModeGraph middleMode targetMode)
    (wfBoth : pathWallFree (composePath first second))
    (wfFirst : pathWallFree first) (wfSecond : pathWallFree second) :
    pathInvert (composePath first second) wfBoth
      = composePath (pathInvert first wfFirst) (pathInvert second wfSecond) := by
  apply monadPathWord_injective
  apply mapEmbedRight_injective
  rw [monadEmbedInvert_word (composePath first second) wfBoth,
      monadPathWord_composePath (pathInvert first wfFirst) (pathInvert second wfSecond),
      mapAppendDistrib,
      monadEmbedInvert_word first wfFirst,
      monadEmbedInvert_word second wfSecond]
  exact pushoutPathWord_composePath first second

/-! ## The four-case structural recursion `wallFreeCellInvert` -/

/-- ★★★ **THE WALL-FREE CELL CONVERSE.**  A wall-free-boundary pushout 2-cell reconstructs a MONAD 2-cell at the
`pathInvert` boundary.  Structural on the cell, mirroring `mapCellAlong` with `pathInvert` in place of `mapPath`:

  * **`gen`** — the crux `wallFreeGenInvert`;
  * **`id`** — `id (pathInvert path _)` (proof-irrelevant `pathInvert`, so source/target coincide);
  * **`vcomp`** — recurse on both halves, the middle 1-cell's wall-freeness from `wallFreeMiddleOfCell` (cast-free —
    `pathInvert` of the shared middle is one term);
  * **`whiskerLeft` / `whiskerRight`** — split the composite boundary (`pathWallFree_composePath_split`), whisker the
    `pathInvert`-frame over the recursively-inverted core, and reconcile through the single `castBoundary
    (pathInvert_composePath …)` — byte-for-byte `mapCellAlong`'s whisker shape.

The pushout middle mode never enters the output (`pathInvert` is fixed endo at `monadOnlyMode`), so there is no
`Eq.rec`-through-a-type-level-function; the boundaries carry by `pathInvert`.  This is the r11-scoped forward cell
converse, delivered. -/
def wallFreeCellInvert :
    {sourceMode targetMode : Fin involutionMonadPushout.modeCount} →
    {sourcePath targetPath : ModalityPath involutionMonadPushout.toModeSignature.graph sourceMode targetMode} →
    RawTwoCellExpr involutionMonadPushout.toModeSignature sourcePath targetPath →
    (wfS : pathWallFree sourcePath) → (wfT : pathWallFree targetPath) →
    RawTwoCellExpr monadComputad.toModeSignature (pathInvert sourcePath wfS) (pathInvert targetPath wfT)
  | _, _, _, _, .gen generator, wfS, wfT => RawTwoCellExpr.gen (wallFreeGenInvert generator wfS wfT)
  | _, _, _, _, .id path, wfS, _wfT =>
      RawTwoCellExpr.id (signature := monadComputad.toModeSignature) (pathInvert path wfS)
  | _, _, _, _, .vcomp cellAlpha cellBeta, wfS, wfT =>
      RawTwoCellExpr.vcomp (wallFreeCellInvert cellAlpha wfS (wallFreeMiddleOfCell cellAlpha wfS))
        (wallFreeCellInvert cellBeta (wallFreeMiddleOfCell cellAlpha wfS) wfT)
  | _, _, _, _, @RawTwoCellExpr.whiskerLeft _ _ _ _ oneCell bodyDom bodyCod body, wfS, wfT =>
      RawTwoCellExpr.castBoundary
        (pathInvert_composePath oneCell bodyDom wfS
          (pathWallFree_composePath_split oneCell bodyDom wfS).1
          (pathWallFree_composePath_split oneCell bodyDom wfS).2).symm
        (pathInvert_composePath oneCell bodyCod wfT
          (pathWallFree_composePath_split oneCell bodyDom wfS).1
          (pathWallFree_composePath_split oneCell bodyCod wfT).2).symm
        (RawTwoCellExpr.whiskerLeft
          (pathInvert oneCell (pathWallFree_composePath_split oneCell bodyDom wfS).1)
          (wallFreeCellInvert body
            (pathWallFree_composePath_split oneCell bodyDom wfS).2
            (pathWallFree_composePath_split oneCell bodyCod wfT).2))
  | _, _, _, _, @RawTwoCellExpr.whiskerRight _ _ _ _ bodyDom bodyCod oneCell body, wfS, wfT =>
      RawTwoCellExpr.castBoundary
        (pathInvert_composePath bodyDom oneCell wfS
          (pathWallFree_composePath_split bodyDom oneCell wfS).1
          (pathWallFree_composePath_split bodyDom oneCell wfS).2).symm
        (pathInvert_composePath bodyCod oneCell wfT
          (pathWallFree_composePath_split bodyCod oneCell wfT).1
          (pathWallFree_composePath_split bodyDom oneCell wfS).2).symm
        (RawTwoCellExpr.whiskerRight
          (pathInvert oneCell (pathWallFree_composePath_split bodyDom oneCell wfS).2)
          (wallFreeCellInvert body
            (pathWallFree_composePath_split bodyDom oneCell wfS).1
            (pathWallFree_composePath_split bodyCod oneCell wfT).1))

/-! ## Forward probes — the cell converse fires on a concrete cell of every constructor -/

/-- The wall-free witness for the endo path `t·t` at the pushout, via the join law. -/
def tRunTwoWallFreeJoin : pathWallFree (composePath monadPushTPath monadPushTPath) :=
  pathWallFree_composePath_join monadPushTPath monadPushTPath monadPushTPath_wallFree monadPushTPath_wallFree

/-- ★★ **PROBE (id).**  Inverting the identity 2-cell on `t` yields the identity on `pathInvert t` — size `1`. -/
theorem wallFreeCellInvert_id_size :
    (wallFreeCellInvert (RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature) monadPushTPath)
        monadPushTPath_wallFree monadPushTPath_wallFree).size = 1 := rfl

/-- ★★ **PROBE (gen).**  Inverting the pushout unit cell `eta` yields a bare generator — size `1`. -/
theorem wallFreeCellInvert_gen_size :
    (wallFreeCellInvert pushoutEta True.intro monadPushTPath_wallFree).size = 1 := rfl

/-- A concrete wall-free vertical composite `id_t ⊟ id_t : t ⇒ t`. -/
def probeVcomp :
    RawTwoCellExpr involutionMonadPushout.toModeSignature monadPushTPath monadPushTPath :=
  RawTwoCellExpr.vcomp (RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature) monadPushTPath)
    (RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature) monadPushTPath)

/-- ★★ **PROBE (vcomp).**  Inverting `id_t ⊟ id_t` yields a vertical composite of two inverted identities — size
`1 + 1 + 1 = 3`. -/
theorem wallFreeCellInvert_vcomp_size :
    (wallFreeCellInvert probeVcomp monadPushTPath_wallFree monadPushTPath_wallFree).size = 3 := rfl

/-- A concrete wall-free left whiskering `t ⊳ id_t : t·t ⇒ t·t`. -/
def probeWhiskerLeft :
    RawTwoCellExpr involutionMonadPushout.toModeSignature
      (composePath monadPushTPath monadPushTPath) (composePath monadPushTPath monadPushTPath) :=
  RawTwoCellExpr.whiskerLeft (signature := involutionMonadPushout.toModeSignature) monadPushTPath
    (RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature) monadPushTPath)

/-- ★★ **PROBE (whiskerLeft).**  Inverting `t ⊳ id_t` typechecks at the `pathInvert` boundary — the whisker frame is
reconciled through `pathInvert_composePath`.  A genuine reduction of the whisker arm on concrete data. -/
def wallFreeCellInvertWhiskerLeftProbe :
    RawTwoCellExpr monadComputad.toModeSignature
      (pathInvert (composePath monadPushTPath monadPushTPath) tRunTwoWallFreeJoin)
      (pathInvert (composePath monadPushTPath monadPushTPath) tRunTwoWallFreeJoin) :=
  wallFreeCellInvert probeWhiskerLeft tRunTwoWallFreeJoin tRunTwoWallFreeJoin

/-- A concrete wall-free right whiskering `id_t ⊲ t : t·t ⇒ t·t`. -/
def probeWhiskerRight :
    RawTwoCellExpr involutionMonadPushout.toModeSignature
      (composePath monadPushTPath monadPushTPath) (composePath monadPushTPath monadPushTPath) :=
  RawTwoCellExpr.whiskerRight (signature := involutionMonadPushout.toModeSignature) monadPushTPath
    (RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature) monadPushTPath)

/-- ★★ **PROBE (whiskerRight).**  Inverting `id_t ⊲ t` typechecks at the `pathInvert` boundary — the whisker arm on
concrete data. -/
def wallFreeCellInvertWhiskerRightProbe :
    RawTwoCellExpr monadComputad.toModeSignature
      (pathInvert (composePath monadPushTPath monadPushTPath) tRunTwoWallFreeJoin)
      (pathInvert (composePath monadPushTPath monadPushTPath) tRunTwoWallFreeJoin) :=
  wallFreeCellInvert probeWhiskerRight tRunTwoWallFreeJoin tRunTwoWallFreeJoin

end FX1Poly.Polygraph.Amalgam
