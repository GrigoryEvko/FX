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
2-cell equality is decided.  This is the r11-scoped `gen` case, delivered. -/
def wallFreeGenInvert
    {sourcePath targetPath : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode}
    (generator : involutionMonadPushout.ReconstructedTwoCell sourcePath targetPath)
    (wfS : pathWallFree sourcePath) (wfT : pathWallFree targetPath) :
    monadComputad.ReconstructedTwoCell (pathInvert sourcePath wfS) (pathInvert targetPath wfT) :=
  ⟨retractRightTwoGen generator.val,
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

end FX1Poly.Polygraph.Amalgam
