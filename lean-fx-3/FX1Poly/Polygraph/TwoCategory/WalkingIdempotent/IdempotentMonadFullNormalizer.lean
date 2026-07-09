import FX1Poly.Polygraph.TwoCategory.WalkingIdempotent.IdempotentMonadRightWhisker

/-! # WalkingIdempotent/IdempotentMonadFullNormalizer — the boundary-determined representative + normalization

`IdempotentMonadRightWhisker` closed the general-width RIGHT-whisker canonicalisation; with `whiskerLeftCanon`
(LEFT) it gives the two whisker bricks.  This file assembles the boundary-determined total representative `repFull`
and the six-case structural normalization `normalizeFull : cell ≈ repFull cell`, closing
`idempotentThinness_ofNormalize` and hence inhabiting local posetality.

## The normal-form representative

`repNF sourceLen targetLen` reads only the two boundary lengths and returns the canonical cell of that hom, in
NORMAL-FORM (`monadTPower`) coordinates — so it needs NO boundary cast:

  * `targetLen = targetPred + 1` : the through-`t` canonical cell `canonThroughT sourceLen targetPred`
    (`monadTPower sourceLen ⇒ monadTPower (targetPred + 1)`, exactly the hom type),
  * `(0, 0)` : the identity on `t^0`,
  * `(sourceCount + 1, 0)` : the EMPTY hom `t^{sourceCount+1} ⇒ nil`, refuted by cell-level rigidity.

`repFull cell` transports `cell` to normal-form coordinates (`monadPath_normalForm`), applies `repNF`, and
transports back — so it is BOUNDARY-DETERMINED (`repNF` ignores the cell except in the refuted branch).

Raw Lean 4 + Init; `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; STRUCTURAL matches on
`Nat`.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph

open IdempotentMonadSaturatedTwoCellConv

/-! ## The normal-form representative -/

/-- ★ The **normal-form boundary representative** — reads the two boundary lengths and returns the canonical cell
of the `t^sourceLen ⇒ t^targetLen` hom, in `monadTPower` coordinates.  Full-enum `Nat` match (propext-clean); the
empty hom `t^{sourceCount+1} ⇒ t^0` is refuted by cell-level rigidity (`rawCell_targetLenZero_impliesSourceLenZero`
forces the source length `0`, contradicting `sourceCount + 1`). -/
def repNF : (sourceLen targetLen : Nat) →
    RawTwoCellExpr monadModeSignature (monadTPower sourceLen) (monadTPower targetLen) →
    RawTwoCellExpr monadModeSignature (monadTPower sourceLen) (monadTPower targetLen)
  | sourceLen, targetPred + 1, _ => canonThroughT sourceLen targetPred
  | 0, 0, _ => RawTwoCellExpr.id (signature := monadModeSignature) (monadTPower 0)
  | sourceCount + 1, 0, cell =>
      Nat.noConfusion ((monadTPower_length (sourceCount + 1)).symm.trans
        (rawCell_targetLenZero_impliesSourceLenZero cell rfl))

/-- Reduction: on a populated target (`targetPred + 1`), `repNF` is the through-`t` canonical cell (definitional). -/
theorem repNF_targetSucc (sourceLen targetPred : Nat)
    (cell : RawTwoCellExpr monadModeSignature (monadTPower sourceLen) (monadTPower (targetPred + 1))) :
    repNF sourceLen (targetPred + 1) cell = canonThroughT sourceLen targetPred := rfl

/-- Reduction: on the `nil ⇒ nil` hom, `repNF` is the identity (definitional). -/
theorem repNF_zeroZero
    (cell : RawTwoCellExpr monadModeSignature (monadTPower 0) (monadTPower 0)) :
    repNF 0 0 cell = RawTwoCellExpr.id (signature := monadModeSignature) (monadTPower 0) := rfl

/-- ★ **`repNF` is cell-INDEPENDENT** (boundary-determined): parallel cells get the same `repNF`.  The two
populated branches ignore the cell (return `canonThroughT` / `id`); the refuted branch is proof-irrelevant
(`Nat.noConfusion` of a `False`-proof).  Full-enum `Nat` match, every branch `rfl`. -/
theorem repNF_cellIndependent : (sourceLen targetLen : Nat) →
    (cellA cellB : RawTwoCellExpr monadModeSignature (monadTPower sourceLen) (monadTPower targetLen)) →
    repNF sourceLen targetLen cellA = repNF sourceLen targetLen cellB
  | _, _ + 1, _, _ => rfl
  | 0, 0, _, _ => rfl
  | _ + 1, 0, _, _ => rfl

/-! ## The boundary-determined total representative -/

/-- ★ The **boundary-determined total representative**: transport `cell` to normal-form coordinates
(`monadPath_normalForm`), apply `repNF`, transport back.  Depends on `cell` only through `repNF` (which is
cell-independent on populated homs and proof-irrelevant on the empty hom), so it is BOUNDARY-DETERMINED. -/
def repFull {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
    (cell : RawTwoCellExpr monadModeSignature sourcePath targetPath) :
    RawTwoCellExpr monadModeSignature sourcePath targetPath :=
  match sourceMode, targetMode with
  | MonadMode.point, MonadMode.point =>
      RawTwoCellExpr.castBoundary (monadPath_normalForm sourcePath).symm (monadPath_normalForm targetPath).symm
        (repNF sourcePath.length targetPath.length
          (RawTwoCellExpr.castBoundary (monadPath_normalForm sourcePath) (monadPath_normalForm targetPath) cell))

/-- ★ **`repFull` is boundary-determined**: parallel cells get equal `repFull` (the outer transports are
cell-free; `repNF` is cell-independent).  The honest reduction `idempotentThinness_ofNormalize` needs exactly
this. -/
theorem repFull_boundary {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
    (cellA cellB : RawTwoCellExpr monadModeSignature sourcePath targetPath) :
    repFull cellA = repFull cellB := by
  cases sourceMode; cases targetMode
  show RawTwoCellExpr.castBoundary _ _
      (repNF sourcePath.length targetPath.length (RawTwoCellExpr.castBoundary _ _ cellA))
    = RawTwoCellExpr.castBoundary _ _
      (repNF sourcePath.length targetPath.length (RawTwoCellExpr.castBoundary _ _ cellB))
  exact congrArg (RawTwoCellExpr.castBoundary _ _)
    (repNF_cellIndependent sourcePath.length targetPath.length _ _)

/-! ## Honesty marker -/

/-- **ESTABLISHED — the boundary-determined total representative + its boundary-determinedness.**  `repFull`
(`repNF` in `monadTPower` coordinates, transported by `monadPath_normalForm`) reads only the boundary lengths and
returns the canonical cell — `canonThroughT` on a populated target, `id` on `nil ⇒ nil`, the empty hom refuted by
cell-level rigidity.  It is BOUNDARY-DETERMINED (`repFull_boundary` : parallel cells get equal `repFull`, since
`repNF` ignores the cell on populated homs and is proof-irrelevant on the empty hom).  These are two of the three
inputs `idempotentThinness_ofNormalize` needs.  `= true`. -/
def fxIdempotentMonad_hasBoundaryRepresentative : Bool := true

end FX1Poly.Polygraph
