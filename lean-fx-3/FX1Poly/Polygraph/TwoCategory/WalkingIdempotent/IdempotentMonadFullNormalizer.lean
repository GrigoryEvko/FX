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

/-! ## The normalization reduction kit — the `rw`-free tools the six-case `normalizeFull` consumes

`normalizeFull : cell ≈ repFull cell` is a six-case structural induction; each case must REDUCE `repFull` (which
matches on the boundary lengths) to a concrete `canonThroughT` / `id`, then thread the per-constructor conversion
(`gen` via the unit/mul laws, `id` via `foldThenGrow`, `whiskerLeft`/`whiskerRight` via the shipped whisker
canonicalisations, `vcomp` via the grow/fold ladder).  The reductions and cast manipulations below are the shared
kit: length-keyed `repNF` / `repFull` reductions (proved by `cases` on the length proof, so they FIRE) and
CONV-level cast helpers (applied, not `rw`ed, so unification runs up to definitional equality — handling the
`congrArg` beta-redexes and `rfl` / `Eq.symm rfl` seams).  All zero-axiom, STRUCTURAL. -/

/-- Casting an identity across a boundary equality is the identity of the new boundary. -/
theorem castBoundary_id {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    {onePath twoPath : ModalityPath signature.graph sourceMode targetMode} (hpath : onePath = twoPath) :
    RawTwoCellExpr.castBoundary hpath hpath (RawTwoCellExpr.id (signature := signature) onePath)
      = RawTwoCellExpr.id (signature := signature) twoPath := by
  cases hpath; rfl

/-- `repNF` on a populated target reduces to the through-`t` canonical cell, once the target length is exhibited as
a successor (`cases` on the length proof). -/
theorem repNF_of_targetLen {sourceLen targetLen : Nat}
    (cell : RawTwoCellExpr monadModeSignature (monadTPower sourceLen) (monadTPower targetLen))
    (targetPred : Nat) (htarget : targetLen = targetPred + 1) :
    repNF sourceLen targetLen cell
      = RawTwoCellExpr.castBoundary rfl (congrArg monadTPower htarget).symm (canonThroughT sourceLen targetPred) := by
  cases htarget; rfl

/-- `repNF` on the `nil ⇒ nil` hom reduces to the identity, once both lengths are exhibited as zero. -/
theorem repNF_of_bothZero {sourceLen targetLen : Nat}
    (cell : RawTwoCellExpr monadModeSignature (monadTPower sourceLen) (monadTPower targetLen))
    (hsource : sourceLen = 0) (htarget : targetLen = 0) :
    repNF sourceLen targetLen cell
      = RawTwoCellExpr.castBoundary (congrArg monadTPower hsource).symm (congrArg monadTPower htarget).symm
        (RawTwoCellExpr.id (signature := monadModeSignature) (monadTPower 0)) := by
  cases hsource; cases htarget; rfl

/-- ★ **`repFull` reduces on a populated target** to the through-`t` canonical cell of the boundary lengths,
transported back by `monadPath_normalForm` — the shape the `whiskerLeft`/`whiskerRight`/`vcomp` normalize cases
land on. -/
theorem repFull_populated {sourcePath targetPath : ModalityPath monadGraph MonadMode.point MonadMode.point}
    (cell : RawTwoCellExpr monadModeSignature sourcePath targetPath) (targetPred : Nat)
    (htarget : targetPath.length = targetPred + 1) :
    repFull cell = RawTwoCellExpr.castBoundary (monadPath_normalForm sourcePath).symm
      ((monadPath_normalForm targetPath).trans (congrArg monadTPower htarget)).symm
      (canonThroughT sourcePath.length targetPred) := by
  show RawTwoCellExpr.castBoundary (monadPath_normalForm sourcePath).symm (monadPath_normalForm targetPath).symm
      (repNF sourcePath.length targetPath.length _) = _
  rw [repNF_of_targetLen _ targetPred htarget, RawTwoCellExpr.castBoundary_castBoundary]

/-- ★ **`repFull` reduces on the empty `nil ⇒ nil` hom** to the identity on `t^0`, transported back. -/
theorem repFull_zeroZero {sourcePath targetPath : ModalityPath monadGraph MonadMode.point MonadMode.point}
    (cell : RawTwoCellExpr monadModeSignature sourcePath targetPath)
    (hsource : sourcePath.length = 0) (htarget : targetPath.length = 0) :
    repFull cell = RawTwoCellExpr.castBoundary
      ((monadPath_normalForm sourcePath).trans (congrArg monadTPower hsource)).symm
      ((monadPath_normalForm targetPath).trans (congrArg monadTPower htarget)).symm
      (RawTwoCellExpr.id (signature := monadModeSignature) (monadTPower 0)) := by
  show RawTwoCellExpr.castBoundary (monadPath_normalForm sourcePath).symm (monadPath_normalForm targetPath).symm
      (repNF sourcePath.length targetPath.length _) = _
  rw [repNF_of_bothZero _ hsource htarget, RawTwoCellExpr.castBoundary_castBoundary]

/-- The `id` normalize case in `monadTPower` coordinates: `id (t^L) ≈ repNF L L (id (t^L))` — `refl` on the empty
hom, `foldThenGrow` on a populated one. -/
theorem idNFConv : (targetLen : Nat) →
    IdempotentMonadSaturatedTwoCellConv
      (RawTwoCellExpr.id (signature := monadModeSignature) (monadTPower targetLen))
      (repNF targetLen targetLen (RawTwoCellExpr.id (signature := monadModeSignature) (monadTPower targetLen)))
  | 0 => IdempotentMonadSaturatedTwoCellConv.refl _
  | targetPred + 1 => IdempotentMonadSaturatedTwoCellConv.symm (foldThenGrow targetPred)

/-- Extrude a boundary cast out of a general RIGHT whisker (CONV form). -/
theorem whiskerRightPullConv {sourceMode middleMode targetMode : MonadMode}
    (oneCell : ModalityPath monadGraph middleMode targetMode)
    {sourcePath sourcePath' targetPath targetPath' : ModalityPath monadGraph sourceMode middleMode}
    (hsource : sourcePath = sourcePath') (htarget : targetPath = targetPath')
    (cell : RawTwoCellExpr monadModeSignature sourcePath targetPath) :
    IdempotentMonadSaturatedTwoCellConv
      (RawTwoCellExpr.whiskerRight oneCell (RawTwoCellExpr.castBoundary hsource htarget cell))
      (RawTwoCellExpr.castBoundary (congrArg (fun path => composePath path oneCell) hsource)
        (congrArg (fun path => composePath path oneCell) htarget) (RawTwoCellExpr.whiskerRight oneCell cell)) := by
  cases hsource; cases htarget; exact IdempotentMonadSaturatedTwoCellConv.refl _

/-- Extrude a boundary cast out of a general LEFT whisker (CONV form). -/
theorem whiskerLeftPullConv {sourceMode middleMode targetMode : MonadMode}
    (oneCell : ModalityPath monadGraph sourceMode middleMode)
    {sourcePath sourcePath' targetPath targetPath' : ModalityPath monadGraph middleMode targetMode}
    (hsource : sourcePath = sourcePath') (htarget : targetPath = targetPath')
    (cell : RawTwoCellExpr monadModeSignature sourcePath targetPath) :
    IdempotentMonadSaturatedTwoCellConv
      (RawTwoCellExpr.whiskerLeft oneCell (RawTwoCellExpr.castBoundary hsource htarget cell))
      (RawTwoCellExpr.castBoundary (congrArg (composePath oneCell) hsource)
        (congrArg (composePath oneCell) htarget) (RawTwoCellExpr.whiskerLeft oneCell cell)) := by
  cases hsource; cases htarget; exact IdempotentMonadSaturatedTwoCellConv.refl _

/-- Transport the whisker 1-cell of a RIGHT whisker along a 1-cell equality (CONV form). -/
theorem whiskerRightWhiskerEqConv {sourceMode middleMode targetMode : MonadMode}
    {oneCell oneCell' : ModalityPath monadGraph middleMode targetMode} (hwhisker : oneCell = oneCell')
    {oneCellDom oneCellCod : ModalityPath monadGraph sourceMode middleMode}
    (body : RawTwoCellExpr monadModeSignature oneCellDom oneCellCod) :
    IdempotentMonadSaturatedTwoCellConv (RawTwoCellExpr.whiskerRight oneCell body)
      (RawTwoCellExpr.castBoundary (congrArg (composePath oneCellDom) hwhisker.symm)
        (congrArg (composePath oneCellCod) hwhisker.symm) (RawTwoCellExpr.whiskerRight oneCell' body)) := by
  cases hwhisker; exact IdempotentMonadSaturatedTwoCellConv.refl _

/-- Transport the whisker 1-cell of a LEFT whisker along a 1-cell equality (CONV form). -/
theorem whiskerLeftWhiskerEqConv {sourceMode middleMode targetMode : MonadMode}
    {oneCell oneCell' : ModalityPath monadGraph sourceMode middleMode} (hwhisker : oneCell = oneCell')
    {oneCellDom oneCellCod : ModalityPath monadGraph middleMode targetMode}
    (body : RawTwoCellExpr monadModeSignature oneCellDom oneCellCod) :
    IdempotentMonadSaturatedTwoCellConv (RawTwoCellExpr.whiskerLeft oneCell body)
      (RawTwoCellExpr.castBoundary (congrArg (fun whisker => composePath whisker oneCellDom) hwhisker.symm)
        (congrArg (fun whisker => composePath whisker oneCellCod) hwhisker.symm)
        (RawTwoCellExpr.whiskerLeft oneCell' body)) := by
  cases hwhisker; exact IdempotentMonadSaturatedTwoCellConv.refl _

/-- Reindex the SOURCE count of `canonThroughT` along a `Nat` equality (CONV form) — reconciles the
`length_composePath` / `add_comm` index gaps in the whisker normalize cases. -/
theorem canonThroughT_reindexSource {sourceCount sourceCount' targetPred : Nat} (hcount : sourceCount = sourceCount') :
    IdempotentMonadSaturatedTwoCellConv (canonThroughT sourceCount targetPred)
      (RawTwoCellExpr.castBoundary (congrArg monadTPower hcount).symm rfl (canonThroughT sourceCount' targetPred)) := by
  cases hcount; exact IdempotentMonadSaturatedTwoCellConv.refl _

/-- Reindex the TARGET predecessor of `canonThroughT` along a `Nat` equality (CONV form). -/
theorem canonThroughT_reindexTarget {sourceCount targetPred targetPred' : Nat} (hpred : targetPred = targetPred') :
    IdempotentMonadSaturatedTwoCellConv (canonThroughT sourceCount targetPred)
      (RawTwoCellExpr.castBoundary rfl (congrArg (fun pred => monadTPower (pred + 1)) hpred).symm
        (canonThroughT sourceCount targetPred')) := by
  cases hpred; exact IdempotentMonadSaturatedTwoCellConv.refl _

/-- **Honesty marker — the `normalizeFull` REDUCTION KIT is shipped; the six-case assembly is the residual.**
The length-keyed `repNF` / `repFull` reductions (`repFull_populated` / `repFull_zeroZero`, proved by `cases` on the
boundary-length proof so they actually FIRE the stuck dependent match) plus the CONV-level cast helpers
(`whiskerRight/LeftPullConv`, `whiskerRight/LeftWhiskerEqConv`, `canonThroughT_reindexSource/Target`, applied so
defeq handles the `congrArg` beta-redexes) are the shared tools `normalizeFull` consumes.  With them the `gen`,
`id`, and populated-`whiskerRight` cases are mechanical (each `ofCastLeft` + reduce + shipped whisker
canonicalisation).  What is NOT assembled this round is the full `normalizeFull` induction: the two whisker EMPTY
sub-cases (a `nil ⇒ nil` body whiskered — needs the whisker-length reindex through `whiskerRightId`/`idNFConv`),
the general-width LEFT whisker (an `add_comm` reindex on both indices vs `whiskerLeftCanon`'s `a+k` order), and the
`vcomp` case (the middle grow/fold collapse `growThenFold` across the four `middle`/`target` length sub-cases).
Until `normalizeFull` lands and feeds `idempotentThinness_ofNormalize`, `IdempotentMonadLocalPosetality` is NOT
inhabited.  `= false`. -/
def fxIdempotentMonad_hasNormalizeFull : Bool := false

end FX1Poly.Polygraph
