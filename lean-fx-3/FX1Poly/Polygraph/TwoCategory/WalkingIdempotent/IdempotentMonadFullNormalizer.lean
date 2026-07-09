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

/-- ★ **The vcomp middle-collapse crux** — `canonThroughT s g ∘ canonThroughT (g+1) h ≈ canonThroughT s h`.  Two
through-`t` canonical cells compose to the through-`t` canonical of the outer boundary: the inner grow tower
`growTower g` (up to `t^{g+1}`) meets the fold `monadGadget (g+1)` and the round-trip collapses by `growThenFold g`
(the mu-iso grow/fold ladder), leaving `monadGadget s ∘ growTower h = canonThroughT s h`.  The mathematical heart
of the `vcomp` normalize case (in `monadTPower` coordinates), zero-axiom. -/
theorem vcompCanonCollapse (sourceLen middlePred targetPred : Nat) :
    IdempotentMonadSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp (canonThroughT sourceLen middlePred) (canonThroughT (middlePred + 1) targetPred))
      (canonThroughT sourceLen targetPred) := by
  show IdempotentMonadSaturatedTwoCellConv
    (RawTwoCellExpr.vcomp (RawTwoCellExpr.vcomp (monadGadget sourceLen) (growTower middlePred))
      (RawTwoCellExpr.vcomp (monadGadget (middlePred + 1)) (growTower targetPred)))
    (RawTwoCellExpr.vcomp (monadGadget sourceLen) (growTower targetPred))
  refine trans (idempotentConvOfStep (TwoCellStep.vcompAssoc (monadGadget sourceLen) (growTower middlePred)
    (RawTwoCellExpr.vcomp (monadGadget (middlePred + 1)) (growTower targetPred)))) ?_
  refine trans (vcompCongrRight (monadGadget sourceLen)
    (symm (idempotentConvOfStep (TwoCellStep.vcompAssoc (growTower middlePred) (monadGadget (middlePred + 1))
      (growTower targetPred))))) ?_
  refine trans (vcompCongrRight (monadGadget sourceLen)
    (vcompCongrLeft (growTower targetPred) (growThenFold middlePred))) ?_
  refine trans (vcompCongrRight (monadGadget sourceLen)
    (idempotentConvOfStep (TwoCellStep.vcompIdLeft (growTower targetPred)))) ?_
  exact IdempotentMonadSaturatedTwoCellConv.refl _

/-! ## The six-case assembly `normalizeFull : cell ≈ repFull cell`

`normalizeFull` is assembled at the CELL level: each constructor recomposes the boundary-canonical
representatives of its children (`repFull child`, unfolded DEFINITIONALLY so the shared `monadPath_normalForm`
seams line up) through a free-`Nat` COLLAPSE lemma (the `vcomp` middle-collapse `repNFVcompCollapse`, the whisker
canonicalisations `repNFWhiskerLeftBrick` / `repNFWhiskerRightBrick`), then transports back.  The collapse lemmas
are over FREE `Nat` boundary lengths, so their internal case splits (`0` vs successor — the whisker-EMPTY vs
populated sub-cases) run on genuine variables, discharging the empty homs by cell-level rigidity
(`rawCell_targetLenZero_impliesSourceLenZero`).  All zero-axiom, STRUCTURAL. -/

/-- `repFull` in point-to-point coordinates unfolds definitionally to its `monadPath_normalForm`-transported
`repNF` body.  Stated as an `rfl` so the recomposition lemmas can `rw` the outer transports open and match the
shared `monadPath_normalForm` seams. -/
theorem repFull_def {sourcePath targetPath : ModalityPath monadGraph MonadMode.point MonadMode.point}
    (cell : RawTwoCellExpr monadModeSignature sourcePath targetPath) :
    repFull cell = RawTwoCellExpr.castBoundary (monadPath_normalForm sourcePath).symm
      (monadPath_normalForm targetPath).symm
      (repNF sourcePath.length targetPath.length
        (RawTwoCellExpr.castBoundary (monadPath_normalForm sourcePath) (monadPath_normalForm targetPath) cell)) :=
  rfl

/-- ★ **The `vcomp` middle-collapse in `monadTPower` coordinates** — over FREE `Nat` boundary lengths.  Two
boundary-canonical cells `repNF Fl Gl cA` and `repNF Gl Hl cB` compose to the boundary-canonical of the outer
`Fl ⇒ Hl` hom.  Case split on the middle length `Gl` (and the endpoints): both populated ⇒ `vcompCanonCollapse`;
empty middle ⇒ `vcompIdLeft`; the `t^{≥1} ⇒ t^0` empty homs are refuted by cell-level rigidity. -/
theorem repNFVcompCollapse : (Fl Gl Hl : Nat) →
    (cA : RawTwoCellExpr monadModeSignature (monadTPower Fl) (monadTPower Gl)) →
    (cB : RawTwoCellExpr monadModeSignature (monadTPower Gl) (monadTPower Hl)) →
    IdempotentMonadSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp (repNF Fl Gl cA) (repNF Gl Hl cB))
      (repNF Fl Hl (RawTwoCellExpr.vcomp cA cB))
  | Fl, 0, Hl, cA, cB => by
      cases Fl with
      | succ fp =>
          exact absurd (rawCell_targetLenZero_impliesSourceLenZero cA rfl)
            (fun hlen => Nat.noConfusion ((monadTPower_length (fp + 1)).symm.trans hlen))
      | zero =>
          refine IdempotentMonadSaturatedTwoCellConv.trans (idempotentConvOfStep (TwoCellStep.vcompIdLeft (repNF 0 Hl cB))) ?_
          rw [repNF_cellIndependent 0 Hl cB (RawTwoCellExpr.vcomp cA cB)]
          exact IdempotentMonadSaturatedTwoCellConv.refl _
  | Fl, gp + 1, Hl, cA, cB => by
      cases Hl with
      | zero =>
          exact absurd (rawCell_targetLenZero_impliesSourceLenZero cB rfl)
            (fun hlen => Nat.noConfusion ((monadTPower_length (gp + 1)).symm.trans hlen))
      | succ hp =>
          exact vcompCanonCollapse Fl gp hp

/-- ★ **The general-width LEFT-whisker canonicalisation in `monadTPower` coordinates** — over FREE `Nat` boundary
lengths.  `t^k ◁ (repNF G H X) ≈ (transported) repNF (k+G) (k+H) W`.  Populated body ⇒ `whiskerLeftCanon` with the
`add_comm` reindex (`canonThroughT_reindexSource`/`Target`); empty body (`H = 0` forces `G = 0` by rigidity) ⇒
`whiskerLeftId` + `idNFConv`.  The `W` argument is any parallel cell — `repNF` reads only the boundary. -/
theorem repNFWhiskerLeftBrick : (k G H : Nat) →
    (X : RawTwoCellExpr monadModeSignature (monadTPower G) (monadTPower H)) →
    (W : RawTwoCellExpr monadModeSignature (monadTPower (k + G)) (monadTPower (k + H))) →
    IdempotentMonadSaturatedTwoCellConv
      (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) (monadTPower k) (repNF G H X))
      (RawTwoCellExpr.castBoundary (monadTPower_add k G) (monadTPower_add k H) (repNF (k + G) (k + H) W))
  | k, G, hp + 1, X, W => by
      refine IdempotentMonadSaturatedTwoCellConv.trans (whiskerLeftCanon k G hp) ?_
      refine IdempotentMonadSaturatedTwoCellConv.trans (castBoundaryCongr _ _ (canonThroughT_reindexSource (Nat.add_comm G k))) ?_
      refine IdempotentMonadSaturatedTwoCellConv.trans (castBoundaryCongr _ _
        (castBoundaryCongr _ _ (canonThroughT_reindexTarget (Nat.add_comm hp k)))) ?_
      refine IdempotentMonadSaturatedTwoCellConv.trans (castBoundaryCongr _ _ (castChainCollapseConv _ _ _ _ _)) ?_
      refine IdempotentMonadSaturatedTwoCellConv.trans (castChainCollapseConv _ _ _ _ _) ?_
      exact IdempotentMonadSaturatedTwoCellConv.refl _
  | k, G, 0, X, W => by
      have hG0 : G = 0 := (monadTPower_length G).symm.trans (rawCell_targetLenZero_impliesSourceLenZero X rfl)
      subst hG0
      show IdempotentMonadSaturatedTwoCellConv
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) (monadTPower k)
          (RawTwoCellExpr.id (signature := monadModeSignature) (monadTPower 0)))
        (RawTwoCellExpr.castBoundary (monadTPower_add k 0) (monadTPower_add k 0) (repNF (k + 0) (k + 0) W))
      refine IdempotentMonadSaturatedTwoCellConv.trans
        (idempotentConvOfStep
          (TwoCellStep.whiskerLeftId (signature := monadModeSignature) (monadTPower k) (monadTPower 0))) ?_
      rw [repNF_cellIndependent (k + 0) (k + 0) W
        (RawTwoCellExpr.id (signature := monadModeSignature) (monadTPower (k + 0)))]
      refine IdempotentMonadSaturatedTwoCellConv.trans ?_
        (castBoundaryCongr _ _ (idNFConv (k + 0)))
      rw [castBoundary_id (monadTPower_add k 0)]
      exact IdempotentMonadSaturatedTwoCellConv.refl _

/-- ★ **The general-width RIGHT-whisker canonicalisation in `monadTPower` coordinates** — over FREE `Nat` boundary
lengths.  `(repNF G H X) ▷ t^k ≈ (transported) repNF (G+k) (H+k) W`.  Populated body ⇒ `whiskerRightCanon` (the
target length `(hp+1)+k` re-expressed as `(hp+k)+1` by `repNF_of_targetLen` + `Nat.succ_add`, the casts fusing by
proof irrelevance); empty body ⇒ `whiskerRightId` + `idNFConv`. -/
theorem repNFWhiskerRightBrick : (k G H : Nat) →
    (X : RawTwoCellExpr monadModeSignature (monadTPower G) (monadTPower H)) →
    (W : RawTwoCellExpr monadModeSignature (monadTPower (G + k)) (monadTPower (H + k))) →
    IdempotentMonadSaturatedTwoCellConv
      (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower k) (repNF G H X))
      (RawTwoCellExpr.castBoundary (monadTPower_add G k) (monadTPower_add H k) (repNF (G + k) (H + k) W))
  | k, G, hp + 1, X, W => by
      refine IdempotentMonadSaturatedTwoCellConv.trans (whiskerRightCanon k G hp) ?_
      rw [repNF_of_targetLen W (hp + k) (Nat.succ_add hp k), RawTwoCellExpr.castBoundary_castBoundary]
      exact IdempotentMonadSaturatedTwoCellConv.refl _
  | k, G, 0, X, W => by
      have hG0 : G = 0 := (monadTPower_length G).symm.trans (rawCell_targetLenZero_impliesSourceLenZero X rfl)
      subst hG0
      show IdempotentMonadSaturatedTwoCellConv
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower k)
          (RawTwoCellExpr.id (signature := monadModeSignature) (monadTPower 0)))
        (RawTwoCellExpr.castBoundary (monadTPower_add 0 k) (monadTPower_add 0 k) (repNF (0 + k) (0 + k) W))
      refine IdempotentMonadSaturatedTwoCellConv.trans
        (idempotentConvOfStep
          (TwoCellStep.whiskerRightId (signature := monadModeSignature) (monadTPower 0) (monadTPower k))) ?_
      rw [repNF_cellIndependent (0 + k) (0 + k) W
        (RawTwoCellExpr.id (signature := monadModeSignature) (monadTPower (0 + k)))]
      refine IdempotentMonadSaturatedTwoCellConv.trans ?_
        (castBoundaryCongr _ _ (idNFConv (0 + k)))
      rw [castBoundary_id (monadTPower_add 0 k)]
      exact IdempotentMonadSaturatedTwoCellConv.refl _

/-- Transport `repNF` along `Nat` boundary-length equalities (`cases` both, then `rfl`).  The whisker `normalizeFull`
cases bridge the stuck `(composePath oc gg).length` against the brick's `oc.length + gg.length`. -/
theorem repNF_lengthCast {sourceLen sourceLen' targetLen targetLen' : Nat}
    (hsource : sourceLen = sourceLen') (htarget : targetLen = targetLen')
    (cell : RawTwoCellExpr monadModeSignature (monadTPower sourceLen) (monadTPower targetLen)) :
    repNF sourceLen targetLen cell
      = RawTwoCellExpr.castBoundary (congrArg monadTPower hsource).symm (congrArg monadTPower htarget).symm
        (repNF sourceLen' targetLen'
          (RawTwoCellExpr.castBoundary (congrArg monadTPower hsource) (congrArg monadTPower htarget) cell)) := by
  cases hsource; cases htarget; rfl

/-- Convert a `Conv cell (repFull cell)` result into `monadTPower`-coordinate NF form (the inverse of `ofCastLeft`,
via `castBoundaryCongr` + the round-trip cast cancellation).  The `vcomp` recomposition consumes the children's
recursive results in this NF form. -/
theorem toNF {sourcePath targetPath : ModalityPath monadGraph MonadMode.point MonadMode.point}
    {cell : RawTwoCellExpr monadModeSignature sourcePath targetPath}
    (conv : IdempotentMonadSaturatedTwoCellConv cell (repFull cell)) :
    IdempotentMonadSaturatedTwoCellConv
      (RawTwoCellExpr.castBoundary (monadPath_normalForm sourcePath) (monadPath_normalForm targetPath) cell)
      (repNF sourcePath.length targetPath.length
        (RawTwoCellExpr.castBoundary (monadPath_normalForm sourcePath) (monadPath_normalForm targetPath) cell)) := by
  have hcongr := castBoundaryCongr (monadPath_normalForm sourcePath) (monadPath_normalForm targetPath) conv
  rw [repFull_def cell, RawTwoCellExpr.castBoundary_castBoundary] at hcongr
  exact hcongr

/-- ★★ **`normalizeFull`** — every free 2-cell is convertible to its boundary-determined representative
`repFull cell`.  MODE-GENERIC structural recursion over `RawTwoCellExpr` (binder-form mode indices — no partial
index match, so `propext`/`Quot.sound`-free), each arm making its recursive calls BEFORE resolving the (unique)
mode to `point`: `gen` bases (unit / mul chases, casts strip on the concrete boundaries), `id` (`idNFConv`),
`vcomp` (`vcompCastMergeConv` decompose + `repNFVcompCollapse` on the children's `toNF` results), the two whiskers
(`repNFWhiskerLeft`/`RightBrick` after re-expressing the whisker 1-cell as `monadTPower oc.length`, the
`length_composePath` boundary bridged by `repNF_lengthCast`).  Feeds `idempotentThinness_ofNormalize`. -/
theorem normalizeFull :
    {sourceMode targetMode : MonadMode} →
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode} →
    (cell : RawTwoCellExpr monadModeSignature sourcePath targetPath) →
    IdempotentMonadSaturatedTwoCellConv cell (repFull cell)
  | _, _, _, _, .gen MonadTwoCell.eta =>
      IdempotentMonadSaturatedTwoCellConv.symm
        (idempotentConvOfStep (TwoCellStep.vcompIdRight monadUnitTwoCell))
  | _, _, _, _, .gen MonadTwoCell.mu => by
      refine IdempotentMonadSaturatedTwoCellConv.trans
        (IdempotentMonadSaturatedTwoCellConv.symm
          (idempotentConvOfStep (TwoCellStep.vcompIdLeft monadMulTwoCell))) ?_
      refine IdempotentMonadSaturatedTwoCellConv.trans
        (vcompCongrLeft monadMulTwoCell
          (IdempotentMonadSaturatedTwoCellConv.symm
            (idempotentConvOfStep
              (TwoCellStep.whiskerLeftId (signature := monadModeSignature) monadT monadT)))) ?_
      exact IdempotentMonadSaturatedTwoCellConv.symm
        (idempotentConvOfStep (TwoCellStep.vcompIdRight (monadGadget 2)))
  | smode, tmode, _, _, .id path => by
      cases smode; cases tmode
      exact IdempotentMonadSaturatedTwoCellConv.ofCastLeft
        (monadPath_normalForm path) (monadPath_normalForm path)
        (by rw [castBoundary_id (monadPath_normalForm path)]; exact idNFConv path.length)
  | smode, tmode, _, _, .vcomp a b => by
      have iha := normalizeFull a
      have ihb := normalizeFull b
      cases smode; cases tmode
      refine IdempotentMonadSaturatedTwoCellConv.ofCastLeft
        (monadPath_normalForm _) (monadPath_normalForm _) ?_
      refine IdempotentMonadSaturatedTwoCellConv.trans
        (IdempotentMonadSaturatedTwoCellConv.symm
          (vcompCastMergeConv (monadPath_normalForm _) (monadPath_normalForm _)
            (monadPath_normalForm _) a b)) ?_
      refine IdempotentMonadSaturatedTwoCellConv.trans
        (IdempotentMonadSaturatedTwoCellConv.trans
          (vcompCongrLeft _ (toNF iha)) (vcompCongrRight _ (toNF ihb))) ?_
      refine IdempotentMonadSaturatedTwoCellConv.trans
        (repNFVcompCollapse _ _ _ _ _) ?_
      rw [repNF_cellIndependent _ _
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.castBoundary (monadPath_normalForm _) (monadPath_normalForm _) a)
          (RawTwoCellExpr.castBoundary (monadPath_normalForm _) (monadPath_normalForm _) b))
        (RawTwoCellExpr.castBoundary (monadPath_normalForm _) (monadPath_normalForm _)
          (RawTwoCellExpr.vcomp a b))]
      exact IdempotentMonadSaturatedTwoCellConv.refl _
  | smode, tmode, _, _, @RawTwoCellExpr.whiskerLeft _ _ middleMode _ oc gg hh body => by
      have hBody := normalizeFull body
      cases smode; cases middleMode; cases tmode
      refine IdempotentMonadSaturatedTwoCellConv.ofCastLeft
        (monadPath_normalForm (composePath oc gg)) (monadPath_normalForm (composePath oc hh)) ?_
      have heq := repNF_lengthCast (ModalityPath.length_composePath oc gg)
        (ModalityPath.length_composePath oc hh)
        (RawTwoCellExpr.castBoundary (monadPath_normalForm (composePath oc gg))
          (monadPath_normalForm (composePath oc hh)) (RawTwoCellExpr.whiskerLeft oc body))
      refine heq ▸ ?_
      refine IdempotentMonadSaturatedTwoCellConv.trans (castBoundaryCongr _ _ (whiskerLeftCongr oc hBody)) ?_
      rw [repFull_def body]
      refine IdempotentMonadSaturatedTwoCellConv.trans (castBoundaryCongr _ _ (whiskerLeftPullConv oc _ _ _)) ?_
      refine IdempotentMonadSaturatedTwoCellConv.trans (castBoundaryCongr _ _
        (castBoundaryCongr _ _ (whiskerLeftWhiskerEqConv (monadPath_normalForm oc) _))) ?_
      refine IdempotentMonadSaturatedTwoCellConv.trans (castBoundaryCongr _ _ (castChainCollapseConv _ _ _ _ _)) ?_
      refine IdempotentMonadSaturatedTwoCellConv.trans (castBoundaryCongr _ _
        (castBoundaryCongr _ _ (repNFWhiskerLeftBrick oc.length gg.length hh.length _
          (RawTwoCellExpr.castBoundary (congrArg monadTPower (ModalityPath.length_composePath oc gg))
            (congrArg monadTPower (ModalityPath.length_composePath oc hh))
            (RawTwoCellExpr.castBoundary (monadPath_normalForm (composePath oc gg))
              (monadPath_normalForm (composePath oc hh)) (RawTwoCellExpr.whiskerLeft oc body)))))) ?_
      refine IdempotentMonadSaturatedTwoCellConv.trans (castBoundaryCongr _ _ (castChainCollapseConv _ _ _ _ _)) ?_
      refine IdempotentMonadSaturatedTwoCellConv.trans (castChainCollapseConv _ _ _ _ _) ?_
      exact IdempotentMonadSaturatedTwoCellConv.refl _
  | smode, tmode, _, _, @RawTwoCellExpr.whiskerRight _ _ middleMode _ gg hh oc body => by
      have hBody := normalizeFull body
      cases smode; cases middleMode; cases tmode
      refine IdempotentMonadSaturatedTwoCellConv.ofCastLeft
        (monadPath_normalForm (composePath gg oc)) (monadPath_normalForm (composePath hh oc)) ?_
      have heq := repNF_lengthCast (ModalityPath.length_composePath gg oc)
        (ModalityPath.length_composePath hh oc)
        (RawTwoCellExpr.castBoundary (monadPath_normalForm (composePath gg oc))
          (monadPath_normalForm (composePath hh oc)) (RawTwoCellExpr.whiskerRight oc body))
      refine heq ▸ ?_
      refine IdempotentMonadSaturatedTwoCellConv.trans (castBoundaryCongr _ _ (whiskerRightCongr oc hBody)) ?_
      rw [repFull_def body]
      refine IdempotentMonadSaturatedTwoCellConv.trans (castBoundaryCongr _ _ (whiskerRightPullConv oc _ _ _)) ?_
      refine IdempotentMonadSaturatedTwoCellConv.trans (castBoundaryCongr _ _
        (castBoundaryCongr _ _ (whiskerRightWhiskerEqConv (monadPath_normalForm oc) _))) ?_
      refine IdempotentMonadSaturatedTwoCellConv.trans (castBoundaryCongr _ _ (castChainCollapseConv _ _ _ _ _)) ?_
      refine IdempotentMonadSaturatedTwoCellConv.trans (castBoundaryCongr _ _
        (castBoundaryCongr _ _ (repNFWhiskerRightBrick oc.length gg.length hh.length _
          (RawTwoCellExpr.castBoundary (congrArg monadTPower (ModalityPath.length_composePath gg oc))
            (congrArg monadTPower (ModalityPath.length_composePath hh oc))
            (RawTwoCellExpr.castBoundary (monadPath_normalForm (composePath gg oc))
              (monadPath_normalForm (composePath hh oc)) (RawTwoCellExpr.whiskerRight oc body)))))) ?_
      refine IdempotentMonadSaturatedTwoCellConv.trans (castBoundaryCongr _ _ (castChainCollapseConv _ _ _ _ _)) ?_
      refine IdempotentMonadSaturatedTwoCellConv.trans (castChainCollapseConv _ _ _ _ _) ?_
      exact IdempotentMonadSaturatedTwoCellConv.refl _

/-! ## Inhabiting local posetality + the TOTAL decision -/

/-- ★★ **Local posetality is INHABITED** — the real closed term (zero hypotheses): thinness from the
boundary-determined normalizer `repFull` (`repFull_boundary` + `normalizeFull`), via
`idempotentThinness_ofNormalize`.  Every parallel pair of free 2-cells of the walking idempotent monad is
convertible. -/
def idempotentLocalPosetality : IdempotentMonadLocalPosetality :=
  ⟨idempotentThinness_ofNormalize repFull repFull_boundary normalizeFull⟩

/-- ★★ **The TOTAL walking-idempotent-monad saturated 2-cell decision** — with local posetality now inhabited, the
decision interface is a real closed term deciding EVERY parallel pair (always `isTrue`), zero hypotheses. -/
@[reducible] def decideIdempotentConv : IdempotentMonadDecidableSaturatedTwoCellConvFor :=
  idempotentSaturatedWordProblemModuloPosetality idempotentLocalPosetality

/-- Non-vacuity smoke: a GENUINE `size 4` parallel pair at the hom `t.t ⇒ t.t` — `mu ∘ (eta ▷ t)`
(`vcomp mu (eta ▷ t)`) and its `t ◁ eta` twin `mu ∘ (t ◁ eta)` — is decided TRUE by the TOTAL decision. -/
def idempotentDecidesTrue_smoke : Bool :=
  match decideIdempotentConv (RawTwoCellExpr.vcomp monadMulTwoCell monadEtaTCell)
      (RawTwoCellExpr.vcomp monadMulTwoCell monadTEtaCell) with
  | isTrue _ => true
  | isFalse _ => false

/-- Smoke value: the total decision returns `true` on the genuine `size 4` parallel pair (non-vacuous). -/
theorem idempotentDecidesTrue_smoke_holds : idempotentDecidesTrue_smoke = true := rfl

/-- Non-vacuity: the empty hom still SEPARATES — there is NO free 2-cell `t.t ⇒ nil` (rigidity forces `t.t`'s
length `2 = 0`), so the total decision does not spuriously populate empty homs. -/
theorem idempotentDecision_emptyHom_separates
    (cell : RawTwoCellExpr monadModeSignature monadTThenT
      (ModalityPath.nil (graph := monadGraph) MonadMode.point)) :
    (2 : Nat) = 0 :=
  rawCell_targetLenZero_impliesSourceLenZero cell rfl

/-! ## Honesty marker -/

/-- ★★ **ESTABLISHED — `normalizeFull` + the TOTAL decision.**  Every free 2-cell is convertible to its
boundary-determined representative (`normalizeFull : cell ≈ repFull cell`), the six-case structural NF induction
`NFnorm` transported by `ofCastLeft`: `gen` (unit / mul chases), `id` (`idNFConv`), `vcomp` (`vcompCastMergeConv`
decompose + `repNFVcompCollapse`), the two whiskers (`repNFWhiskerLeft`/`RightBrick` = `whiskerLeftCanon` /
`whiskerRightCanon` + the `add_comm` / `succ_add` reindex + `length_composePath` boundary bridge `repNF_lengthCast`),
the whisker-EMPTY sub-cases discharged by cell-level rigidity.  This feeds `idempotentThinness_ofNormalize` (with
`repFull` / `repFull_boundary`) to inhabit `IdempotentMonadLocalPosetality` as a REAL closed term
(`idempotentLocalPosetality`, zero hypotheses), making `decideIdempotentConv` a TOTAL zero-axiom decision.
Non-vacuous: a `size 4` parallel pair decides `true` (`idempotentDecidesTrue_smoke_holds`) while the empty hom
`t.t ⇒ nil` still separates (`idempotentDecision_emptyHom_separates`).  Closes the walking-idempotent-monad word
problem — the property-like / posetal walker rung DECIDED.  `= true`. -/
def fxIdempotentMonad_hasNormalizeFull : Bool := true

end FX1Poly.Polygraph
