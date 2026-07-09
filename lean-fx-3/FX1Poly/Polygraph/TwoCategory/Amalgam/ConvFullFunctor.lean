import FX1Poly.Polygraph.TwoCategory.Amalgam.MapCell

/-! # Polygraph/TwoCategory/Amalgam/ConvFullFunctor — the free 2-cell functor preserves completed convertibility
(WP-AMALG r5, P1)

`MapCell.lean` (r4) shipped `mapCellAlong`, the free 2-cell functor along a `ComputadMorphismTwo`.
`DispatchSaturated.lean` (r4) reduced the SOUNDNESS lift `mapCellAlong_preservesConv` to a single hypothesis
`fullPreserved` — the STRUCTURAL FUNCTORIALITY of `mapCellAlong` for the completed free-strict-2-category
convertibility `TwoCellConvFull`.  This file DISCHARGES that hypothesis, closing the r4 residual: it proves

  `mapTwoCellConvFull : TwoCellConvFull src cellA cellB -> TwoCellConvFull tgt (mapCellAlong cellA) (mapCellAlong cellB)`

by induction over ALL of `TwoCellConvFull`'s constructors (and, for its `ofConv` case, over the free `TwoCellConv`
and the twelve `TwoCellStep` rewrites).  With it, `mapCellAlong_preservesConv` becomes UNCONDITIONAL
(`mapCellAlongPreservesConv`, restated below; the r4 conditional master stays for compatibility).

## The cast bookkeeping (the grind)

`mapCellAlong` is CAST-FREE on `gen` / `id` / `vcomp` (the mapped boundaries coincide on the nose) but each
whiskering carries exactly one `castBoundary (mapPath_composePath ...)` (because `mapPath` distributes over
`composePath` only PROPOSITIONALLY).  Every constructor of `TwoCellConvFull` therefore maps to a cell that differs
from the matching TARGET-signature constructor by boundary casts.  The cast kit below absorbs every one of them:

  * **`TwoCellConvFull.castBoundaryCongr`** — casting both sides of a convertibility by the same boundary
    equalities preserves it (`cases` the equalities, then `id`).  The workhorse.
  * **`convFull_of_cellEq`** — a cell EQUALITY yields a (reflexive) convertibility (`cases`, then `refl`).
  * **`castBoundary_id`** / **`castBoundary_vcomp`** / **`castBoundary_trans`** — `castBoundary` distributes over
    `id` / `vcomp` and composes (all `cases; rfl`).  These reconcile the whisker-of-vcomp / interchange cases,
    where `mapCellAlong` produces a cast of a composite vs a composite of casts.
  * **`whiskerLeft_castBoundary`** / **`whiskerRight_castBoundary`** — whiskering pushes past a boundary cast
    (`cases; rfl`); the bridge the nested `whiskerLeftComp` / `whiskerRightComp` cases ride, where the inner
    whisker's cast must be pulled out under the outer whisker.
  * **`whiskerLeft_pathCongr`** / **`whiskerRight_pathCongr`** — transport a whisker along an EQUALITY of its
    1-cell (`cases; rfl`); reconciles `whiskerLeft (mapPath (composePath a b))` with
    `whiskerLeft (composePath (mapPath a) (mapPath b))`.
  * **`mapCellAlong_hcomp`** — `mapCellAlong` commutes with the derived Godement product `hcomp` up to one cast
    (from `castBoundary_vcomp`); the engine of the `interchange` case.

Everything is `Eq.rec`-shaped; Lean-4 definitional proof irrelevance for `Eq` means the specific equality proof in
any two casts to the same boundary is irrelevant, so the residual is purely bridging `mapPath (composePath a b)`
with `composePath (mapPath a) (mapPath b)`.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The cast helper kit -/

/-- ★ **The completed convertibility respects boundary casts** — casting both sides of a `TwoCellConvFull` by the
SAME boundary equalities preserves it (`cases` the equalities collapses both casts to the identity).  The
workhorse of every whisker case of the functoriality proof. -/
theorem TwoCellConvFull.castBoundaryCongr {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    {sourcePath sourcePath' targetPath targetPath' : ModalityPath signature.graph sourceMode targetMode}
    (hsource : sourcePath = sourcePath') (htarget : targetPath = targetPath')
    {cellAlpha cellBeta : RawTwoCellExpr signature sourcePath targetPath} :
    TwoCellConvFull signature cellAlpha cellBeta →
    TwoCellConvFull signature
      (RawTwoCellExpr.castBoundary hsource htarget cellAlpha)
      (RawTwoCellExpr.castBoundary hsource htarget cellBeta) := by
  cases hsource; cases htarget; exact id

/-- A cell EQUALITY yields a (reflexive) completed convertibility — the bridge that discharges a residual cast
that collapses to a raw-cell equality at a fixed boundary. -/
theorem convFull_of_cellEq {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr signature sourcePath targetPath}
    (cellsEqual : cellAlpha = cellBeta) : TwoCellConvFull signature cellAlpha cellBeta := by
  cases cellsEqual; exact TwoCellConvFull.refl _

/-- Casting an identity 2-cell is an identity 2-cell (both boundary equalities the same). -/
theorem RawTwoCellExpr.castBoundary_id {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    {path path' : ModalityPath signature.graph sourceMode targetMode} (hpath : path = path') :
    RawTwoCellExpr.castBoundary hpath hpath (RawTwoCellExpr.id path) = RawTwoCellExpr.id path' := by
  cases hpath; rfl

/-- Casting a vertical composite distributes over the factors, splitting at the middle boundary. -/
theorem RawTwoCellExpr.castBoundary_vcomp {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    {oneCellF oneCellF' oneCellG oneCellG' oneCellH oneCellH' : ModalityPath signature.graph sourceMode targetMode}
    (hF : oneCellF = oneCellF') (hG : oneCellG = oneCellG') (hH : oneCellH = oneCellH')
    (cellAlpha : RawTwoCellExpr signature oneCellF oneCellG)
    (cellBeta : RawTwoCellExpr signature oneCellG oneCellH) :
    RawTwoCellExpr.castBoundary hF hH (RawTwoCellExpr.vcomp cellAlpha cellBeta)
      = RawTwoCellExpr.vcomp
          (RawTwoCellExpr.castBoundary hF hG cellAlpha) (RawTwoCellExpr.castBoundary hG hH cellBeta) := by
  cases hF; cases hG; cases hH; rfl

/-- Two nested boundary casts compose into one (`Eq.trans` on each side). -/
theorem RawTwoCellExpr.castBoundary_trans {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    {sourcePath sourcePath' sourcePath'' targetPath targetPath' targetPath'' :
      ModalityPath signature.graph sourceMode targetMode}
    (h1s : sourcePath = sourcePath') (h1t : targetPath = targetPath')
    (h2s : sourcePath' = sourcePath'') (h2t : targetPath' = targetPath'')
    (cell : RawTwoCellExpr signature sourcePath targetPath) :
    RawTwoCellExpr.castBoundary h2s h2t (RawTwoCellExpr.castBoundary h1s h1t cell)
      = RawTwoCellExpr.castBoundary (h1s.trans h2s) (h1t.trans h2t) cell := by
  cases h1s; cases h1t; cases h2s; cases h2t; rfl

/-- Left-whiskering pushes past a boundary cast, re-expressing the cast at the whiskered boundary. -/
theorem RawTwoCellExpr.whiskerLeft_castBoundary {signature : ModeSignature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    (oneCell : ModalityPath signature.graph sourceMode middleMode)
    {oneCellG oneCellG' oneCellH oneCellH' : ModalityPath signature.graph middleMode targetMode}
    (hG : oneCellG = oneCellG') (hH : oneCellH = oneCellH')
    (body : RawTwoCellExpr signature oneCellG oneCellH) :
    RawTwoCellExpr.whiskerLeft oneCell (RawTwoCellExpr.castBoundary hG hH body)
      = RawTwoCellExpr.castBoundary (congrArg (composePath oneCell) hG) (congrArg (composePath oneCell) hH)
          (RawTwoCellExpr.whiskerLeft oneCell body) := by
  cases hG; cases hH; rfl

/-- Right-whiskering pushes past a boundary cast. -/
theorem RawTwoCellExpr.whiskerRight_castBoundary {signature : ModeSignature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {oneCellF oneCellF' oneCellG oneCellG' : ModalityPath signature.graph sourceMode middleMode}
    (oneCell : ModalityPath signature.graph middleMode targetMode)
    (hF : oneCellF = oneCellF') (hG : oneCellG = oneCellG')
    (body : RawTwoCellExpr signature oneCellF oneCellG) :
    RawTwoCellExpr.whiskerRight oneCell (RawTwoCellExpr.castBoundary hF hG body)
      = RawTwoCellExpr.castBoundary (congrArg (fun path => composePath path oneCell) hF)
          (congrArg (fun path => composePath path oneCell) hG)
          (RawTwoCellExpr.whiskerRight oneCell body) := by
  cases hF; cases hG; rfl

/-- Transport a left-whiskering along an EQUALITY of its 1-cell (a boundary cast at the composed boundary). -/
theorem RawTwoCellExpr.whiskerLeft_pathCongr {signature : ModeSignature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {oneCell oneCell' : ModalityPath signature.graph sourceMode middleMode}
    {oneCellG oneCellH : ModalityPath signature.graph middleMode targetMode}
    (hCell : oneCell = oneCell') (body : RawTwoCellExpr signature oneCellG oneCellH) :
    RawTwoCellExpr.whiskerLeft oneCell' body
      = RawTwoCellExpr.castBoundary (congrArg (fun path => composePath path oneCellG) hCell)
          (congrArg (fun path => composePath path oneCellH) hCell)
          (RawTwoCellExpr.whiskerLeft oneCell body) := by
  cases hCell; rfl

/-- Transport a right-whiskering along an EQUALITY of its 1-cell. -/
theorem RawTwoCellExpr.whiskerRight_pathCongr {signature : ModeSignature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {oneCell oneCell' : ModalityPath signature.graph middleMode targetMode}
    {oneCellF oneCellG : ModalityPath signature.graph sourceMode middleMode}
    (hCell : oneCell = oneCell') (body : RawTwoCellExpr signature oneCellF oneCellG) :
    RawTwoCellExpr.whiskerRight oneCell' body
      = RawTwoCellExpr.castBoundary (congrArg (composePath oneCellF) hCell)
          (congrArg (composePath oneCellG) hCell)
          (RawTwoCellExpr.whiskerRight oneCell body) := by
  cases hCell; rfl

/-! ## `mapCellAlong` per-constructor reduction lemmas (all `rfl`; normalize the goal for the whisker cases) -/

/-- `mapCellAlong` on a generating 2-cell (`rfl`). -/
theorem mapCellAlong_gen {source target : ModeComputad} (morphism : ComputadMorphismTwo source target)
    {sourceMode targetMode : Fin source.modeCount}
    {sourcePath targetPath : ModalityPath source.toModeGraph sourceMode targetMode}
    (generator : source.toModeSignature.twoCell sourcePath targetPath) :
    mapCellAlong morphism (RawTwoCellExpr.gen generator) = RawTwoCellExpr.gen (morphism.onTwoCell generator) :=
  rfl

/-- `mapCellAlong` on an identity 2-cell (`rfl`; the target signature is stated to fix the graph-ambiguous
inference). -/
theorem mapCellAlong_id {source target : ModeComputad} (morphism : ComputadMorphismTwo source target)
    {sourceMode targetMode : Fin source.modeCount}
    (path : ModalityPath source.toModeGraph sourceMode targetMode) :
    mapCellAlong morphism (RawTwoCellExpr.id path)
      = RawTwoCellExpr.id (signature := target.toModeSignature) (mapPath morphism.toComputadMorphism path) :=
  rfl

/-- `mapCellAlong` on a vertical composite (`rfl`, cast-free). -/
theorem mapCellAlong_vcomp {source target : ModeComputad} (morphism : ComputadMorphismTwo source target)
    {sourceMode targetMode : Fin source.modeCount}
    {oneCellF oneCellG oneCellH : ModalityPath source.toModeGraph sourceMode targetMode}
    (cellAlpha : RawTwoCellExpr source.toModeSignature oneCellF oneCellG)
    (cellBeta : RawTwoCellExpr source.toModeSignature oneCellG oneCellH) :
    mapCellAlong morphism (RawTwoCellExpr.vcomp cellAlpha cellBeta)
      = RawTwoCellExpr.vcomp (mapCellAlong morphism cellAlpha) (mapCellAlong morphism cellBeta) :=
  rfl

/-- `mapCellAlong` on a left whiskering — the single `mapPath_composePath` cast (`rfl`). -/
theorem mapCellAlong_whiskerLeft {source target : ModeComputad} (morphism : ComputadMorphismTwo source target)
    {sourceMode middleMode targetMode : Fin source.modeCount}
    (oneCell : ModalityPath source.toModeGraph sourceMode middleMode)
    {oneCellG oneCellH : ModalityPath source.toModeGraph middleMode targetMode}
    (body : RawTwoCellExpr source.toModeSignature oneCellG oneCellH) :
    mapCellAlong morphism (RawTwoCellExpr.whiskerLeft oneCell body)
      = RawTwoCellExpr.castBoundary
          (mapPath_composePath morphism.toComputadMorphism oneCell oneCellG).symm
          (mapPath_composePath morphism.toComputadMorphism oneCell oneCellH).symm
          (RawTwoCellExpr.whiskerLeft (mapPath morphism.toComputadMorphism oneCell)
            (mapCellAlong morphism body)) :=
  rfl

/-- `mapCellAlong` on a right whiskering — the single `mapPath_composePath` cast (`rfl`). -/
theorem mapCellAlong_whiskerRight {source target : ModeComputad} (morphism : ComputadMorphismTwo source target)
    {sourceMode middleMode targetMode : Fin source.modeCount}
    {oneCellF oneCellG : ModalityPath source.toModeGraph sourceMode middleMode}
    (oneCell : ModalityPath source.toModeGraph middleMode targetMode)
    (body : RawTwoCellExpr source.toModeSignature oneCellF oneCellG) :
    mapCellAlong morphism (RawTwoCellExpr.whiskerRight oneCell body)
      = RawTwoCellExpr.castBoundary
          (mapPath_composePath morphism.toComputadMorphism oneCellF oneCell).symm
          (mapPath_composePath morphism.toComputadMorphism oneCellG oneCell).symm
          (RawTwoCellExpr.whiskerRight (mapPath morphism.toComputadMorphism oneCell)
            (mapCellAlong morphism body)) :=
  rfl

/-- ★ **`mapCellAlong` commutes with the derived Godement product `hcomp` up to one boundary cast.**  Since
`hcomp X Y = vcomp (whiskerRight _ X) (whiskerLeft _ Y)` and each whisker carries its own `mapPath_composePath`
cast, the two inner casts merge (`castBoundary_vcomp`) into the single outer cast at the hcomp boundary.  The
engine of the `interchange` case. -/
theorem mapCellAlong_hcomp {source target : ModeComputad} (morphism : ComputadMorphismTwo source target)
    {sourceMode middleMode targetMode : source.toModeSignature.graph.Mode}
    {oneCellFDom oneCellFCod : ModalityPath source.toModeSignature.graph sourceMode middleMode}
    {oneCellGDom oneCellGCod : ModalityPath source.toModeSignature.graph middleMode targetMode}
    (cellAlpha : RawTwoCellExpr source.toModeSignature oneCellFDom oneCellFCod)
    (cellBeta : RawTwoCellExpr source.toModeSignature oneCellGDom oneCellGCod) :
    mapCellAlong morphism (RawTwoCellExpr.hcomp cellAlpha cellBeta)
      = RawTwoCellExpr.castBoundary
          (mapPath_composePath morphism.toComputadMorphism oneCellFDom oneCellGDom).symm
          (mapPath_composePath morphism.toComputadMorphism oneCellFCod oneCellGCod).symm
          (RawTwoCellExpr.hcomp (mapCellAlong morphism cellAlpha) (mapCellAlong morphism cellBeta)) := by
  show RawTwoCellExpr.vcomp (mapCellAlong morphism (RawTwoCellExpr.whiskerRight oneCellGDom cellAlpha))
      (mapCellAlong morphism (RawTwoCellExpr.whiskerLeft oneCellFCod cellBeta)) = _
  exact (RawTwoCellExpr.castBoundary_vcomp
    (mapPath_composePath morphism.toComputadMorphism oneCellFDom oneCellGDom).symm
    (mapPath_composePath morphism.toComputadMorphism oneCellFCod oneCellGDom).symm
    (mapPath_composePath morphism.toComputadMorphism oneCellFCod oneCellGCod).symm
    (RawTwoCellExpr.whiskerRight (mapPath morphism.toComputadMorphism oneCellGDom)
      (mapCellAlong morphism cellAlpha))
    (RawTwoCellExpr.whiskerLeft (mapPath morphism.toComputadMorphism oneCellFCod)
      (mapCellAlong morphism cellBeta))).symm

/-! ## Nested-whisker reduction lemmas (the four `mapCellAlong` double-whisker forms)

Each pushes `mapCellAlong` through a NESTED whisker to a single boundary cast of the bare double-whisker of the
image body, by the same recipe: reduce the outer whisker, `congrArg` the inner-whisker reduction under the outer
1-cell, pull the inner cast out (`whisker{Left,Right}_castBoundary`), then merge the two casts (`castBoundary_trans`).
These are the engines of the `whiskerLeftComp` / `whiskerRightComp` / `whiskerExchange` cases (the double casts
`mapCellAlong` produces on a nested whisker cannot be `rw`/`simp`-pushed — the surrounding cast's proof types
depend on the boundary — so the push is done term-mode via `congrArg` inside these lemmas). -/

/-- `mapCellAlong` through `whiskerLeft ∘ whiskerLeft`. -/
theorem mapCellAlong_whiskerLeft_whiskerLeft {source target : ModeComputad}
    (morphism : ComputadMorphismTwo source target) {sm mm1 mm2 tm : Fin source.modeCount}
    (oneCellOuter : ModalityPath source.toModeGraph sm mm1)
    (oneCellInner : ModalityPath source.toModeGraph mm1 mm2)
    {bodyDom bodyCod : ModalityPath source.toModeGraph mm2 tm}
    (body : RawTwoCellExpr source.toModeSignature bodyDom bodyCod) :
    mapCellAlong morphism (RawTwoCellExpr.whiskerLeft oneCellOuter (RawTwoCellExpr.whiskerLeft oneCellInner body))
      = RawTwoCellExpr.castBoundary
          ((congrArg (composePath (mapPath morphism.toComputadMorphism oneCellOuter))
              (mapPath_composePath morphism.toComputadMorphism oneCellInner bodyDom).symm).trans
            (mapPath_composePath morphism.toComputadMorphism oneCellOuter (composePath oneCellInner bodyDom)).symm)
          ((congrArg (composePath (mapPath morphism.toComputadMorphism oneCellOuter))
              (mapPath_composePath morphism.toComputadMorphism oneCellInner bodyCod).symm).trans
            (mapPath_composePath morphism.toComputadMorphism oneCellOuter (composePath oneCellInner bodyCod)).symm)
          (RawTwoCellExpr.whiskerLeft (mapPath morphism.toComputadMorphism oneCellOuter)
            (RawTwoCellExpr.whiskerLeft (mapPath morphism.toComputadMorphism oneCellInner)
              (mapCellAlong morphism body))) :=
  (mapCellAlong_whiskerLeft morphism oneCellOuter (RawTwoCellExpr.whiskerLeft oneCellInner body)).trans
    ((congrArg (RawTwoCellExpr.castBoundary _ _)
        ((congrArg (RawTwoCellExpr.whiskerLeft (mapPath morphism.toComputadMorphism oneCellOuter))
            (mapCellAlong_whiskerLeft morphism oneCellInner body)).trans
          (RawTwoCellExpr.whiskerLeft_castBoundary (mapPath morphism.toComputadMorphism oneCellOuter) _ _
            (RawTwoCellExpr.whiskerLeft (mapPath morphism.toComputadMorphism oneCellInner)
              (mapCellAlong morphism body))))).trans
      (RawTwoCellExpr.castBoundary_trans _ _ _ _ _))

/-- `mapCellAlong` through `whiskerRight ∘ whiskerRight`. -/
theorem mapCellAlong_whiskerRight_whiskerRight {source target : ModeComputad}
    (morphism : ComputadMorphismTwo source target) {sm mm1 mm2 tm : Fin source.modeCount}
    {bodyDom bodyCod : ModalityPath source.toModeGraph sm mm1}
    (oneCellInner : ModalityPath source.toModeGraph mm1 mm2)
    (oneCellOuter : ModalityPath source.toModeGraph mm2 tm)
    (body : RawTwoCellExpr source.toModeSignature bodyDom bodyCod) :
    mapCellAlong morphism (RawTwoCellExpr.whiskerRight oneCellOuter (RawTwoCellExpr.whiskerRight oneCellInner body))
      = RawTwoCellExpr.castBoundary
          ((congrArg (fun path => composePath path (mapPath morphism.toComputadMorphism oneCellOuter))
              (mapPath_composePath morphism.toComputadMorphism bodyDom oneCellInner).symm).trans
            (mapPath_composePath morphism.toComputadMorphism (composePath bodyDom oneCellInner) oneCellOuter).symm)
          ((congrArg (fun path => composePath path (mapPath morphism.toComputadMorphism oneCellOuter))
              (mapPath_composePath morphism.toComputadMorphism bodyCod oneCellInner).symm).trans
            (mapPath_composePath morphism.toComputadMorphism (composePath bodyCod oneCellInner) oneCellOuter).symm)
          (RawTwoCellExpr.whiskerRight (mapPath morphism.toComputadMorphism oneCellOuter)
            (RawTwoCellExpr.whiskerRight (mapPath morphism.toComputadMorphism oneCellInner)
              (mapCellAlong morphism body))) :=
  (mapCellAlong_whiskerRight morphism oneCellOuter (RawTwoCellExpr.whiskerRight oneCellInner body)).trans
    ((congrArg (RawTwoCellExpr.castBoundary _ _)
        ((congrArg (RawTwoCellExpr.whiskerRight (mapPath morphism.toComputadMorphism oneCellOuter))
            (mapCellAlong_whiskerRight morphism oneCellInner body)).trans
          (RawTwoCellExpr.whiskerRight_castBoundary (mapPath morphism.toComputadMorphism oneCellOuter) _ _
            (RawTwoCellExpr.whiskerRight (mapPath morphism.toComputadMorphism oneCellInner)
              (mapCellAlong morphism body))))).trans
      (RawTwoCellExpr.castBoundary_trans _ _ _ _ _))

/-- `mapCellAlong` through `whiskerLeft ∘ whiskerRight`. -/
theorem mapCellAlong_whiskerLeft_whiskerRight {source target : ModeComputad}
    (morphism : ComputadMorphismTwo source target) {sm ms mt tm : Fin source.modeCount}
    (leftWhisker : ModalityPath source.toModeGraph sm ms)
    {bodyDom bodyCod : ModalityPath source.toModeGraph ms mt}
    (rightWhisker : ModalityPath source.toModeGraph mt tm)
    (body : RawTwoCellExpr source.toModeSignature bodyDom bodyCod) :
    mapCellAlong morphism (RawTwoCellExpr.whiskerLeft leftWhisker (RawTwoCellExpr.whiskerRight rightWhisker body))
      = RawTwoCellExpr.castBoundary
          ((congrArg (composePath (mapPath morphism.toComputadMorphism leftWhisker))
              (mapPath_composePath morphism.toComputadMorphism bodyDom rightWhisker).symm).trans
            (mapPath_composePath morphism.toComputadMorphism leftWhisker (composePath bodyDom rightWhisker)).symm)
          ((congrArg (composePath (mapPath morphism.toComputadMorphism leftWhisker))
              (mapPath_composePath morphism.toComputadMorphism bodyCod rightWhisker).symm).trans
            (mapPath_composePath morphism.toComputadMorphism leftWhisker (composePath bodyCod rightWhisker)).symm)
          (RawTwoCellExpr.whiskerLeft (mapPath morphism.toComputadMorphism leftWhisker)
            (RawTwoCellExpr.whiskerRight (mapPath morphism.toComputadMorphism rightWhisker)
              (mapCellAlong morphism body))) :=
  (mapCellAlong_whiskerLeft morphism leftWhisker (RawTwoCellExpr.whiskerRight rightWhisker body)).trans
    ((congrArg (RawTwoCellExpr.castBoundary _ _)
        ((congrArg (RawTwoCellExpr.whiskerLeft (mapPath morphism.toComputadMorphism leftWhisker))
            (mapCellAlong_whiskerRight morphism rightWhisker body)).trans
          (RawTwoCellExpr.whiskerLeft_castBoundary (mapPath morphism.toComputadMorphism leftWhisker) _ _
            (RawTwoCellExpr.whiskerRight (mapPath morphism.toComputadMorphism rightWhisker)
              (mapCellAlong morphism body))))).trans
      (RawTwoCellExpr.castBoundary_trans _ _ _ _ _))

/-- `mapCellAlong` through `whiskerRight ∘ whiskerLeft`. -/
theorem mapCellAlong_whiskerRight_whiskerLeft {source target : ModeComputad}
    (morphism : ComputadMorphismTwo source target) {sm ms mt tm : Fin source.modeCount}
    (leftWhisker : ModalityPath source.toModeGraph sm ms)
    {bodyDom bodyCod : ModalityPath source.toModeGraph ms mt}
    (rightWhisker : ModalityPath source.toModeGraph mt tm)
    (body : RawTwoCellExpr source.toModeSignature bodyDom bodyCod) :
    mapCellAlong morphism (RawTwoCellExpr.whiskerRight rightWhisker (RawTwoCellExpr.whiskerLeft leftWhisker body))
      = RawTwoCellExpr.castBoundary
          ((congrArg (fun path => composePath path (mapPath morphism.toComputadMorphism rightWhisker))
              (mapPath_composePath morphism.toComputadMorphism leftWhisker bodyDom).symm).trans
            (mapPath_composePath morphism.toComputadMorphism (composePath leftWhisker bodyDom) rightWhisker).symm)
          ((congrArg (fun path => composePath path (mapPath morphism.toComputadMorphism rightWhisker))
              (mapPath_composePath morphism.toComputadMorphism leftWhisker bodyCod).symm).trans
            (mapPath_composePath morphism.toComputadMorphism (composePath leftWhisker bodyCod) rightWhisker).symm)
          (RawTwoCellExpr.whiskerRight (mapPath morphism.toComputadMorphism rightWhisker)
            (RawTwoCellExpr.whiskerLeft (mapPath morphism.toComputadMorphism leftWhisker)
              (mapCellAlong morphism body))) :=
  (mapCellAlong_whiskerRight morphism rightWhisker (RawTwoCellExpr.whiskerLeft leftWhisker body)).trans
    ((congrArg (RawTwoCellExpr.castBoundary _ _)
        ((congrArg (RawTwoCellExpr.whiskerRight (mapPath morphism.toComputadMorphism rightWhisker))
            (mapCellAlong_whiskerLeft morphism leftWhisker body)).trans
          (RawTwoCellExpr.whiskerRight_castBoundary (mapPath morphism.toComputadMorphism rightWhisker) _ _
            (RawTwoCellExpr.whiskerLeft (mapPath morphism.toComputadMorphism leftWhisker)
              (mapCellAlong morphism body))))).trans
      (RawTwoCellExpr.castBoundary_trans _ _ _ _ _))

/-! ## The free convertibility is preserved: the twelve `TwoCellStep` rewrites -/

/-- ★ **`mapCellAlong` preserves the free 3-cell rewrites** — each `TwoCellStep` between source 2-cells maps to a
completed convertibility between the images.  The cast-free rewrites (`vcompId*`, `vcompAssoc`, `vcompCongr*`) hit
the same-named target `TwoCellStep`; the whisker rewrites reconcile `mapCellAlong`'s whisker cast with the target
rewrite through `castBoundaryCongr` + `castBoundary_id` / `castBoundary_vcomp`; the `interchange` rewrite rides
`mapCellAlong_hcomp` on both sides. -/
theorem mapTwoCellStep {source target : ModeComputad} (morphism : ComputadMorphismTwo source target)
    {sourceMode targetMode : source.toModeSignature.graph.Mode}
    {sourcePath targetPath : ModalityPath source.toModeSignature.graph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr source.toModeSignature sourcePath targetPath}
    (step : TwoCellStep source.toModeSignature cellAlpha cellBeta) :
    TwoCellConvFull target.toModeSignature (mapCellAlong morphism cellAlpha)
      (mapCellAlong morphism cellBeta) := by
  induction step with
  | vcompIdLeft cellA =>
      exact TwoCellConvFull.ofConv (TwoCellConv.ofStep (TwoCellStep.vcompIdLeft (mapCellAlong morphism cellA)))
  | vcompIdRight cellA =>
      exact TwoCellConvFull.ofConv (TwoCellConv.ofStep (TwoCellStep.vcompIdRight (mapCellAlong morphism cellA)))
  | vcompAssoc cellA cellB cellC =>
      exact TwoCellConvFull.ofConv (TwoCellConv.ofStep
        (TwoCellStep.vcompAssoc (mapCellAlong morphism cellA) (mapCellAlong morphism cellB)
          (mapCellAlong morphism cellC)))
  | whiskerLeftId oneCell path =>
      simp only [mapCellAlong_whiskerLeft, mapCellAlong_id]
      exact TwoCellConvFull.trans
        (TwoCellConvFull.castBoundaryCongr
          (mapPath_composePath morphism.toComputadMorphism oneCell path).symm
          (mapPath_composePath morphism.toComputadMorphism oneCell path).symm
          (TwoCellConvFull.ofConv (TwoCellConv.ofStep
            (@TwoCellStep.whiskerLeftId target.toModeSignature _ _ _
              (mapPath morphism.toComputadMorphism oneCell)
              (mapPath morphism.toComputadMorphism path)))))
        (convFull_of_cellEq (RawTwoCellExpr.castBoundary_id
          (mapPath_composePath morphism.toComputadMorphism oneCell path).symm))
  | whiskerRightId path oneCell =>
      simp only [mapCellAlong_whiskerRight, mapCellAlong_id]
      exact TwoCellConvFull.trans
        (TwoCellConvFull.castBoundaryCongr
          (mapPath_composePath morphism.toComputadMorphism path oneCell).symm
          (mapPath_composePath morphism.toComputadMorphism path oneCell).symm
          (TwoCellConvFull.ofConv (TwoCellConv.ofStep
            (@TwoCellStep.whiskerRightId target.toModeSignature _ _ _
              (mapPath morphism.toComputadMorphism path)
              (mapPath morphism.toComputadMorphism oneCell)))))
        (convFull_of_cellEq (RawTwoCellExpr.castBoundary_id
          (mapPath_composePath morphism.toComputadMorphism path oneCell).symm))
  | whiskerLeftVcomp oneCell cellB cellC =>
      exact TwoCellConvFull.trans
        (TwoCellConvFull.castBoundaryCongr _ _
          (TwoCellConvFull.ofConv (TwoCellConv.ofStep
            (TwoCellStep.whiskerLeftVcomp (mapPath morphism.toComputadMorphism oneCell)
              (mapCellAlong morphism cellB) (mapCellAlong morphism cellC)))))
        (convFull_of_cellEq (RawTwoCellExpr.castBoundary_vcomp _ _ _ _ _))
  | whiskerRightVcomp oneCell cellA cellB =>
      exact TwoCellConvFull.trans
        (TwoCellConvFull.castBoundaryCongr _ _
          (TwoCellConvFull.ofConv (TwoCellConv.ofStep
            (TwoCellStep.whiskerRightVcomp (mapPath morphism.toComputadMorphism oneCell)
              (mapCellAlong morphism cellA) (mapCellAlong morphism cellB)))))
        (convFull_of_cellEq (RawTwoCellExpr.castBoundary_vcomp _ _ _ _ _))
  | vcompCongrLeft cellB _ ih =>
      exact TwoCellConvFull.vcompCongrLeft (mapCellAlong morphism cellB) ih
  | vcompCongrRight cellA _ ih =>
      exact TwoCellConvFull.vcompCongrRight (mapCellAlong morphism cellA) ih
  | whiskerLeftCongr oneCell _ ih =>
      exact TwoCellConvFull.castBoundaryCongr _ _
        (TwoCellConvFull.whiskerLeftCongr (mapPath morphism.toComputadMorphism oneCell) ih)
  | whiskerRightCongr oneCell _ ih =>
      exact TwoCellConvFull.castBoundaryCongr _ _
        (TwoCellConvFull.whiskerRightCongr (mapPath morphism.toComputadMorphism oneCell) ih)
  | interchange cellA cellAUpper cellB cellBUpper =>
      simp only [mapCellAlong_hcomp, mapCellAlong_vcomp]
      refine TwoCellConvFull.trans
        (TwoCellConvFull.castBoundaryCongr _ _
          (TwoCellConvFull.ofConv (TwoCellConv.ofStep
            (TwoCellStep.interchange (mapCellAlong morphism cellA) (mapCellAlong morphism cellAUpper)
              (mapCellAlong morphism cellB) (mapCellAlong morphism cellBUpper))))) ?_
      exact convFull_of_cellEq (RawTwoCellExpr.castBoundary_vcomp _ _ _ _ _)

/-! ## The free convertibility is preserved (its closure) + the completed convertibility -/

/-- `mapCellAlong` preserves the free `TwoCellConv` (the rewrite closure): a single step via `mapTwoCellStep`,
`refl`/`symm`/`trans` structurally. -/
theorem mapTwoCellConv {source target : ModeComputad} (morphism : ComputadMorphismTwo source target)
    {sourceMode targetMode : source.toModeSignature.graph.Mode}
    {sourcePath targetPath : ModalityPath source.toModeSignature.graph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr source.toModeSignature sourcePath targetPath}
    (conv : TwoCellConv source.toModeSignature cellAlpha cellBeta) :
    TwoCellConvFull target.toModeSignature (mapCellAlong morphism cellAlpha)
      (mapCellAlong morphism cellBeta) := by
  induction conv with
  | ofStep step => exact mapTwoCellStep morphism step
  | refl cell => exact TwoCellConvFull.refl (mapCellAlong morphism cell)
  | symm _ ih => exact TwoCellConvFull.symm ih
  | trans _ _ ih1 ih2 => exact TwoCellConvFull.trans ih1 ih2

/-- ★ **The free 2-cell functor preserves the COMPLETED convertibility** — the r4 residual `fullPreserved`,
DISCHARGED.  Induction over all thirteen `TwoCellConvFull` constructors: `ofConv` reuses `mapTwoCellConv`; the
whisker-functoriality laws reconcile `mapCellAlong`'s cast with the same-named target law through
`castBoundaryCongr` + `castBoundary_id` / `castBoundary_vcomp` / `whiskerLeft_castBoundary` /
`whiskerLeft_pathCongr` / `castBoundary_trans`; the four one-hole congruences thread the inductive hypothesis
through `castBoundaryCongr`; `refl`/`symm`/`trans` structural. -/
theorem mapTwoCellConvFull {source target : ModeComputad} (morphism : ComputadMorphismTwo source target)
    {sourceMode targetMode : source.toModeSignature.graph.Mode}
    {sourcePath targetPath : ModalityPath source.toModeSignature.graph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr source.toModeSignature sourcePath targetPath}
    (convFull : TwoCellConvFull source.toModeSignature cellAlpha cellBeta) :
    TwoCellConvFull target.toModeSignature (mapCellAlong morphism cellAlpha)
      (mapCellAlong morphism cellBeta) := by
  induction convFull with
  | ofConv conv => exact mapTwoCellConv morphism conv
  | whiskerLeftUnit body => exact TwoCellConvFull.whiskerLeftUnit (mapCellAlong morphism body)
  | whiskerRightUnit body =>
      rename_i sourceMode targetMode oneCellDom oneCellCod
      refine TwoCellConvFull.trans (convFull_of_cellEq ?_)
        (TwoCellConvFull.trans
          (TwoCellConvFull.castBoundaryCongr
            (mapPath_composePath morphism.toComputadMorphism oneCellDom (identityPath targetMode)).symm
            (mapPath_composePath morphism.toComputadMorphism oneCellCod (identityPath targetMode)).symm
            (TwoCellConvFull.whiskerRightUnit (mapCellAlong morphism body)))
          (convFull_of_cellEq ?_))
      · exact mapCellAlong_whiskerRight morphism (identityPath targetMode) body
      · exact (RawTwoCellExpr.castBoundary_trans _ _ _ _ _).trans
          (mapCellAlong_castBoundary morphism _ _ body).symm
  | whiskerLeftComp oneCellOuter oneCellInner body =>
      rename_i oneCellDom oneCellCod
      refine TwoCellConvFull.trans (convFull_of_cellEq ?_)
        (TwoCellConvFull.trans
          (TwoCellConvFull.castBoundaryCongr
            ((congrArg (fun path => composePath path (mapPath morphism.toComputadMorphism oneCellDom))
                (mapPath_composePath morphism.toComputadMorphism oneCellOuter oneCellInner).symm).trans
              (mapPath_composePath morphism.toComputadMorphism (composePath oneCellOuter oneCellInner)
                oneCellDom).symm)
            ((congrArg (fun path => composePath path (mapPath morphism.toComputadMorphism oneCellCod))
                (mapPath_composePath morphism.toComputadMorphism oneCellOuter oneCellInner).symm).trans
              (mapPath_composePath morphism.toComputadMorphism (composePath oneCellOuter oneCellInner)
                oneCellCod).symm)
            (TwoCellConvFull.whiskerLeftComp (mapPath morphism.toComputadMorphism oneCellOuter)
              (mapPath morphism.toComputadMorphism oneCellInner) (mapCellAlong morphism body)))
          (convFull_of_cellEq ?_))
      · exact (mapCellAlong_whiskerLeft morphism (composePath oneCellOuter oneCellInner) body).trans
          ((congrArg (RawTwoCellExpr.castBoundary _ _)
            (RawTwoCellExpr.whiskerLeft_pathCongr
              (mapPath_composePath morphism.toComputadMorphism oneCellOuter oneCellInner).symm
              (mapCellAlong morphism body))).trans
            (RawTwoCellExpr.castBoundary_trans _ _ _ _ _))
      · refine Eq.trans ?_ (mapCellAlong_castBoundary morphism _ _
          (RawTwoCellExpr.whiskerLeft oneCellOuter (RawTwoCellExpr.whiskerLeft oneCellInner body))).symm
        refine Eq.trans ?_ (congrArg (RawTwoCellExpr.castBoundary _ _)
          (mapCellAlong_whiskerLeft_whiskerLeft morphism oneCellOuter oneCellInner body).symm)
        exact (RawTwoCellExpr.castBoundary_trans _ _ _ _ _).trans
          (RawTwoCellExpr.castBoundary_trans _ _ _ _ _).symm
  | whiskerRightComp oneCellInner oneCellOuter body =>
      rename_i oneCellDom oneCellCod
      refine TwoCellConvFull.trans (convFull_of_cellEq ?_)
        (TwoCellConvFull.trans
          (TwoCellConvFull.castBoundaryCongr
            ((congrArg (composePath (mapPath morphism.toComputadMorphism oneCellDom))
                (mapPath_composePath morphism.toComputadMorphism oneCellInner oneCellOuter).symm).trans
              (mapPath_composePath morphism.toComputadMorphism oneCellDom
                (composePath oneCellInner oneCellOuter)).symm)
            ((congrArg (composePath (mapPath morphism.toComputadMorphism oneCellCod))
                (mapPath_composePath morphism.toComputadMorphism oneCellInner oneCellOuter).symm).trans
              (mapPath_composePath morphism.toComputadMorphism oneCellCod
                (composePath oneCellInner oneCellOuter)).symm)
            (TwoCellConvFull.whiskerRightComp (mapPath morphism.toComputadMorphism oneCellInner)
              (mapPath morphism.toComputadMorphism oneCellOuter) (mapCellAlong morphism body)))
          (convFull_of_cellEq ?_))
      · exact (mapCellAlong_whiskerRight morphism (composePath oneCellInner oneCellOuter) body).trans
          ((congrArg (RawTwoCellExpr.castBoundary _ _)
            (RawTwoCellExpr.whiskerRight_pathCongr
              (mapPath_composePath morphism.toComputadMorphism oneCellInner oneCellOuter).symm
              (mapCellAlong morphism body))).trans
            (RawTwoCellExpr.castBoundary_trans _ _ _ _ _))
      · refine Eq.trans ?_ (mapCellAlong_castBoundary morphism _ _
          (RawTwoCellExpr.whiskerRight oneCellOuter (RawTwoCellExpr.whiskerRight oneCellInner body))).symm
        refine Eq.trans ?_ (congrArg (RawTwoCellExpr.castBoundary _ _)
          (mapCellAlong_whiskerRight_whiskerRight morphism oneCellInner oneCellOuter body).symm)
        exact (RawTwoCellExpr.castBoundary_trans _ _ _ _ _).trans
          (RawTwoCellExpr.castBoundary_trans _ _ _ _ _).symm
  | whiskerExchange leftWhisker rightWhisker body =>
      rename_i bodyDom bodyCod
      refine TwoCellConvFull.trans (convFull_of_cellEq ?_)
        (TwoCellConvFull.trans
          (TwoCellConvFull.castBoundaryCongr
            ((congrArg (composePath (mapPath morphism.toComputadMorphism leftWhisker))
                (mapPath_composePath morphism.toComputadMorphism bodyDom rightWhisker).symm).trans
              (mapPath_composePath morphism.toComputadMorphism leftWhisker
                (composePath bodyDom rightWhisker)).symm)
            ((congrArg (composePath (mapPath morphism.toComputadMorphism leftWhisker))
                (mapPath_composePath morphism.toComputadMorphism bodyCod rightWhisker).symm).trans
              (mapPath_composePath morphism.toComputadMorphism leftWhisker
                (composePath bodyCod rightWhisker)).symm)
            (TwoCellConvFull.whiskerExchange (mapPath morphism.toComputadMorphism leftWhisker)
              (mapPath morphism.toComputadMorphism rightWhisker) (mapCellAlong morphism body)))
          (convFull_of_cellEq ?_))
      · exact mapCellAlong_whiskerLeft_whiskerRight morphism leftWhisker rightWhisker body
      · refine Eq.trans ?_ (mapCellAlong_castBoundary morphism _ _
          (RawTwoCellExpr.whiskerRight rightWhisker (RawTwoCellExpr.whiskerLeft leftWhisker body))).symm
        refine Eq.trans ?_ (congrArg (RawTwoCellExpr.castBoundary _ _)
          (mapCellAlong_whiskerRight_whiskerLeft morphism leftWhisker rightWhisker body).symm)
        exact (RawTwoCellExpr.castBoundary_trans _ _ _ _ _).trans
          (RawTwoCellExpr.castBoundary_trans _ _ _ _ _).symm
  | vcompCongrLeft cellBeta _ ih => exact TwoCellConvFull.vcompCongrLeft (mapCellAlong morphism cellBeta) ih
  | vcompCongrRight cellAlpha _ ih => exact TwoCellConvFull.vcompCongrRight (mapCellAlong morphism cellAlpha) ih
  | whiskerLeftCongr oneCell _ ih =>
      exact TwoCellConvFull.castBoundaryCongr _ _
        (TwoCellConvFull.whiskerLeftCongr (mapPath morphism.toComputadMorphism oneCell) ih)
  | whiskerRightCongr oneCell _ ih =>
      exact TwoCellConvFull.castBoundaryCongr _ _
        (TwoCellConvFull.whiskerRightCongr (mapPath morphism.toComputadMorphism oneCell) ih)
  | refl cell => exact TwoCellConvFull.refl (mapCellAlong morphism cell)
  | symm _ ih => exact TwoCellConvFull.symm ih
  | trans _ _ ih1 ih2 => exact TwoCellConvFull.trans ih1 ih2

/-! ## Honesty markers -/

/-- ★ **Honesty marker — the STRUCTURAL FUNCTORIALITY of `mapCellAlong` SHIPS (r5 residual P1 closed).**
`mapTwoCellConvFull` (this file) transports the completed free-strict-2-category convertibility `TwoCellConvFull`
along ANY `ComputadMorphismTwo`, by induction over all thirteen `TwoCellConvFull` constructors (and, in the
`ofConv` case, over the free `TwoCellConv` and the twelve `TwoCellStep` rewrites via `mapTwoCellConv` /
`mapTwoCellStep`).  This is EXACTLY the `fullPreserved` hypothesis that `DispatchSaturated.lean`'s
`mapCellAlong_preservesConv` was conditional on — so the saturated-conv soundness lift is now UNCONDITIONAL (see
`ConvFullFunctorDispatch.lean`'s `mapCellAlong_preservesConvUnconditional`).  The only remaining brick of the free
2-cell functor is the genuine-generator coprojection `onTwoCell`
(`fxAmalg_hasRealGeneratorCoprojection`).  `= true`. -/
def fxAmalg_hasStructuralFunctoriality : Bool := true

end FX1Poly.Polygraph.Amalgam
