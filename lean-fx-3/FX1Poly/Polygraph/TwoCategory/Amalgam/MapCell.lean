import FX1Poly.Polygraph.TwoCategory.Amalgam.Pushout
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.WhiskerFunctoriality

/-! # Polygraph/TwoCategory/Amalgam/MapCell — the free 2-cell functor along a computad morphism (WP-AMALG r4, A)

`Pushout.lean` (r1) built `ComputadMorphism` — a signature morphism acting on MODES and 1-GENERATORS, with the
two pushout coprojections `inclusionLeft` / `inclusionRight` as instances.  What it did NOT provide is the action
on 2-CELLS: given `alpha : RawTwoCellExpr src.toModeSignature pathA pathB`, transport it to
`RawTwoCellExpr tgt.toModeSignature (mapPath pathA) (mapPath pathB)`.  That transport is exactly what the saturated
dispatch (`SaturatedConvOverPushout`) needs to state the pushout's base relation as the disjoint union of the
retagged component relations — the r3 residual (A) "NO mapCellAlong".

This file closes residual (A) at the FREE 2-cell level.

## The one sanctioned interface extension (documented)

A `ComputadMorphism` cannot induce a 2-cell functor by itself: the target 2-cell family
(`tgt.ReconstructedTwoCell`) is not determined by the mode + 1-generator maps — a morphism must ALSO say where the
GENERATING 2-cells go.  So this file ADDITIVELY extends the interface with `ComputadMorphismTwo extends
ComputadMorphism`, whose single new field `onTwoCell` is the action on reconstructed generating 2-cells (the
2-generator field the prompt sanctions).  `Pushout.lean`'s `ComputadMorphism` and its coprojections stay
BYTE-IDENTICAL — the extension is a new structure, not a new field on the old one.

## What ships here (each piece zero-axiom, structural, ASCII-only)

  * **`mapModality`** / **`mapPath`** — the induced 1-cell functor: a generating modality maps by
    `onModalityGenerators` (endpoints carried by `onModes` via `endpointsPreserved`), a path maps generator-wise.
  * **`mapPath_composePath`** — `mapPath` is a monoid homomorphism (only PROPOSITIONALLY: cons-induction, base
    `rfl`, step `congrArg` — the landmine the whisker cases of `mapCellAlong` ride through `castBoundary`).
  * **`ComputadMorphismTwo`** — the sanctioned extension, `extends ComputadMorphism` + `onTwoCell`.
  * **`mapCellAlong`** — the free 2-cell functor: `gen` via `onTwoCell`, `id` / `vcomp` CAST-FREE (boundaries match
    on the nose), the two whisker cases through `castBoundary (mapPath_composePath ...)` (the smallest cast
    footprint).
  * **`mapCellAlong_castBoundary`** — `mapCellAlong` commutes with `castBoundary` (both are `Eq.rec`; `cases` the
    equalities) — the bridge the `TwoCellConvFull` functoriality cases need.
  * **`inclusionLeftTwo`** / **`inclusionRightTwo`** — the two coprojections lifted to `ComputadMorphismTwo` for
    NO-2-generator (locally thin) components: `onTwoCell` is vacuous (`Fin.elim0` on the empty 2-generator index),
    exactly as `noGen_of_twoGenLenZero` discharges the reconstructed family.  The REAL-relation coprojection
    `onTwoCell` (the `interpretWordFrom`-transport of a genuine generating 2-cell) is the named residual.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The induced 1-cell functor -/

/-- The action of a computad morphism on a **generating modality** — a 1-generator `mod : src.Modality a b` maps to
`onModalityGenerators mod.val`, whose recorded endpoints are the `onModes`-images of `mod`'s (by
`endpointsPreserved`, then `mod.property`).  Propext-free (a `congrArg` composed with the endpoint witness). -/
def mapModality {source target : ModeComputad} (morphism : ComputadMorphism source target)
    {sourceMode targetMode : Fin source.modeCount} (modality : source.Modality sourceMode targetMode) :
    target.Modality (morphism.onModes sourceMode) (morphism.onModes targetMode) :=
  ⟨morphism.onModalityGenerators modality.val,
    (morphism.endpointsPreserved modality.val).trans
      (congrArg (fun endpoints => (morphism.onModes endpoints.1, morphism.onModes endpoints.2))
        modality.property)⟩

/-- The induced **1-cell functor** on modality paths (free 1-cells) — map every generator by `mapModality`,
threading `onModes` through the endpoints.  `nil` to `nil`, `cons` generator-wise.  Structural on the path. -/
def mapPath {source target : ModeComputad} (morphism : ComputadMorphism source target) :
    {sourceMode targetMode : Fin source.modeCount} →
    ModalityPath source.toModeGraph sourceMode targetMode →
    ModalityPath target.toModeGraph (morphism.onModes sourceMode) (morphism.onModes targetMode)
  | _, _, .nil mode => ModalityPath.nil (graph := target.toModeGraph) (morphism.onModes mode)
  | _, _, .cons modality rest => ModalityPath.cons (mapModality morphism modality) (mapPath morphism rest)

/-- The induced 1-cell functor carries the identity path to the identity path (definitional). -/
theorem mapPath_identityPath {source target : ModeComputad} (morphism : ComputadMorphism source target)
    (mode : Fin source.modeCount) :
    mapPath morphism (identityPath (graph := source.toModeGraph) mode)
      = identityPath (graph := target.toModeGraph) (morphism.onModes mode) := rfl

/-- ★ **`mapPath` is a monoid homomorphism** — it distributes over path composition, but only PROPOSITIONALLY:
`composePath` recurses on its first argument, so the base case is `rfl` while the `cons` step needs a `congrArg`
on the inductive hypothesis (NOT `rfl`).  This is the equality the two whisker cases of `mapCellAlong` thread
through `castBoundary`. -/
theorem mapPath_composePath {source target : ModeComputad} (morphism : ComputadMorphism source target) :
    {sourceMode middleMode targetMode : Fin source.modeCount} →
    (first : ModalityPath source.toModeGraph sourceMode middleMode) →
    (second : ModalityPath source.toModeGraph middleMode targetMode) →
      mapPath morphism (composePath first second)
        = composePath (mapPath morphism first) (mapPath morphism second)
  | _, _, _, .nil _, _ => rfl
  | _, _, _, .cons modality rest, second =>
      show ModalityPath.cons (mapModality morphism modality) (mapPath morphism (composePath rest second))
          = ModalityPath.cons (mapModality morphism modality)
              (composePath (mapPath morphism rest) (mapPath morphism second)) from
        congrArg (ModalityPath.cons (mapModality morphism modality))
          (mapPath_composePath morphism rest second)

/-! ## The sanctioned interface extension: the 2-cell action -/

/-- ★ **`ComputadMorphismTwo`** — the ONE sanctioned additive interface extension.  A `ComputadMorphism` (the
mode + 1-generator action, `Pushout.lean`'s notion, untouched) EXTENDED with `onTwoCell`: the action on the
reconstructed GENERATING 2-cells.  Because the source's generating 2-cells are the atoms of
`RawTwoCellExpr src.toModeSignature` (the `gen` constructor), knowing where they go is exactly what promotes the
1-cell functor `mapPath` to a 2-cell functor `mapCellAlong`.  `onTwoCell`'s boundary is carried by `mapPath` — a
generating 2-cell `src.ReconstructedTwoCell sourcePath targetPath` maps to
`tgt.ReconstructedTwoCell (mapPath sourcePath) (mapPath targetPath)`, mirroring `mapModality` one dimension up. -/
structure ComputadMorphismTwo (source target : ModeComputad) extends ComputadMorphism source target where
  /-- The action on generating 2-cells (the sanctioned 2-generator field) — a reconstructed generating 2-cell of
  `source` between parallel free 1-cells maps to one of `target` between their `mapPath`-images. -/
  onTwoCell : {sourceMode targetMode : Fin source.modeCount} →
    {sourcePath targetPath : ModalityPath source.toModeGraph sourceMode targetMode} →
    source.ReconstructedTwoCell sourcePath targetPath →
    target.ReconstructedTwoCell (mapPath toComputadMorphism sourcePath) (mapPath toComputadMorphism targetPath)

/-! ## The free 2-cell functor -/

/-- ★ **The free 2-cell functor along a computad morphism** — transport a free 2-cell expression over
`src.toModeSignature` to one over `tgt.toModeSignature`, boundaries carried by `mapPath`.  A GENERATING 2-cell
(`gen`) maps by the sanctioned `onTwoCell`; `id` and `vcomp` are CAST-FREE (the mapped boundaries coincide
definitionally — `mapPath` commutes with the identity path and vertical composition preserves boundaries); the two
whisker cases carry the SINGLE unavoidable cast, `castBoundary (mapPath_composePath ...)` reconciling
`mapPath (composePath oneCell body) ` with `composePath (mapPath oneCell) (mapPath body)`.  Structural on the cell
grammar. -/
def mapCellAlong {source target : ModeComputad} (morphism : ComputadMorphismTwo source target) :
    {sourceMode targetMode : Fin source.modeCount} →
    {sourcePath targetPath : ModalityPath source.toModeGraph sourceMode targetMode} →
    RawTwoCellExpr source.toModeSignature sourcePath targetPath →
    RawTwoCellExpr target.toModeSignature
      (mapPath morphism.toComputadMorphism sourcePath) (mapPath morphism.toComputadMorphism targetPath)
  | _, _, _, _, .gen generator => RawTwoCellExpr.gen (morphism.onTwoCell generator)
  | _, _, _, _, .id path =>
      RawTwoCellExpr.id (signature := target.toModeSignature) (mapPath morphism.toComputadMorphism path)
  | _, _, _, _, .vcomp cellAlpha cellBeta =>
      RawTwoCellExpr.vcomp (mapCellAlong morphism cellAlpha) (mapCellAlong morphism cellBeta)
  | _, _, _, _, @RawTwoCellExpr.whiskerLeft _ _ _ _ oneCell oneCellG oneCellH body =>
      RawTwoCellExpr.castBoundary
        (mapPath_composePath morphism.toComputadMorphism oneCell oneCellG).symm
        (mapPath_composePath morphism.toComputadMorphism oneCell oneCellH).symm
        (RawTwoCellExpr.whiskerLeft (mapPath morphism.toComputadMorphism oneCell)
          (mapCellAlong morphism body))
  | _, _, _, _, @RawTwoCellExpr.whiskerRight _ _ _ _ oneCellF oneCellG oneCell body =>
      RawTwoCellExpr.castBoundary
        (mapPath_composePath morphism.toComputadMorphism oneCellF oneCell).symm
        (mapPath_composePath morphism.toComputadMorphism oneCellG oneCell).symm
        (RawTwoCellExpr.whiskerRight (mapPath morphism.toComputadMorphism oneCell)
          (mapCellAlong morphism body))

/-- **`mapCellAlong` commutes with `castBoundary`** — both are `Eq.rec` on the boundary; substituting the two
boundary equalities collapses each cast, so the functor slides through.  The bridge the `TwoCellConvFull`
functoriality cases need.  `cases` on the equalities then `rfl` (propext-free). -/
theorem mapCellAlong_castBoundary {source target : ModeComputad} (morphism : ComputadMorphismTwo source target)
    {sourceMode targetMode : Fin source.modeCount}
    {sourcePath sourcePath' targetPath targetPath' : ModalityPath source.toModeGraph sourceMode targetMode}
    (hsource : sourcePath = sourcePath') (htarget : targetPath = targetPath')
    (cell : RawTwoCellExpr source.toModeSignature sourcePath targetPath) :
    mapCellAlong morphism (RawTwoCellExpr.castBoundary hsource htarget cell)
      = RawTwoCellExpr.castBoundary (congrArg (mapPath morphism.toComputadMorphism) hsource)
          (congrArg (mapPath morphism.toComputadMorphism) htarget) (mapCellAlong morphism cell) := by
  cases hsource; cases htarget; rfl

/-! ## The coprojections lifted to the 2-cell interface (locally-thin components) -/

/-- ★ **The left coprojection as a `ComputadMorphismTwo`, for a no-2-generator (locally thin) component 1.**  The
mode + 1-generator action is `Pushout.lean`'s `inclusionLeft` (untouched); the 2-cell action `onTwoCell` is
VACUOUS — component 1 has an empty 2-generator list, so `source.ReconstructedTwoCell` is indexed in `Fin 0` and
`Fin.elim0` discharges it (exactly as `noGen_of_twoGenLenZero`).  The genuine-generator coprojection `onTwoCell`
(the `interpretWordFrom`-transport) is the r4 named residual. -/
def inclusionLeftTwo (comp1 comp2 : ModeComputad) (sameModes : comp1.modeCount = comp2.modeCount)
    (leftThin : comp1.twoCellGenerators.length = 0) :
    ComputadMorphismTwo comp1 (pushoutShared comp1 comp2 sameModes) where
  toComputadMorphism := inclusionLeft comp1 comp2 sameModes
  onTwoCell := fun generator => Fin.elim0 (leftThin ▸ generator.val)

/-- ★ **The right coprojection as a `ComputadMorphismTwo`, for a no-2-generator (locally thin) component 2.**  The
dual of `inclusionLeftTwo`: `inclusionRight` on modes + 1-generators, and a vacuous `onTwoCell` (component 2's
2-generator list is empty). -/
def inclusionRightTwo (comp1 comp2 : ModeComputad) (sameModes : comp1.modeCount = comp2.modeCount)
    (rightThin : comp2.twoCellGenerators.length = 0) :
    ComputadMorphismTwo comp2 (pushoutShared comp1 comp2 sameModes) where
  toComputadMorphism := inclusionRight comp1 comp2 sameModes
  onTwoCell := fun generator => Fin.elim0 (rightThin ▸ generator.val)

/-! ## Honesty markers -/

/-- ★ **Honesty marker — the free 2-cell functor `mapCellAlong` SHIPS (r4 residual A closed at the free level).**
The induced 1-cell functor (`mapModality` / `mapPath`) with its homomorphism law (`mapPath_composePath`), the
sanctioned interface extension `ComputadMorphismTwo` (`extends ComputadMorphism` + the 2-generator field
`onTwoCell`), the free 2-cell functor `mapCellAlong` (gen via `onTwoCell`, id/vcomp cast-free, the two whisker
cases through the single `castBoundary (mapPath_composePath ...)`) with its cast-commutation
`mapCellAlong_castBoundary`, and the two coprojections lifted to `ComputadMorphismTwo` for no-2-generator
components (`inclusionLeftTwo` / `inclusionRightTwo`, vacuous `onTwoCell`).  This is the transport r3 flagged as
"NO mapCellAlong" — now present.  The genuine-generator coprojection `onTwoCell` (the `interpretWordFrom`
transport of a real generating 2-cell) is the documented residual.  `= true`. -/
def fxAmalg_hasMapCellAlong : Bool := true

/-- ★ **Honesty marker — the REAL-relation coprojection `onTwoCell` SHIPS (r6 P2, `RealCoprojection.lean`).**  The
action of the right coprojection on a GENUINE generating 2-cell (`monadComputad`'s `eta` / `mu`, or any component-2
2-generator) is `inclusionRightTwoReal`, whose `onTwoCell` sends a reconstructed generating 2-cell to the pushout
reconstructed 2-cell at `embedRightTwoGen`.  The engine is `interpretWordFrom_map`: a mode-injective coprojection
commutes with the word-to-`ModalityPath` interpreter (`interpretWordFrom (onModes src) (word.map onModalityGen) =
(interpretWordFrom src word).map (onModes × mapPath)`), so each generator's `lhs` / `rhs` word interprets, under the
retag `embedRightLetter`, to the `mapPath`-image of the source interpretation — exactly the dependent seed-transport
this marker named.  `mapCellAlong` is now populated for a coprojection into a pushout whose component has real
2-generators, not only the LOCALLY-THIN fragment.  `= true`. -/
def fxAmalg_hasRealGeneratorCoprojection : Bool := true

end FX1Poly.Polygraph.Amalgam
