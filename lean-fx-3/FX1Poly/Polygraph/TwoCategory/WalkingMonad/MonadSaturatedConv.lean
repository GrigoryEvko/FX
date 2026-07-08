import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.WhiskerFunctoriality
import FX1Poly.Polygraph.Computad.MonadSeed

/-! # WalkingMonad — the SATURATED walking-monad 2-cell convertibility (the three monad laws as relations)

The walking-monad seed (`MonadSeed`) posits the unit `eta` and multiplication `mu` as 2-cell GENERATORS; a monad
is those generators SUBJECT to the three laws.  This file ships the SATURATED 2-cell convertibility of the seed:
the completed free-strict-2-category convertibility (`TwoCellConvFull`, embedded by `ofFull`) augmented with the
three monad laws as generating equations, made a genuine congruence by the four one-hole congruence closures plus
`refl` / `symm` / `trans`.

## The three monad laws (Mac Lane §VII.6 / Street)

  * **left unit**  `mu ∘ (eta ▷ t) ≈ id_t`  — `eta` whiskered on the right by `t`, then `mu`, collapses to `id_t`.
  * **right unit** `mu ∘ (t ◁ eta) ≈ id_t`  — `eta` whiskered on the left by `t`, then `mu`, collapses to `id_t`.
  * **associativity** `mu ∘ (mu ▷ t) ≈ mu ∘ (t ◁ mu)`  — the two ways to multiply three `t`'s agree.

These are the walking-monad analog of the adjunction's TWO triangle identities (`SaturatedTwoCellConv`), but the
monad has THREE laws (two units + one associativity) instead of two triangles.  Unlike the adjunction, whose
covariant monotone fold is REFUTED, the walking monad lives purely on Δ₊ where the covariant fold IS the sound
canonicalization carrier (`WalkingMonad/MonadDeltaModel`): the two unit laws are the SIMPLICIAL IDENTITIES
`σ_i ∘ δ_i = id` and `σ_i ∘ δ_{i+1} = id`, and associativity is the degeneracy–degeneracy commutation
`σ_j ∘ σ_i = σ_i ∘ σ_{j+1}` — all shipped, zero-axiom.

Raw Lean 4 + Init; the relation is an inductive `Prop`, its witnesses are constructors, so every declaration is
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.  Per-declaration `#assert_no_axioms`
gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-! ## The unit / multiplication as free 2-cells + the three law composites -/

/-- The seed's UNIT embeds as a free 2-cell `id_point ⇒ t`. -/
def monadUnitTwoCell :
    RawTwoCellExpr monadModeSignature (ModalityPath.nil (graph := monadGraph) MonadMode.point) monadT :=
  RawTwoCellExpr.gen MonadTwoCell.eta

/-- The seed's MULTIPLICATION embeds as a free 2-cell `t·t ⇒ t`. -/
def monadMulTwoCell :
    RawTwoCellExpr monadModeSignature monadTThenT monadT :=
  RawTwoCellExpr.gen MonadTwoCell.mu

/-- The **left-unit composite** `mu ∘ (eta ▷ t)` — the unit whiskered on the right by `t`, then the
multiplication.  A 2-cell `t ⇒ t`; the left-unit law asserts it is `id_t`. -/
def monadLeftUnitCell : RawTwoCellExpr monadModeSignature monadT monadT :=
  RawTwoCellExpr.vcomp
    (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT monadUnitTwoCell)
    monadMulTwoCell

/-- The **right-unit composite** `mu ∘ (t ◁ eta)` — the unit whiskered on the left by `t`, then the
multiplication.  A 2-cell `t ⇒ t`; the right-unit law asserts it is `id_t`. -/
def monadRightUnitCell : RawTwoCellExpr monadModeSignature monadT monadT :=
  RawTwoCellExpr.vcomp
    (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT monadUnitTwoCell)
    monadMulTwoCell

/-- The **left-associativity composite** `mu ∘ (mu ▷ t)` — multiply the first two `t`'s, then multiply the
result with the third.  A 2-cell `t·t·t ⇒ t`. -/
def monadAssocLeftCell : RawTwoCellExpr monadModeSignature monadTThenTThenT monadT :=
  RawTwoCellExpr.vcomp
    (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT monadMulTwoCell)
    monadMulTwoCell

/-- The **right-associativity composite** `mu ∘ (t ◁ mu)` — multiply the last two `t`'s, then multiply the first
with the result.  A 2-cell `t·t·t ⇒ t` (the source `t·(t·t)` is DEFINITIONALLY `(t·t)·t`). -/
def monadAssocRightCell : RawTwoCellExpr monadModeSignature monadTThenTThenT monadT :=
  RawTwoCellExpr.vcomp
    (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT monadMulTwoCell)
    monadMulTwoCell

/-- The identity 2-cell on `t` (the RHS of both unit laws). -/
def monadIdTCell : RawTwoCellExpr monadModeSignature monadT monadT :=
  RawTwoCellExpr.id (signature := monadModeSignature) monadT

/-! ## The saturated 2-cell convertibility -/

/-- ★ The **saturated 2-cell convertibility** of the walking monad: the completed free-strict-2-category
convertibility (`TwoCellConvFull`, embedded by `ofFull`) augmented with the THREE monad laws (left unit, right
unit, associativity) as generating equations, closed under the four one-hole congruences and `refl`/`symm`/`trans`
into a genuine congruence.  Two free 2-cells are equal AS 2-cells of the walking monad (the terminal monad
2-category `BΔ₊`) exactly when they are `MonadSaturatedTwoCellConv`-related. -/
inductive MonadSaturatedTwoCellConv :
    {sourceMode targetMode : MonadMode} →
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode} →
    RawTwoCellExpr monadModeSignature sourcePath targetPath →
    RawTwoCellExpr monadModeSignature sourcePath targetPath → Prop where
  /-- Embed the completed free-strict-2-category convertibility (structural laws + interchange + whisker
  functoriality + disjoint-whisker exchange + congruence closure). -/
  | ofFull {sourceMode targetMode : MonadMode}
      {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
      {cellAlpha cellBeta : RawTwoCellExpr monadModeSignature sourcePath targetPath} :
      TwoCellConvFull monadModeSignature cellAlpha cellBeta →
      MonadSaturatedTwoCellConv cellAlpha cellBeta
  /-- The **left-unit law** `mu ∘ (eta ▷ t) ≈ id_t`. -/
  | leftUnit : MonadSaturatedTwoCellConv monadLeftUnitCell monadIdTCell
  /-- The **right-unit law** `mu ∘ (t ◁ eta) ≈ id_t`. -/
  | rightUnit : MonadSaturatedTwoCellConv monadRightUnitCell monadIdTCell
  /-- The **associativity law** `mu ∘ (mu ▷ t) ≈ mu ∘ (t ◁ mu)`. -/
  | assoc : MonadSaturatedTwoCellConv monadAssocLeftCell monadAssocRightCell
  /-- Congruence in the LEFT factor of a vertical composite. -/
  | vcompCongrLeft {sourceMode targetMode : MonadMode}
      {oneCellF oneCellG oneCellH : ModalityPath monadGraph sourceMode targetMode}
      {cellAlpha cellAlpha' : RawTwoCellExpr monadModeSignature oneCellF oneCellG}
      (cellBeta : RawTwoCellExpr monadModeSignature oneCellG oneCellH) :
      MonadSaturatedTwoCellConv cellAlpha cellAlpha' →
      MonadSaturatedTwoCellConv (RawTwoCellExpr.vcomp cellAlpha cellBeta)
        (RawTwoCellExpr.vcomp cellAlpha' cellBeta)
  /-- Congruence in the RIGHT factor of a vertical composite. -/
  | vcompCongrRight {sourceMode targetMode : MonadMode}
      {oneCellF oneCellG oneCellH : ModalityPath monadGraph sourceMode targetMode}
      (cellAlpha : RawTwoCellExpr monadModeSignature oneCellF oneCellG)
      {cellBeta cellBeta' : RawTwoCellExpr monadModeSignature oneCellG oneCellH} :
      MonadSaturatedTwoCellConv cellBeta cellBeta' →
      MonadSaturatedTwoCellConv (RawTwoCellExpr.vcomp cellAlpha cellBeta)
        (RawTwoCellExpr.vcomp cellAlpha cellBeta')
  /-- Congruence under a left whiskering (so a law fires whiskered by a 1-cell). -/
  | whiskerLeftCongr {sourceMode middleMode targetMode : MonadMode}
      (oneCell : ModalityPath monadGraph sourceMode middleMode)
      {oneCellG oneCellH : ModalityPath monadGraph middleMode targetMode}
      {cellBeta cellBeta' : RawTwoCellExpr monadModeSignature oneCellG oneCellH} :
      MonadSaturatedTwoCellConv cellBeta cellBeta' →
      MonadSaturatedTwoCellConv (RawTwoCellExpr.whiskerLeft oneCell cellBeta)
        (RawTwoCellExpr.whiskerLeft oneCell cellBeta')
  /-- Congruence under a right whiskering. -/
  | whiskerRightCongr {sourceMode middleMode targetMode : MonadMode}
      {oneCellF oneCellG : ModalityPath monadGraph sourceMode middleMode}
      (oneCell : ModalityPath monadGraph middleMode targetMode)
      {cellAlpha cellAlpha' : RawTwoCellExpr monadModeSignature oneCellF oneCellG} :
      MonadSaturatedTwoCellConv cellAlpha cellAlpha' →
      MonadSaturatedTwoCellConv (RawTwoCellExpr.whiskerRight oneCell cellAlpha)
        (RawTwoCellExpr.whiskerRight oneCell cellAlpha')
  /-- Reflexivity. -/
  | refl {sourceMode targetMode : MonadMode}
      {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
      (cell : RawTwoCellExpr monadModeSignature sourcePath targetPath) :
      MonadSaturatedTwoCellConv cell cell
  /-- Symmetry. -/
  | symm {sourceMode targetMode : MonadMode}
      {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
      {cellAlpha cellBeta : RawTwoCellExpr monadModeSignature sourcePath targetPath} :
      MonadSaturatedTwoCellConv cellAlpha cellBeta → MonadSaturatedTwoCellConv cellBeta cellAlpha
  /-- Transitivity. -/
  | trans {sourceMode targetMode : MonadMode}
      {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
      {cellAlpha cellBeta cellGamma : RawTwoCellExpr monadModeSignature sourcePath targetPath} :
      MonadSaturatedTwoCellConv cellAlpha cellBeta → MonadSaturatedTwoCellConv cellBeta cellGamma →
      MonadSaturatedTwoCellConv cellAlpha cellGamma

/-! ## Embeddings: every free-system convertibility lifts to the saturated relation -/

/-- The free `TwoCellConv` (structural laws + interchange) lifts to the saturated relation. -/
theorem MonadSaturatedTwoCellConv.ofConv {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr monadModeSignature sourcePath targetPath}
    (conv : TwoCellConv monadModeSignature cellAlpha cellBeta) :
    MonadSaturatedTwoCellConv cellAlpha cellBeta :=
  MonadSaturatedTwoCellConv.ofFull (TwoCellConvFull.ofConv conv)

/-! ## The three monad-law witnesses (the saturation-flag content) -/

/-- ★ **The left-unit law holds in the saturated relation** — `mu ∘ (eta ▷ t) ≈ id_t`. -/
theorem monadLeftUnitHolds : MonadSaturatedTwoCellConv monadLeftUnitCell monadIdTCell :=
  MonadSaturatedTwoCellConv.leftUnit

/-- ★ **The right-unit law holds in the saturated relation** — `mu ∘ (t ◁ eta) ≈ id_t`. -/
theorem monadRightUnitHolds : MonadSaturatedTwoCellConv monadRightUnitCell monadIdTCell :=
  MonadSaturatedTwoCellConv.rightUnit

/-- ★ **The associativity law holds in the saturated relation** — `mu ∘ (mu ▷ t) ≈ mu ∘ (t ◁ mu)`. -/
theorem monadAssocHolds : MonadSaturatedTwoCellConv monadAssocLeftCell monadAssocRightCell :=
  MonadSaturatedTwoCellConv.assoc

/-- Smoke: the left-unit law fires UNDER a left-whisker context — `t ◁ (mu ∘ (eta ▷ t)) ≈ t ◁ id_t` — exercising
the congruence closure with the law generator (a genuine congruence, the whiskered monad law). -/
theorem monadLeftUnitWhiskeredHolds :
    MonadSaturatedTwoCellConv
      (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT monadLeftUnitCell)
      (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT monadIdTCell) :=
  MonadSaturatedTwoCellConv.whiskerLeftCongr _ MonadSaturatedTwoCellConv.leftUnit

/-- Smoke: the two unit composites are saturated-convertible to EACH OTHER (both collapse to `id_t`) — the monad's
`mu ∘ (eta ▷ t) ≈ mu ∘ (t ◁ eta)`, chaining the two unit laws through `id_t`. -/
theorem monadUnitCoherence :
    MonadSaturatedTwoCellConv monadLeftUnitCell monadRightUnitCell :=
  MonadSaturatedTwoCellConv.trans MonadSaturatedTwoCellConv.leftUnit
    (MonadSaturatedTwoCellConv.symm MonadSaturatedTwoCellConv.rightUnit)

/-! ## Honesty markers -/

/-- **ESTABLISHED.**  The SATURATED walking-monad 2-cell convertibility (`MonadSaturatedTwoCellConv`) — the
completed free-strict-2-category convertibility plus the THREE monad laws as a congruence — is shipped, and all
three laws hold (`monadLeftUnitHolds` / `monadRightUnitHolds` / `monadAssocHolds`).  `= true`. -/
def fxMonad_hasSaturatedTwoCellConvRelation : Bool := true

end FX1Poly.Polygraph
