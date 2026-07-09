import FX1Poly.Polygraph.TwoCategory.WalkingIdempotent.IdempotentMonadSeed

/-! # WalkingIdempotent/IdempotentMonadSaturatedConv — the saturated 2-cell convertibility with the idempotence law

The walking-monad saturated convertibility (`MonadSaturatedTwoCellConv`) is the free strict-2-category
convertibility plus the three monad laws.  The walking IDEMPOTENT monad adds ONE more generating equation — the
well-pointedness / idempotence law `eta ▷ t ≈ t ◁ eta` (`monadEtaTCell ≈ monadTEtaCell`) — and re-closes under the
four one-hole congruences and `refl`/`symm`/`trans` so the new law is a genuine congruence.  The congruences and
the equivalence closure MUST be re-listed at this level: they cannot be inherited through `ofMonad`, because a
congruence built over `MonadSaturatedTwoCellConv` could not step through an `idempotence` premise.

By nLab (*idempotent monad*) `mu` is then a natural isomorphism and every hom-category is a POSET (Lack, *A
2-Categories Companion*, §1.5: "locally posetal … at most one 2-cell between any two parallel 1-cells"); the
walking idempotent monad is the terminal locally-posetal monad.  That local posetality (thinness) is the decision
content, developed in `IdempotentMonadModel` / `IdempotentMonadDecision`.

Raw Lean 4 + Init; the relation is an inductive `Prop`, so every declaration is
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.  Per-declaration `#assert_no_axioms`
gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-- ★ The **saturated 2-cell convertibility of the walking IDEMPOTENT monad**: the walking-monad saturated
convertibility (embedded by `ofMonad`) plus the idempotence law `eta ▷ t ≈ t ◁ eta` (`idempotence`), closed under
the four one-hole congruences and `refl`/`symm`/`trans` into a genuine congruence.  Two free 2-cells are equal AS
2-cells of the walking idempotent monad exactly when they are `IdempotentMonadSaturatedTwoCellConv`-related. -/
inductive IdempotentMonadSaturatedTwoCellConv :
    {sourceMode targetMode : MonadMode} →
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode} →
    RawTwoCellExpr monadModeSignature sourcePath targetPath →
    RawTwoCellExpr monadModeSignature sourcePath targetPath → Prop where
  /-- Embed the walking-monad saturated convertibility (structural laws + the three monad laws). -/
  | ofMonad {sourceMode targetMode : MonadMode}
      {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
      {cellAlpha cellBeta : RawTwoCellExpr monadModeSignature sourcePath targetPath} :
      MonadSaturatedTwoCellConv cellAlpha cellBeta →
      IdempotentMonadSaturatedTwoCellConv cellAlpha cellBeta
  /-- ★ The **idempotence law** `eta ▷ t ≈ t ◁ eta` — the two unit whiskerings coincide (well-pointedness); the
  sole generating equation of the walking IDEMPOTENT monad over the walking monad. -/
  | idempotence : IdempotentMonadSaturatedTwoCellConv monadEtaTCell monadTEtaCell
  /-- Congruence in the LEFT factor of a vertical composite. -/
  | vcompCongrLeft {sourceMode targetMode : MonadMode}
      {oneCellF oneCellG oneCellH : ModalityPath monadGraph sourceMode targetMode}
      {cellAlpha cellAlpha' : RawTwoCellExpr monadModeSignature oneCellF oneCellG}
      (cellBeta : RawTwoCellExpr monadModeSignature oneCellG oneCellH) :
      IdempotentMonadSaturatedTwoCellConv cellAlpha cellAlpha' →
      IdempotentMonadSaturatedTwoCellConv (RawTwoCellExpr.vcomp cellAlpha cellBeta)
        (RawTwoCellExpr.vcomp cellAlpha' cellBeta)
  /-- Congruence in the RIGHT factor of a vertical composite. -/
  | vcompCongrRight {sourceMode targetMode : MonadMode}
      {oneCellF oneCellG oneCellH : ModalityPath monadGraph sourceMode targetMode}
      (cellAlpha : RawTwoCellExpr monadModeSignature oneCellF oneCellG)
      {cellBeta cellBeta' : RawTwoCellExpr monadModeSignature oneCellG oneCellH} :
      IdempotentMonadSaturatedTwoCellConv cellBeta cellBeta' →
      IdempotentMonadSaturatedTwoCellConv (RawTwoCellExpr.vcomp cellAlpha cellBeta)
        (RawTwoCellExpr.vcomp cellAlpha cellBeta')
  /-- Congruence under a left whiskering (so the idempotence law fires whiskered by a 1-cell). -/
  | whiskerLeftCongr {sourceMode middleMode targetMode : MonadMode}
      (oneCell : ModalityPath monadGraph sourceMode middleMode)
      {oneCellG oneCellH : ModalityPath monadGraph middleMode targetMode}
      {cellBeta cellBeta' : RawTwoCellExpr monadModeSignature oneCellG oneCellH} :
      IdempotentMonadSaturatedTwoCellConv cellBeta cellBeta' →
      IdempotentMonadSaturatedTwoCellConv (RawTwoCellExpr.whiskerLeft oneCell cellBeta)
        (RawTwoCellExpr.whiskerLeft oneCell cellBeta')
  /-- Congruence under a right whiskering. -/
  | whiskerRightCongr {sourceMode middleMode targetMode : MonadMode}
      {oneCellF oneCellG : ModalityPath monadGraph sourceMode middleMode}
      (oneCell : ModalityPath monadGraph middleMode targetMode)
      {cellAlpha cellAlpha' : RawTwoCellExpr monadModeSignature oneCellF oneCellG} :
      IdempotentMonadSaturatedTwoCellConv cellAlpha cellAlpha' →
      IdempotentMonadSaturatedTwoCellConv (RawTwoCellExpr.whiskerRight oneCell cellAlpha)
        (RawTwoCellExpr.whiskerRight oneCell cellAlpha')
  /-- Reflexivity. -/
  | refl {sourceMode targetMode : MonadMode}
      {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
      (cell : RawTwoCellExpr monadModeSignature sourcePath targetPath) :
      IdempotentMonadSaturatedTwoCellConv cell cell
  /-- Symmetry. -/
  | symm {sourceMode targetMode : MonadMode}
      {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
      {cellAlpha cellBeta : RawTwoCellExpr monadModeSignature sourcePath targetPath} :
      IdempotentMonadSaturatedTwoCellConv cellAlpha cellBeta →
      IdempotentMonadSaturatedTwoCellConv cellBeta cellAlpha
  /-- Transitivity. -/
  | trans {sourceMode targetMode : MonadMode}
      {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
      {cellAlpha cellBeta cellGamma : RawTwoCellExpr monadModeSignature sourcePath targetPath} :
      IdempotentMonadSaturatedTwoCellConv cellAlpha cellBeta →
      IdempotentMonadSaturatedTwoCellConv cellBeta cellGamma →
      IdempotentMonadSaturatedTwoCellConv cellAlpha cellGamma

/-! ## The idempotence witnesses (the presentation content) -/

/-- ★ **The idempotence law holds** — `eta ▷ t ≈ t ◁ eta`: the two unit whiskerings are convertible, so `mu` is a
(natural) isomorphism and the monad is idempotent. -/
theorem idempotenceLawHolds :
    IdempotentMonadSaturatedTwoCellConv monadEtaTCell monadTEtaCell :=
  IdempotentMonadSaturatedTwoCellConv.idempotence

/-- Every walking-monad saturated convertibility lifts to the idempotent relation (the `ofMonad` embedding as a
theorem, so the three monad laws are available directly). -/
theorem IdempotentMonadSaturatedTwoCellConv.ofMonadLaw {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr monadModeSignature sourcePath targetPath}
    (conv : MonadSaturatedTwoCellConv cellAlpha cellBeta) :
    IdempotentMonadSaturatedTwoCellConv cellAlpha cellBeta :=
  IdempotentMonadSaturatedTwoCellConv.ofMonad conv

/-- Smoke: the LEFT-UNIT monad law still holds in the idempotent relation (via `ofMonad`) — the idempotent monad
is still a monad. -/
theorem idempotentLeftUnitHolds :
    IdempotentMonadSaturatedTwoCellConv monadLeftUnitCell monadIdTCell :=
  IdempotentMonadSaturatedTwoCellConv.ofMonad MonadSaturatedTwoCellConv.leftUnit

/-- Smoke: the ASSOCIATIVITY monad law still holds in the idempotent relation (via `ofMonad`). -/
theorem idempotentAssocHolds :
    IdempotentMonadSaturatedTwoCellConv monadAssocLeftCell monadAssocRightCell :=
  IdempotentMonadSaturatedTwoCellConv.ofMonad MonadSaturatedTwoCellConv.assoc

/-- Smoke: the idempotence law fires UNDER a left-whisker context — `t ◁ (eta ▷ t) ≈ t ◁ (t ◁ eta)` — exercising
the congruence closure with the idempotence generator (a genuine congruence, the whiskered idempotence law). -/
theorem idempotenceWhiskeredHolds :
    IdempotentMonadSaturatedTwoCellConv
      (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT monadEtaTCell)
      (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT monadTEtaCell) :=
  IdempotentMonadSaturatedTwoCellConv.whiskerLeftCongr _ IdempotentMonadSaturatedTwoCellConv.idempotence

/-- Smoke: the two idempotence faces are convertible to EACH OTHER through the identity witness — `eta ▷ t ≈
t ◁ eta` chained with reflexivity, exercising `trans` around the new law. -/
theorem idempotentFacesCohere :
    IdempotentMonadSaturatedTwoCellConv monadEtaTCell monadTEtaCell :=
  IdempotentMonadSaturatedTwoCellConv.trans (IdempotentMonadSaturatedTwoCellConv.refl monadEtaTCell)
    IdempotentMonadSaturatedTwoCellConv.idempotence

/-! ## Honesty marker -/

/-- **ESTABLISHED.**  The SATURATED walking-idempotent-monad 2-cell convertibility
(`IdempotentMonadSaturatedTwoCellConv`) — the walking-monad saturated convertibility plus the idempotence law
`eta ▷ t ≈ t ◁ eta` as a congruence — is shipped, the idempotence law holds (`idempotenceLawHolds`), it fires
under whiskering (`idempotenceWhiskeredHolds`), and the three monad laws still hold via `ofMonad`.  `= true`. -/
def fxIdempotentMonad_hasSaturatedConvWithIdempotence : Bool := true

end FX1Poly.Polygraph
