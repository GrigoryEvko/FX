import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadSaturatedConv

/-! # WalkingKZ/KZMonadPresentation — the walking Kock-Zoberlein (lax-idempotent) monad presentation

A lax-idempotent (KZ) 2-monad `(t, eta, mu)` is one for which the multiplication is LEFT ADJOINT to the unit
whiskering — `Tη ⊣ mu ⊣ ηT` (Kock, *Monads for which structures are adjoint to units*, JPAA 1995; nLab
*lax-idempotent 2-monad*).  In the order-enriched (locally-posetal) presentation this adjunction is a single
DIRECTED INEQUALITY between two parallel 2-cells — the KZ comparison `Tη <= ηT`, i.e. `t ◁ eta <= eta ▷ t`
(Stubbe; Marmolejo-Walters; both after Kock 1995) — NOT an equality.  The walking IDEMPOTENT monad is the STRICT
special case that forces these two EQUAL (`mu` iso, homs discrete/thin); the walking KZ monad RELAXES that equality
to the directed order, so the homs become genuine POSETS (Street: the free KZ structure is Delta_+ under the
POINTWISE ordering).

## The presentation: a PREORDER on 2-cells, not an equivalence

The walking monad's 2-cells (`MonadSaturatedTwoCellConv`) are the free strict-2-category convertibility plus the
three monad laws.  The walking KZ monad enriches those in posets: a single generating INEQUALITY `t ◁ eta <= eta ▷
t` (`kzGen`), closed under the four one-hole congruences plus `refl` / `trans` into a genuine PREORDER — with NO
`symm` (that omission IS the lax-idempotency: the comparison is directed).  Monad-law EQUALITIES enter as `<=` in
BOTH directions through `ofMonad`, so the poset's antisymmetrization recovers exactly `MonadSaturatedTwoCellConv`
(the poset enrichment adds no new 2-cell EQUALITIES, only the order).

The two idempotence faces (`kzTEtaCell` = `t ◁ eta`, `kzEtaTCell` = `eta ▷ t`) are the same free cells whose
identification defines the walking idempotent monad; here they are ORDERED, not identified.  Under the shipped
Delta_+ fold `monadMonotoneMapOf` they fold to the monotone maps `[0]` and `[1]` (verified `rfl`), so the KZ
generator is the fold-order `[0] <= [1]` — the standard `Tη <= ηT` direction.

Raw Lean 4 + Init; the relation is an inductive `Prop`, its witnesses are constructors, so every declaration is
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.  Per-declaration `#assert_no_axioms`
gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-! ## The two idempotence faces (the KZ comparison endpoints) -/

/-- **`t ◁ eta`** — the unit whiskered on the LEFT by `t`: a free 2-cell `t ⇒ t.t`.  The SMALL side of the KZ
comparison `Tη <= ηT`; folds to the monotone map `[0]` in the Delta_+ model. -/
def kzTEtaCell : RawTwoCellExpr monadModeSignature monadT monadTThenT :=
  RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT monadUnitTwoCell

/-- **`eta ▷ t`** — the unit whiskered on the RIGHT by `t`: a free 2-cell `t ⇒ t.t`.  The LARGE side of the KZ
comparison `Tη <= ηT`; folds to the monotone map `[1]` in the Delta_+ model. -/
def kzEtaTCell : RawTwoCellExpr monadModeSignature monadT monadTThenT :=
  RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT monadUnitTwoCell

/-! ## The walking-KZ 2-cell PREORDER -/

/-- ★ The **walking Kock-Zoberlein 2-cell order** `KZTwoCellLE`: the walking-monad saturated convertibility
(embedded BOTH ways via `ofMonad`) plus the single generating KZ inequality `t ◁ eta <= eta ▷ t` (`kzGen`), closed
under the four one-hole congruences and `refl` / `trans` into a genuine PREORDER.  There is deliberately NO `symm`:
the KZ comparison is DIRECTED (lax-idempotency).  `KZTwoCellLE a b` means "there is a KZ 2-cell `a => b`" in the
locally-posetal walking KZ monad. -/
inductive KZTwoCellLE :
    {sourceMode targetMode : MonadMode} →
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode} →
    RawTwoCellExpr monadModeSignature sourcePath targetPath →
    RawTwoCellExpr monadModeSignature sourcePath targetPath → Prop where
  /-- Embed a walking-monad EQUALITY of 2-cells as `<=` (applied in both directions it keeps the monad laws
  symmetric, so the order's antisymmetrization is exactly `MonadSaturatedTwoCellConv`). -/
  | ofMonad {sourceMode targetMode : MonadMode}
      {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
      {cellAlpha cellBeta : RawTwoCellExpr monadModeSignature sourcePath targetPath} :
      MonadSaturatedTwoCellConv cellAlpha cellBeta →
      KZTwoCellLE cellAlpha cellBeta
  /-- ★ The **KZ generating inequality** `t ◁ eta <= eta ▷ t` (`Tη <= ηT`) — the sole lax-idempotency generator; it
  is DIRECTED (its reverse does not hold), so the walking KZ monad is properly laxer than the idempotent one. -/
  | kzGen : KZTwoCellLE kzTEtaCell kzEtaTCell
  /-- Congruence in the LEFT factor of a vertical composite. -/
  | vcompCongrLeft {sourceMode targetMode : MonadMode}
      {oneCellF oneCellG oneCellH : ModalityPath monadGraph sourceMode targetMode}
      {cellAlpha cellAlpha' : RawTwoCellExpr monadModeSignature oneCellF oneCellG}
      (cellBeta : RawTwoCellExpr monadModeSignature oneCellG oneCellH) :
      KZTwoCellLE cellAlpha cellAlpha' →
      KZTwoCellLE (RawTwoCellExpr.vcomp cellAlpha cellBeta) (RawTwoCellExpr.vcomp cellAlpha' cellBeta)
  /-- Congruence in the RIGHT factor of a vertical composite. -/
  | vcompCongrRight {sourceMode targetMode : MonadMode}
      {oneCellF oneCellG oneCellH : ModalityPath monadGraph sourceMode targetMode}
      (cellAlpha : RawTwoCellExpr monadModeSignature oneCellF oneCellG)
      {cellBeta cellBeta' : RawTwoCellExpr monadModeSignature oneCellG oneCellH} :
      KZTwoCellLE cellBeta cellBeta' →
      KZTwoCellLE (RawTwoCellExpr.vcomp cellAlpha cellBeta) (RawTwoCellExpr.vcomp cellAlpha cellBeta')
  /-- Congruence under a left whiskering (the KZ inequality fires whiskered by a 1-cell). -/
  | whiskerLeftCongr {sourceMode middleMode targetMode : MonadMode}
      (oneCell : ModalityPath monadGraph sourceMode middleMode)
      {oneCellG oneCellH : ModalityPath monadGraph middleMode targetMode}
      {cellBeta cellBeta' : RawTwoCellExpr monadModeSignature oneCellG oneCellH} :
      KZTwoCellLE cellBeta cellBeta' →
      KZTwoCellLE (RawTwoCellExpr.whiskerLeft oneCell cellBeta) (RawTwoCellExpr.whiskerLeft oneCell cellBeta')
  /-- Congruence under a right whiskering. -/
  | whiskerRightCongr {sourceMode middleMode targetMode : MonadMode}
      {oneCellF oneCellG : ModalityPath monadGraph sourceMode middleMode}
      (oneCell : ModalityPath monadGraph middleMode targetMode)
      {cellAlpha cellAlpha' : RawTwoCellExpr monadModeSignature oneCellF oneCellG} :
      KZTwoCellLE cellAlpha cellAlpha' →
      KZTwoCellLE (RawTwoCellExpr.whiskerRight oneCell cellAlpha) (RawTwoCellExpr.whiskerRight oneCell cellAlpha')
  /-- Reflexivity. -/
  | refl {sourceMode targetMode : MonadMode}
      {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
      (cell : RawTwoCellExpr monadModeSignature sourcePath targetPath) :
      KZTwoCellLE cell cell
  /-- Transitivity (the order is a preorder; NO symmetry). -/
  | trans {sourceMode targetMode : MonadMode}
      {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
      {cellAlpha cellBeta cellGamma : RawTwoCellExpr monadModeSignature sourcePath targetPath} :
      KZTwoCellLE cellAlpha cellBeta → KZTwoCellLE cellBeta cellGamma → KZTwoCellLE cellAlpha cellGamma

/-- **KZ 2-cell EQUALITY** — the antisymmetric core of the order: `a` and `b` are KZ-equal when each is `<=` the
other.  On the walking KZ monad this coincides with walking-monad convertibility (`KZMonadDecision.kzEq_iff_mapEq`);
the poset enrichment adds order, not new equalities. -/
def KZTwoCellEq {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
    (cellA cellB : RawTwoCellExpr monadModeSignature sourcePath targetPath) : Prop :=
  KZTwoCellLE cellA cellB ∧ KZTwoCellLE cellB cellA

/-! ## Presentation witnesses -/

/-- ★ **The KZ comparison holds** — `t ◁ eta <= eta ▷ t`: the lax-idempotency inequality. -/
theorem kzComparisonHolds : KZTwoCellLE kzTEtaCell kzEtaTCell :=
  KZTwoCellLE.kzGen

/-- Every walking-monad convertibility lifts to `<=` (the `ofMonad` embedding as a theorem, so the three monad laws
are available as order facts directly). -/
theorem KZTwoCellLE.ofMonadLaw {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr monadModeSignature sourcePath targetPath}
    (conv : MonadSaturatedTwoCellConv cellAlpha cellBeta) :
    KZTwoCellLE cellAlpha cellBeta :=
  KZTwoCellLE.ofMonad conv

/-- Smoke: the KZ comparison fires UNDER a left-whisker context — `t ◁ (t ◁ eta) <= t ◁ (eta ▷ t)` — exercising the
congruence closure with the KZ generator (a genuine congruence, the whiskered lax-idempotency inequality). -/
theorem kzComparisonWhiskeredHolds :
    KZTwoCellLE
      (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT kzTEtaCell)
      (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT kzEtaTCell) :=
  KZTwoCellLE.whiskerLeftCongr _ KZTwoCellLE.kzGen

/-- Smoke: the monad LEFT-UNIT law is an order fact both ways (via `ofMonad`) — the walking KZ monad is still a
monad, its laws entering the order symmetrically. -/
theorem kzLeftUnitEq : KZTwoCellEq monadLeftUnitCell monadIdTCell :=
  ⟨KZTwoCellLE.ofMonad MonadSaturatedTwoCellConv.leftUnit,
   KZTwoCellLE.ofMonad (MonadSaturatedTwoCellConv.symm MonadSaturatedTwoCellConv.leftUnit)⟩

/-- Smoke: the KZ comparison chained through `refl`/`trans` — `t ◁ eta <= eta ▷ t` composed with reflexivity,
exercising `trans` around the generator. -/
theorem kzComparisonViaTrans : KZTwoCellLE kzTEtaCell kzEtaTCell :=
  KZTwoCellLE.trans (KZTwoCellLE.refl kzTEtaCell) KZTwoCellLE.kzGen

/-! ## Honesty marker -/

/-- **ESTABLISHED.**  The walking Kock-Zoberlein (lax-idempotent) monad PRESENTATION is shipped: the directed 2-cell
PREORDER `KZTwoCellLE` — the walking-monad convertibility both ways (`ofMonad`) plus the single KZ generating
inequality `t ◁ eta <= eta ▷ t` (`kzGen`, `Tη <= ηT`), closed under the four congruences and `refl`/`trans` with NO
`symm` (the comparison is DIRECTED — lax-idempotency).  The KZ comparison holds (`kzComparisonHolds`), fires under
whiskering (`kzComparisonWhiskeredHolds`), and the monad laws enter the order both ways (`kzLeftUnitEq`).  KZ 2-cell
equality `KZTwoCellEq` is the antisymmetric core.  `= true`. -/
def fxKZ_hasWalkingKZPresentation : Bool := true

end FX1Poly.Polygraph
