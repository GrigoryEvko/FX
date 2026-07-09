import FX1Poly.Polygraph.TwoCategory.Amalgam.DispatchLocallyThin
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadSaturatedConv

/-! # Polygraph/TwoCategory/Amalgam/SaturatedOver — the GENERIC per-presentation saturated 2-cell congruence
(WP-AMALG r3, piece 1 + the INT-SIG-ALIGN #2079 alignment)

r2's load-bearing finding: `DecidableTwoCellConvFor` (`FreeTwoCell/Model.lean`) decides the FREE 2-cell
convertibility, whose generating 2-cells enter only as opaque `gen` atoms — the doctrine RELATIONS are NOT in
that congruence.  Every shipped walking-doctrine DECISION, by contrast, decides a strictly LARGER,
doctrine-SATURATED relation (the adjunction triangles, the monad laws, the idempotence law).  The interface
mismatch is the real obstruction to re-basing the combination theorem: the deciders and the free interface speak
different word problems.

This file closes that mismatch at the GENERIC level.  Each per-lane saturated convertibility
(`MonadSaturatedTwoCellConv`, `StringSaturatedTwoCellConv`, `CohesionSaturatedTwoCellConv`, the adjunction
`SaturatedTwoCellConv`, `IdempotentMonadSaturatedTwoCellConv`) is the SAME shape: the completed
free-strict-2-category convertibility (`TwoCellConvFull`, embedded by `ofFull`) augmented with the doctrine's
laws as generating equations, made a genuine congruence by the four one-hole congruences + `refl`/`symm`/`trans`.
`SaturatedConvOver signature baseRel` is that uniform shape ABSTRACTED over an explicit law relation `baseRel` —
a `CellRel` — so every per-lane conv is an instance for its own law relation.

## The honest generic (the laws are NOT readable off `ModeComputad`)

`ModeComputad` stores generating 2-cells (the `twoCellGenerators`), NOT the doctrine LAWS (which identify
COMPOSITES of those generators — 3-cells living in no field of the computad).  So the generic cannot read a base
relation off the computad; it takes an EXPLICIT `CellRel`.  `SaturatedConvOverPushout` (in the dispatch file)
then feeds it the disjoint union of the retagged component law relations.

## What ships here (each piece zero-axiom, structural, ASCII-only)

  * **`CellRel`** — a heterogeneous relation on parallel free 2-cell expressions (the shape of a law relation).
  * **`SaturatedConvOver signature baseRel`** — the generic saturated convertibility: `ofFull` (embed
    `TwoCellConvFull`) + `ofRelation` (each law row of `baseRel` becomes a congruence generator) + the four
    one-hole congruences + `refl`/`symm`/`trans`.
  * **`SaturatedConvOver.ofConv`** — the free `TwoCellConv` lifts (through `TwoCellConvFull.ofConv`).
  * **`DecidableSaturatedConvForRel`** — the decision interface for a given `baseRel`.
  * **`emptyCellRel`** + **`saturatedLocallyThinDecider`** + **`involutionSaturatedThinDecider`** — the empty
    law relation and the TRIVIAL (no-2-generator) instance: with no rows and no generators every parallel pair
    collapses (r2's `allParallelConv_of_noGen` lifted to the saturated interface), witnessed at the involution.
  * **`MonadLawRel`** + **`monadSaturated_iff_generic`** — the INT-SIG-ALIGN #2079 exemplar: the walking monad's
    three laws as a `CellRel`, and the two-way iso `MonadSaturatedTwoCellConv a b <-> SaturatedConvOver
    monadModeSignature MonadLawRel a b`.  Each direction is one structural induction, ctor-for-ctor.  This is the
    ADDITIVE alignment: the lanes stay untouched; the generic is exhibited as their common shape.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The law-relation shape -/

/-- A **cell relation** — a heterogeneous relation on parallel free 2-cell expressions (same signature, same
boundary).  The shape a doctrine's law relation takes: `baseRel a b` asserts `a` and `b` are identified by a
generating equation.  `SaturatedConvOver` closes such a relation into a congruence over `TwoCellConvFull`. -/
abbrev CellRel (signature : ModeSignature) : Type :=
  {sourceMode targetMode : signature.graph.Mode} →
  {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
  RawTwoCellExpr signature sourcePath targetPath →
  RawTwoCellExpr signature sourcePath targetPath → Prop

/-! ## The generic saturated convertibility -/

/-- ★ The **generic per-presentation saturated 2-cell convertibility** — the uniform shape of every shipped
walking-doctrine saturated conv (INT-SIG-ALIGN #2079): the completed free-strict-2-category convertibility
(`TwoCellConvFull`, embedded by `ofFull`) augmented with an EXPLICIT law relation `baseRel` (each law row a
congruence generator via `ofRelation`), closed under the four one-hole congruences and `refl`/`symm`/`trans` into
a genuine congruence.  `MonadSaturatedTwoCellConv` is exactly `SaturatedConvOver monadModeSignature MonadLawRel`
(proven below); the string / cohesion / adjunction / idempotent convs are the same shape for their own law
relations.  The base relation is EXPLICIT because the laws (3-cells identifying composites) are not stored in a
`ModeComputad`. -/
inductive SaturatedConvOver (signature : ModeSignature) (baseRel : CellRel signature) :
    {sourceMode targetMode : signature.graph.Mode} →
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    RawTwoCellExpr signature sourcePath targetPath →
    RawTwoCellExpr signature sourcePath targetPath → Prop where
  /-- Embed the completed free-strict-2-category convertibility (structural laws + interchange + whisker
  functoriality + disjoint-whisker exchange + congruence closure). -/
  | ofFull {sourceMode targetMode : signature.graph.Mode}
      {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
      {cellAlpha cellBeta : RawTwoCellExpr signature sourcePath targetPath} :
      TwoCellConvFull signature cellAlpha cellBeta →
      SaturatedConvOver signature baseRel cellAlpha cellBeta
  /-- Embed a law row of `baseRel` as a generating equation of the congruence. -/
  | ofRelation {sourceMode targetMode : signature.graph.Mode}
      {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
      {cellAlpha cellBeta : RawTwoCellExpr signature sourcePath targetPath} :
      baseRel cellAlpha cellBeta →
      SaturatedConvOver signature baseRel cellAlpha cellBeta
  /-- Congruence in the LEFT factor of a vertical composite. -/
  | vcompCongrLeft {sourceMode targetMode : signature.graph.Mode}
      {oneCellF oneCellG oneCellH : ModalityPath signature.graph sourceMode targetMode}
      {cellAlpha cellAlpha' : RawTwoCellExpr signature oneCellF oneCellG}
      (cellBeta : RawTwoCellExpr signature oneCellG oneCellH) :
      SaturatedConvOver signature baseRel cellAlpha cellAlpha' →
      SaturatedConvOver signature baseRel (RawTwoCellExpr.vcomp cellAlpha cellBeta)
        (RawTwoCellExpr.vcomp cellAlpha' cellBeta)
  /-- Congruence in the RIGHT factor of a vertical composite. -/
  | vcompCongrRight {sourceMode targetMode : signature.graph.Mode}
      {oneCellF oneCellG oneCellH : ModalityPath signature.graph sourceMode targetMode}
      (cellAlpha : RawTwoCellExpr signature oneCellF oneCellG)
      {cellBeta cellBeta' : RawTwoCellExpr signature oneCellG oneCellH} :
      SaturatedConvOver signature baseRel cellBeta cellBeta' →
      SaturatedConvOver signature baseRel (RawTwoCellExpr.vcomp cellAlpha cellBeta)
        (RawTwoCellExpr.vcomp cellAlpha cellBeta')
  /-- Congruence under a left whiskering (so a law fires whiskered by a 1-cell). -/
  | whiskerLeftCongr {sourceMode middleMode targetMode : signature.graph.Mode}
      (oneCell : ModalityPath signature.graph sourceMode middleMode)
      {oneCellG oneCellH : ModalityPath signature.graph middleMode targetMode}
      {cellBeta cellBeta' : RawTwoCellExpr signature oneCellG oneCellH} :
      SaturatedConvOver signature baseRel cellBeta cellBeta' →
      SaturatedConvOver signature baseRel (RawTwoCellExpr.whiskerLeft oneCell cellBeta)
        (RawTwoCellExpr.whiskerLeft oneCell cellBeta')
  /-- Congruence under a right whiskering. -/
  | whiskerRightCongr {sourceMode middleMode targetMode : signature.graph.Mode}
      {oneCellF oneCellG : ModalityPath signature.graph sourceMode middleMode}
      (oneCell : ModalityPath signature.graph middleMode targetMode)
      {cellAlpha cellAlpha' : RawTwoCellExpr signature oneCellF oneCellG} :
      SaturatedConvOver signature baseRel cellAlpha cellAlpha' →
      SaturatedConvOver signature baseRel (RawTwoCellExpr.whiskerRight oneCell cellAlpha)
        (RawTwoCellExpr.whiskerRight oneCell cellAlpha')
  /-- Reflexivity. -/
  | refl {sourceMode targetMode : signature.graph.Mode}
      {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
      (cell : RawTwoCellExpr signature sourcePath targetPath) :
      SaturatedConvOver signature baseRel cell cell
  /-- Symmetry. -/
  | symm {sourceMode targetMode : signature.graph.Mode}
      {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
      {cellAlpha cellBeta : RawTwoCellExpr signature sourcePath targetPath} :
      SaturatedConvOver signature baseRel cellAlpha cellBeta →
      SaturatedConvOver signature baseRel cellBeta cellAlpha
  /-- Transitivity. -/
  | trans {sourceMode targetMode : signature.graph.Mode}
      {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
      {cellAlpha cellBeta cellGamma : RawTwoCellExpr signature sourcePath targetPath} :
      SaturatedConvOver signature baseRel cellAlpha cellBeta →
      SaturatedConvOver signature baseRel cellBeta cellGamma →
      SaturatedConvOver signature baseRel cellAlpha cellGamma

/-- The free `TwoCellConv` (structural laws + interchange) lifts to any saturated relation (through
`TwoCellConvFull.ofConv`). -/
theorem SaturatedConvOver.ofConv {signature : ModeSignature} {baseRel : CellRel signature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr signature sourcePath targetPath}
    (conv : TwoCellConv signature cellAlpha cellBeta) :
    SaturatedConvOver signature baseRel cellAlpha cellBeta :=
  SaturatedConvOver.ofFull (TwoCellConvFull.ofConv conv)

/-! ## The universal property — the eliminator into any absorbing congruence

`SaturatedConvOver signature baseRel` is the FREEST congruence absorbing both `TwoCellConvFull` and `baseRel`;
mapping OUT of it (the backward direction of every per-lane iso) is exactly recursion into a target relation `R`
that is itself such a congruence.  Packaging the absorption as `IsSaturatedCongruence` lets the eliminator
`recInto` induct with `signature` / `baseRel` as genuine VARIABLES — sidestepping the `monadModeSignature.graph`
vs `monadGraph` defeq that blocks `induction` when the parameters are the concrete monad signature. -/

/-- A target relation `R` **absorbs** the generic saturated congruence over `baseRel` — closed under the
`TwoCellConvFull` image, the law rows, the four one-hole congruences, and `refl`/`symm`/`trans`.  The universal
property's hypothesis: any such `R` receives a map from `SaturatedConvOver signature baseRel`. -/
structure IsSaturatedCongruence (signature : ModeSignature) (baseRel : CellRel signature)
    (targetRel : CellRel signature) : Prop where
  /-- Absorb the completed free convertibility. -/
  ofFull : {sourceMode targetMode : signature.graph.Mode} →
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    {cellAlpha cellBeta : RawTwoCellExpr signature sourcePath targetPath} →
    TwoCellConvFull signature cellAlpha cellBeta → targetRel cellAlpha cellBeta
  /-- Absorb a law row. -/
  ofRelation : {sourceMode targetMode : signature.graph.Mode} →
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    {cellAlpha cellBeta : RawTwoCellExpr signature sourcePath targetPath} →
    baseRel cellAlpha cellBeta → targetRel cellAlpha cellBeta
  /-- Congruence in the left factor of a vertical composite. -/
  vcompCongrLeft : {sourceMode targetMode : signature.graph.Mode} →
    {oneCellF oneCellG oneCellH : ModalityPath signature.graph sourceMode targetMode} →
    {cellAlpha cellAlpha' : RawTwoCellExpr signature oneCellF oneCellG} →
    {cellBeta : RawTwoCellExpr signature oneCellG oneCellH} →
    targetRel cellAlpha cellAlpha' →
    targetRel (RawTwoCellExpr.vcomp cellAlpha cellBeta) (RawTwoCellExpr.vcomp cellAlpha' cellBeta)
  /-- Congruence in the right factor of a vertical composite. -/
  vcompCongrRight : {sourceMode targetMode : signature.graph.Mode} →
    {oneCellF oneCellG oneCellH : ModalityPath signature.graph sourceMode targetMode} →
    {cellAlpha : RawTwoCellExpr signature oneCellF oneCellG} →
    {cellBeta cellBeta' : RawTwoCellExpr signature oneCellG oneCellH} →
    targetRel cellBeta cellBeta' →
    targetRel (RawTwoCellExpr.vcomp cellAlpha cellBeta) (RawTwoCellExpr.vcomp cellAlpha cellBeta')
  /-- Congruence under a left whiskering. -/
  whiskerLeftCongr : {sourceMode middleMode targetMode : signature.graph.Mode} →
    {oneCell : ModalityPath signature.graph sourceMode middleMode} →
    {oneCellG oneCellH : ModalityPath signature.graph middleMode targetMode} →
    {cellBeta cellBeta' : RawTwoCellExpr signature oneCellG oneCellH} →
    targetRel cellBeta cellBeta' →
    targetRel (RawTwoCellExpr.whiskerLeft oneCell cellBeta) (RawTwoCellExpr.whiskerLeft oneCell cellBeta')
  /-- Congruence under a right whiskering. -/
  whiskerRightCongr : {sourceMode middleMode targetMode : signature.graph.Mode} →
    {oneCellF oneCellG : ModalityPath signature.graph sourceMode middleMode} →
    {oneCell : ModalityPath signature.graph middleMode targetMode} →
    {cellAlpha cellAlpha' : RawTwoCellExpr signature oneCellF oneCellG} →
    targetRel cellAlpha cellAlpha' →
    targetRel (RawTwoCellExpr.whiskerRight oneCell cellAlpha) (RawTwoCellExpr.whiskerRight oneCell cellAlpha')
  /-- Reflexivity. -/
  refl : {sourceMode targetMode : signature.graph.Mode} →
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    (cell : RawTwoCellExpr signature sourcePath targetPath) → targetRel cell cell
  /-- Symmetry. -/
  symm : {sourceMode targetMode : signature.graph.Mode} →
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    {cellAlpha cellBeta : RawTwoCellExpr signature sourcePath targetPath} →
    targetRel cellAlpha cellBeta → targetRel cellBeta cellAlpha
  /-- Transitivity. -/
  trans : {sourceMode targetMode : signature.graph.Mode} →
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    {cellAlpha cellBeta cellGamma : RawTwoCellExpr signature sourcePath targetPath} →
    targetRel cellAlpha cellBeta → targetRel cellBeta cellGamma → targetRel cellAlpha cellGamma

/-- ★ **The universal property of `SaturatedConvOver`** — its eliminator into any absorbing congruence `R`.  With
`signature` / `baseRel` / `targetRel` genuine variables the induction is clean (no concrete-signature defeq to
fight); every backward-direction lane iso is an instance. -/
theorem SaturatedConvOver.recInto {signature : ModeSignature} {baseRel targetRel : CellRel signature}
    (cong : IsSaturatedCongruence signature baseRel targetRel)
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr signature sourcePath targetPath}
    (conv : SaturatedConvOver signature baseRel cellAlpha cellBeta) :
    targetRel cellAlpha cellBeta := by
  induction conv with
  | ofFull full => exact cong.ofFull full
  | ofRelation row => exact cong.ofRelation row
  | vcompCongrLeft _ _ ih => exact cong.vcompCongrLeft ih
  | vcompCongrRight _ _ ih => exact cong.vcompCongrRight ih
  | whiskerLeftCongr _ _ ih => exact cong.whiskerLeftCongr ih
  | whiskerRightCongr _ _ ih => exact cong.whiskerRightCongr ih
  | refl cell => exact cong.refl cell
  | symm _ ih => exact cong.symm ih
  | trans _ _ ihLeft ihRight => exact cong.trans ihLeft ihRight

/-! ## The decision interface + the empty law relation -/

/-- The **saturated-convertibility decision interface** for a given law relation `baseRel`: saturated
convertibility is decidable on every parallel pair of free 2-cells.  This is the saturated analog of
`DecidableTwoCellConvFor` — the CORRECT target interface that the r2 finding showed the walker decisions
actually inhabit. -/
def DecidableSaturatedConvForRel (signature : ModeSignature) (baseRel : CellRel signature) : Type :=
  {sourceMode targetMode : signature.graph.Mode} →
  {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
  (cellAlpha cellBeta : RawTwoCellExpr signature sourcePath targetPath) →
  Decidable (SaturatedConvOver signature baseRel cellAlpha cellBeta)

/-- The **empty law relation** — no generating equations.  `SaturatedConvOver signature (emptyCellRel signature)`
is then just the completed free convertibility `TwoCellConvFull` closed again (idempotently) under congruence. -/
def emptyCellRel (signature : ModeSignature) : CellRel signature :=
  fun _ _ => False

/-- ★ **The saturated locally-thin decider** — in a no-generating-2-cell signature, every parallel free 2-cell
pair is convertible (r2's `allParallelConv_of_noGen` gives the `TwoCellConv`, lifted through `ofConv`), so the
saturated decision with the empty law relation is `isTrue` everywhere.  The trivial (second) instance of the
saturated decision interface — free conv IS saturated conv when there are no rows and no generators. -/
def saturatedLocallyThinDecider {signature : ModeSignature} (noGen : SignatureHasNoTwoGen signature) :
    DecidableSaturatedConvForRel signature (emptyCellRel signature) :=
  fun cellAlpha cellBeta =>
    Decidable.isTrue (SaturatedConvOver.ofConv (allParallelConv_of_noGen noGen cellAlpha cellBeta))

/-- ★ **The walking-involution saturated component decider** — the concrete trivial instance: the involution's
`s.s = id` relation is 1-cell level, so `twoCellGenerators = []`, and its saturated conv (empty law relation) is
decided by local thinness. -/
def involutionSaturatedThinDecider :
    DecidableSaturatedConvForRel involutionComputad.toModeSignature
      (emptyCellRel involutionComputad.toModeSignature) :=
  saturatedLocallyThinDecider involution_noGen

/-! ## INT-SIG-ALIGN #2079: the walking monad's saturated conv IS the generic at `MonadLawRel` -/

/-- The **walking monad's three laws as a `CellRel`** — left unit, right unit, associativity, each a law row.
The base relation for which `SaturatedConvOver monadModeSignature MonadLawRel = MonadSaturatedTwoCellConv`. -/
inductive MonadLawRel :
    {sourceMode targetMode : MonadMode} →
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode} →
    RawTwoCellExpr monadModeSignature sourcePath targetPath →
    RawTwoCellExpr monadModeSignature sourcePath targetPath → Prop where
  /-- The left-unit law `mu . (eta |> t) ~ id_t`. -/
  | leftUnit : MonadLawRel monadLeftUnitCell monadIdTCell
  /-- The right-unit law `mu . (t <| eta) ~ id_t`. -/
  | rightUnit : MonadLawRel monadRightUnitCell monadIdTCell
  /-- The associativity law `mu . (mu |> t) ~ mu . (t <| mu)`. -/
  | assoc : MonadLawRel monadAssocLeftCell monadAssocRightCell

/-- Forward direction of the INT-SIG-ALIGN exemplar: the walking monad's saturated conv maps into the generic at
`MonadLawRel`.  Structural induction, each ctor to the same-named generic ctor; the three laws land as
`ofRelation`. -/
theorem monadSaturated_to_generic {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr monadModeSignature sourcePath targetPath}
    (conv : MonadSaturatedTwoCellConv cellAlpha cellBeta) :
    SaturatedConvOver monadModeSignature MonadLawRel cellAlpha cellBeta := by
  induction conv with
  | ofFull full => exact SaturatedConvOver.ofFull full
  | leftUnit => exact SaturatedConvOver.ofRelation MonadLawRel.leftUnit
  | rightUnit => exact SaturatedConvOver.ofRelation MonadLawRel.rightUnit
  | assoc => exact SaturatedConvOver.ofRelation MonadLawRel.assoc
  | vcompCongrLeft cellBeta _ ih => exact SaturatedConvOver.vcompCongrLeft cellBeta ih
  | vcompCongrRight cellAlpha _ ih => exact SaturatedConvOver.vcompCongrRight cellAlpha ih
  | whiskerLeftCongr oneCell _ ih => exact SaturatedConvOver.whiskerLeftCongr oneCell ih
  | whiskerRightCongr oneCell _ ih => exact SaturatedConvOver.whiskerRightCongr oneCell ih
  | refl cell => exact SaturatedConvOver.refl cell
  | symm _ ih => exact SaturatedConvOver.symm ih
  | trans _ _ ihLeft ihRight => exact SaturatedConvOver.trans ihLeft ihRight

/-- The walking monad's saturated conv absorbs the generic congruence at `MonadLawRel` — the `ofRelation` field
cases each law row into the matching monad-law ctor; every other field is a same-named `MonadSaturatedTwoCellConv`
ctor.  This is the backward-direction witness, packaged for `recInto`. -/
def monadSaturatedIsCongruence :
    IsSaturatedCongruence monadModeSignature MonadLawRel
      (fun cellAlpha cellBeta => MonadSaturatedTwoCellConv cellAlpha cellBeta) where
  ofFull full := MonadSaturatedTwoCellConv.ofFull full
  ofRelation row :=
    match row with
    | MonadLawRel.leftUnit => MonadSaturatedTwoCellConv.leftUnit
    | MonadLawRel.rightUnit => MonadSaturatedTwoCellConv.rightUnit
    | MonadLawRel.assoc => MonadSaturatedTwoCellConv.assoc
  vcompCongrLeft {_ _ _ _ _ _ _ cellBeta} ih := MonadSaturatedTwoCellConv.vcompCongrLeft cellBeta ih
  vcompCongrRight {_ _ _ _ _ cellAlpha _ _} ih := MonadSaturatedTwoCellConv.vcompCongrRight cellAlpha ih
  whiskerLeftCongr {_ _ _ oneCell _ _ _ _} ih := MonadSaturatedTwoCellConv.whiskerLeftCongr oneCell ih
  whiskerRightCongr {_ _ _ _ _ oneCell _ _} ih := MonadSaturatedTwoCellConv.whiskerRightCongr oneCell ih
  refl cell := MonadSaturatedTwoCellConv.refl cell
  symm ih := MonadSaturatedTwoCellConv.symm ih
  trans ihLeft ihRight := MonadSaturatedTwoCellConv.trans ihLeft ihRight

/-- Backward direction: the generic at `MonadLawRel` maps back into the walking monad's saturated conv (via the
universal property `recInto` with the monad congruence). -/
theorem generic_to_monadSaturated {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr monadModeSignature sourcePath targetPath}
    (conv : SaturatedConvOver monadModeSignature MonadLawRel cellAlpha cellBeta) :
    MonadSaturatedTwoCellConv cellAlpha cellBeta :=
  SaturatedConvOver.recInto monadSaturatedIsCongruence conv

/-- ★ **INT-SIG-ALIGN #2079 exemplar** — the walking monad's saturated conv IS the generic saturated conv at its
law relation `MonadLawRel`.  The additive alignment: the per-lane conv (`MonadSaturatedTwoCellConv`, untouched)
and the generic (`SaturatedConvOver monadModeSignature MonadLawRel`) are logically identical, exhibiting the
generic as the common shape of all the walking-doctrine convs. -/
theorem monadSaturated_iff_generic {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
    (cellAlpha cellBeta : RawTwoCellExpr monadModeSignature sourcePath targetPath) :
    MonadSaturatedTwoCellConv cellAlpha cellBeta
      ↔ SaturatedConvOver monadModeSignature MonadLawRel cellAlpha cellBeta :=
  ⟨monadSaturated_to_generic, generic_to_monadSaturated⟩

/-! ## Honesty markers -/

/-- ★ **Honesty marker — the GENERIC per-presentation saturated 2-cell congruence SHIPS (r3 piece 1).**  The law
relation shape (`CellRel`), the generic saturated convertibility (`SaturatedConvOver signature baseRel` =
`TwoCellConvFull` + explicit law rows + congruence closure), the free lift (`ofConv`), the decision interface
(`DecidableSaturatedConvForRel`), the empty-relation trivial instance (`saturatedLocallyThinDecider`,
`involutionSaturatedThinDecider`), and the INT-SIG-ALIGN #2079 exemplar (`monadSaturated_iff_generic`: the
walking monad's saturated conv IS the generic at `MonadLawRel`).  This closes the r2 interface mismatch at the
generic level: the walker decisions and the free interface spoke different word problems; the generic is the
common shape the decisions actually inhabit.  Additive — the walker lanes are untouched.  `= true`. -/
def fxAmalg_hasSaturatedConvOver : Bool := true

end FX1Poly.Polygraph.Amalgam
