import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutMonotoneReflection
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.TotalWordProblemDecision

/-! # Polygraph/TwoCategory/Amalgam/ComposableFragmentDispatch — the composable saturated dispatch for the
provably-empty-law fragment, purified onto the FREE word problem (WP-AMALG r9)

r8 (`PushoutBundle.lean`) discharged the arity-fold soundness bundle and shipped the CONDITIONAL-then-unconditional
non-convertibility of the specific interleaving pair (`crossPairPushoutNonConvUnconditional`).  What it did NOT
ship was a LIVE combined `Decidable` — a `DecidableSaturatedConvForRel` that COMPUTES `isTrue`/`isFalse` on
arbitrary pairs over the pushout, composably wired from component deciders.  This file ships exactly that, for the
one fragment where the categorical Nelson-Oppen combination is UNCONDITIONAL: the provably-empty law relation.

## The purification, honestly

The recon's two candidate routes were derivation-surgery (reorganize a pushout derivation so the interchange mixer
cancels) and the projection invariant (fold each cell to a conv-invariant).  Derivation surgery is a KNOWN dead end
— `SAT-CONF` (#1992) and `SAT-NF` (#1993) machine-REFUTED local confluence of the free pushout rewriting on the
interchange / whiskered-snake pair, and any reorganize-to-cancel argument needs that confluence.  So we take the
projection, and for the empty-law fragment the projection is EXACT and total: the target invariant is
`TwoCellConvFull`-membership itself.

`SaturatedConvOver signature baseRel` is `TwoCellConvFull` + the law rows (`ofRelation`) + congruence closure.
When `baseRel` has no fireable rows (`ofRelation` is `False.elim`), the closure adds NOTHING beyond `TwoCellConvFull`
(which is already a congruence), so `SaturatedConvOver signature baseRel ↔ TwoCellConvFull signature` — the
projection to `TwoCellConvFull` is exact.  The `ofRelation` constructor is the SOLE conservativity boundary: for a
NON-empty relation it genuinely adds identifications that `TwoCellConvFull` lacks, and the projection fails there
(the walled real-relation case, §RELFAM below).  This is the Toyama observation made precise — modularity of the
word problem holds for the disjoint / empty-crossing-law case (Toyama 1987, `confluence IS modular`), and this file
is its 2-categorical instance: the empty-law amalgam's word problem IS the free pushout word problem, decided by
the FREE decision `decideTwoCellConvFull` (FREE-7, `fxMode_hasUngatedFreeTwoCellDecision`).

## What ships here (each piece zero-axiom, structural, ASCII-only)

  * **`emptyRowsFullCongruence` / `saturatedConvOverEmptyRows_toFull` / `saturatedConvOverEmptyRows_iff_full`** —
    the projection invariant (P1/P2): `SaturatedConvOver` over a provably-empty relation reflects EXACTLY to
    `TwoCellConvFull`, via `SaturatedConvOver.recInto` through the target congruence `TwoCellConvFull`.  Per-ctor
    preservation over all 9 constructors; `ofRelation` = `False.elim` is the conservativity boundary.
  * **`decidableSaturatedConvOverReconstructed`** — the generic decider: over ANY `ModeComputad`'s reconstructed
    signature with a provably-empty law relation, saturated convertibility is `Decidable` (the free
    `decideTwoCellConvFull` transported through the projection iff; the reconstructed `DecidableEq` data is free —
    `Fin` modes, subtype 1-generators, subtype 2-generators).
  * **`combinedDecidableSaturatedConvForRel`** — the composable dispatch (P3): a `DecidableSaturatedConvForRel`
    over the pushout at the `SaturatedConvOverPushout` base relation, from the two component-relation emptiness
    hypotheses.  Interface-out.
  * **`saturatedEmptyRowsPushoutDispatch`** — the interface-in/out form: a genuine `SaturatedDispatchDecidability`
    STORING two component deciders `dl`/`dr` and producing the combined decider (the free route).
  * **`saturatedConvOverPushoutRows_empty`** — the composability enabler: the OUTPUT pushout relation is itself
    provably empty (given the component relations empty), so the dispatch's output feeds back as a component input
    (n-ary fold, 2-generators allowed — strictly generalizing the thin fold `threeWayThinFold`).
  * **`monadWalkerSaturatedDecider`** — a REAL walker decider (the shipped walking-monad saturated decision
    `monadSaturatedTwoCellDecision`) wrapped at the generic `DecidableSaturatedConvForRel` interface via the
    INT-SIG-ALIGN iso `monadSaturated_iff_generic`; `#eval`'d isTrue/isFalse on real monad pairs.
  * **`involutionMonadEmptyRowsDispatch`** — the concrete instance at `involution +_M monad`, storing the REAL
    walking-involution walker `involutionSaturatedThinDecider` as `dl` and the free monad decider as `dr`, with the
    combined decider deciding the interleaving pair `crossPairAlpha` vs `crossPairBeta` `isFalse` and reflexive
    pairs `isTrue` — both `#eval`'d.

## The residual (the marker stays honest)

`fxAmalg_hasGeneralPushoutDispatch` (`PushoutBundle.lean`) stays `false`: the GENERAL combination (a component
contributing genuine, fireable laws) needs the Nelson-Oppen / Baader-Tinelli purification completeness for
wire-creating (unit/mult) generators PLUS the reconstruction-faithfulness reseat (`DeciderReseat.lean`, to feed a
bespoke-signature walker decider as a component).  This file flips ONLY the empty-law fragment marker
`fxAmalg_hasComposableFragmentDispatch`.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## P1 — the projection invariant: `SaturatedConvOver` over an empty relation collapses onto `TwoCellConvFull`

The target congruence is `TwoCellConvFull` itself.  Each `SaturatedConvOver` constructor maps to the same-named
`TwoCellConvFull` constructor; the ONLY constructor that could genuinely widen the relation, `ofRelation`, is
absorbed by `False.elim` when the base relation has no fireable rows.  This is the per-ctor-over-all-9 preservation
the recon named; `ofRelation` is the exact conservativity boundary. -/

/-- The completed convertibility `TwoCellConvFull` absorbs the generic saturated congruence over a PROVABLY-EMPTY
law relation.  `ofFull` is the identity (the image already IS `TwoCellConvFull`); `ofRelation` is `False.elim` on
the empty rows (the conservativity boundary — a real relation would break exactly here); the four one-hole
congruences and `refl`/`symm`/`trans` are `TwoCellConvFull`'s own constructors (it is already a congruence).
Packaged for `SaturatedConvOver.recInto`. -/
def emptyRowsFullCongruence {signature : ModeSignature} {baseRel : CellRel signature}
    (rowsEmpty : {sourceMode targetMode : signature.graph.Mode} →
      {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
      {cellAlpha cellBeta : RawTwoCellExpr signature sourcePath targetPath} →
      baseRel cellAlpha cellBeta → False) :
    IsSaturatedCongruence signature baseRel (fun cellAlpha cellBeta => TwoCellConvFull signature cellAlpha cellBeta) where
  ofFull full := full
  ofRelation row := (rowsEmpty row).elim
  vcompCongrLeft {_ _ _ _ _ _ _ cellBeta} ih := TwoCellConvFull.vcompCongrLeft cellBeta ih
  vcompCongrRight {_ _ _ _ _ cellAlpha _ _} ih := TwoCellConvFull.vcompCongrRight cellAlpha ih
  whiskerLeftCongr {_ _ _ oneCell _ _ _ _} ih := TwoCellConvFull.whiskerLeftCongr oneCell ih
  whiskerRightCongr {_ _ _ _ _ oneCell _ _} ih := TwoCellConvFull.whiskerRightCongr oneCell ih
  refl cell := TwoCellConvFull.refl cell
  symm ih := TwoCellConvFull.symm ih
  trans ihLeft ihRight := TwoCellConvFull.trans ihLeft ihRight

/-- ★ **Forward projection (P1)** — a saturated convertibility over a provably-empty relation IS a completed free
convertibility, via `SaturatedConvOver.recInto` through `emptyRowsFullCongruence`.  Every intermediate cell of the
derivation is absorbed by `TwoCellConvFull`'s own congruence; no law row ever fires. -/
theorem saturatedConvOverEmptyRows_toFull {signature : ModeSignature} {baseRel : CellRel signature}
    (rowsEmpty : {sourceMode targetMode : signature.graph.Mode} →
      {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
      {cellAlpha cellBeta : RawTwoCellExpr signature sourcePath targetPath} →
      baseRel cellAlpha cellBeta → False)
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr signature sourcePath targetPath}
    (conv : SaturatedConvOver signature baseRel cellAlpha cellBeta) :
    TwoCellConvFull signature cellAlpha cellBeta :=
  SaturatedConvOver.recInto (emptyRowsFullCongruence rowsEmpty) conv

/-- ★ **The reflection theorem (P2)** — over a provably-empty law relation the saturated convertibility and the
completed free convertibility are logically IDENTICAL.  Forward via `saturatedConvOverEmptyRows_toFull` (the
projection); backward via `SaturatedConvOver.ofFull` (the free convertibility embeds).  Pure-pure saturated conv
reflects EXACTLY to free conv — the empty-fragment faithfulness. -/
theorem saturatedConvOverEmptyRows_iff_full {signature : ModeSignature} {baseRel : CellRel signature}
    (rowsEmpty : {sourceMode targetMode : signature.graph.Mode} →
      {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
      {cellAlpha cellBeta : RawTwoCellExpr signature sourcePath targetPath} →
      baseRel cellAlpha cellBeta → False)
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (cellAlpha cellBeta : RawTwoCellExpr signature sourcePath targetPath) :
    SaturatedConvOver signature baseRel cellAlpha cellBeta ↔ TwoCellConvFull signature cellAlpha cellBeta :=
  ⟨saturatedConvOverEmptyRows_toFull rowsEmpty, SaturatedConvOver.ofFull⟩

/-! ## The reconstructed-signature decidable-equality data (free)

`decideTwoCellConvFull` (FREE-7) needs `DecidableEq` on modes, 1-generators, and generating 2-cells.  For any
`ModeComputad.toModeSignature` these are all free: modes are `Fin modeCount`, 1-generators are the subtype
`ModeComputad.Modality` (shipped instance), 2-generators are the `@[reducible]` subtype
`ModeComputad.ReconstructedTwoCell` — both proof-irrelevant `Fin`-subtypes. -/

/-- The reconstructed signature's mode `DecidableEq` — `Fin modeCount`. -/
def reconstructedSignatureModeDecEq (computad : ModeComputad) :
    DecidableEq computad.toModeSignature.graph.Mode :=
  inferInstanceAs (DecidableEq (Fin computad.modeCount))

/-- The reconstructed signature's 1-generator `DecidableEq` — the shipped proof-irrelevant subtype instance. -/
def reconstructedSignatureModalityDecEq (computad : ModeComputad)
    (sourceMode targetMode : computad.toModeSignature.graph.Mode) :
    DecidableEq (computad.toModeSignature.graph.Modality sourceMode targetMode) :=
  inferInstanceAs (DecidableEq (computad.Modality sourceMode targetMode))

/-- The reconstructed signature's generating-2-cell `DecidableEq` — the proof-irrelevant `Fin`-subtype
`ReconstructedTwoCell`. -/
def reconstructedSignatureTwoCellDecEq (computad : ModeComputad)
    {sourceMode targetMode : computad.toModeSignature.graph.Mode}
    (sourcePath targetPath : ModalityPath computad.toModeSignature.graph sourceMode targetMode) :
    DecidableEq (computad.toModeSignature.twoCell sourcePath targetPath) :=
  inferInstanceAs (DecidableEq (computad.ReconstructedTwoCell sourcePath targetPath))

/-! ## The generic empty-relation decider over a reconstructed signature -/

/-- ★ **The empty-law saturated decider over a reconstructed signature.**  Over any `ModeComputad`'s reconstructed
signature with a provably-empty law relation, saturated convertibility is decided by the FREE decision
`decideTwoCellConvFull` (FREE-7) transported through the projection iff `saturatedConvOverEmptyRows_iff_full`.  The
`DecidableEq` data is the free reconstructed-signature bundle.  This is the whole computational content of the
empty-law dispatch — 2-generators ARE allowed (the free word problem is nontrivial), only fireable LAW rows are
excluded. -/
def decidableSaturatedConvOverReconstructed (computad : ModeComputad)
    {baseRel : CellRel computad.toModeSignature}
    (rowsEmpty : {sourceMode targetMode : computad.toModeSignature.graph.Mode} →
      {sourcePath targetPath : ModalityPath computad.toModeSignature.graph sourceMode targetMode} →
      {cellAlpha cellBeta : RawTwoCellExpr computad.toModeSignature sourcePath targetPath} →
      baseRel cellAlpha cellBeta → False) :
    DecidableSaturatedConvForRel computad.toModeSignature baseRel :=
  fun cellAlpha cellBeta =>
    match decideTwoCellConvFull (reconstructedSignatureModeDecEq computad)
        (reconstructedSignatureModalityDecEq computad)
        (reconstructedSignatureTwoCellDecEq computad) cellAlpha cellBeta with
    | isTrue full => isTrue ((saturatedConvOverEmptyRows_iff_full rowsEmpty cellAlpha cellBeta).mpr full)
    | isFalse notFull =>
        isFalse (fun conv => notFull ((saturatedConvOverEmptyRows_iff_full rowsEmpty cellAlpha cellBeta).mp conv))

/-! ## The composability enabler: the pushout relation is provably empty when its components are -/

/-- ★ **The pushout law relation is provably empty when both component relations are.**  Both constructors of
`SaturatedConvOverPushout` (`left`, `right`) carry a component-relation hypothesis, so if both component relations
have no fireable rows the pushout relation has none either.  This is the composability enabler: the OUTPUT of the
empty-fragment dispatch (whose relation is `SaturatedConvOverPushout …`) satisfies the emptiness hypothesis of the
NEXT dispatch level, so the fold is n-ary — 2-generators permitted, strictly generalizing the thin fold. -/
theorem saturatedConvOverPushoutRows_empty {comp1 comp2 : ModeComputad}
    {sameModes : comp1.modeCount = comp2.modeCount}
    {inclLeft : ComputadMorphismTwo comp1 (pushoutShared comp1 comp2 sameModes)}
    {inclRight : ComputadMorphismTwo comp2 (pushoutShared comp1 comp2 sameModes)}
    {baseRel1 : CellRel comp1.toModeSignature} {baseRel2 : CellRel comp2.toModeSignature}
    (rows1Empty : {sourceMode targetMode : comp1.toModeSignature.graph.Mode} →
      {sourcePath targetPath : ModalityPath comp1.toModeSignature.graph sourceMode targetMode} →
      {cellAlpha cellBeta : RawTwoCellExpr comp1.toModeSignature sourcePath targetPath} →
      baseRel1 cellAlpha cellBeta → False)
    (rows2Empty : {sourceMode targetMode : comp2.toModeSignature.graph.Mode} →
      {sourcePath targetPath : ModalityPath comp2.toModeSignature.graph sourceMode targetMode} →
      {cellAlpha cellBeta : RawTwoCellExpr comp2.toModeSignature sourcePath targetPath} →
      baseRel2 cellAlpha cellBeta → False)
    {sourceMode targetMode : (pushoutShared comp1 comp2 sameModes).toModeSignature.graph.Mode}
    {sourcePath targetPath :
      ModalityPath (pushoutShared comp1 comp2 sameModes).toModeSignature.graph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr (pushoutShared comp1 comp2 sameModes).toModeSignature sourcePath targetPath}
    (row : SaturatedConvOverPushout comp1 comp2 sameModes inclLeft inclRight baseRel1 baseRel2 cellAlpha cellBeta) :
    False := by
  cases row with
  | left componentRow => exact rows1Empty componentRow
  | right componentRow => exact rows2Empty componentRow

/-! ## P3 — the composable dispatch -/

/-- ★ **The composable saturated dispatch, empty-law fragment (interface-out).**  A `DecidableSaturatedConvForRel`
over the pushout at the `SaturatedConvOverPushout` base relation, produced from the two component-relation
emptiness hypotheses via the free decider `decidableSaturatedConvOverReconstructed`.  This is the LIVE combined
decision that r8 lacked: it COMPUTES `isTrue`/`isFalse` on arbitrary pushout pairs.  The honest fragment
hypothesis is the emptiness of both component law relations (the MODE-ADMIT #2214 gate will discharge it per
instance for admissible presentations). -/
def combinedDecidableSaturatedConvForRel (comp1 comp2 : ModeComputad)
    (sameModes : comp1.modeCount = comp2.modeCount)
    (inclLeft : ComputadMorphismTwo comp1 (pushoutShared comp1 comp2 sameModes))
    (inclRight : ComputadMorphismTwo comp2 (pushoutShared comp1 comp2 sameModes))
    {baseRel1 : CellRel comp1.toModeSignature} {baseRel2 : CellRel comp2.toModeSignature}
    (rows1Empty : {sourceMode targetMode : comp1.toModeSignature.graph.Mode} →
      {sourcePath targetPath : ModalityPath comp1.toModeSignature.graph sourceMode targetMode} →
      {cellAlpha cellBeta : RawTwoCellExpr comp1.toModeSignature sourcePath targetPath} →
      baseRel1 cellAlpha cellBeta → False)
    (rows2Empty : {sourceMode targetMode : comp2.toModeSignature.graph.Mode} →
      {sourcePath targetPath : ModalityPath comp2.toModeSignature.graph sourceMode targetMode} →
      {cellAlpha cellBeta : RawTwoCellExpr comp2.toModeSignature sourcePath targetPath} →
      baseRel2 cellAlpha cellBeta → False) :
    DecidableSaturatedConvForRel (pushoutShared comp1 comp2 sameModes).toModeSignature
      (SaturatedConvOverPushout comp1 comp2 sameModes inclLeft inclRight baseRel1 baseRel2) :=
  decidableSaturatedConvOverReconstructed (pushoutShared comp1 comp2 sameModes)
    (fun row => saturatedConvOverPushoutRows_empty rows1Empty rows2Empty row)

/-- ★ **The interface-in/out form** — a genuine `SaturatedDispatchDecidability` STORING the two component deciders
`dl`/`dr` (the Nelson-Oppen "both components decided" preconditions) and the disjoint-generator condition, and
producing the combined decider through the free route.  "Decider in ⟹ decider out": `combinedDecider` has EXACTLY
the component-decider interface type, so it feeds back into a further amalgam (the `saturatedConvOverPushoutRows_empty`
enabler makes its relation provably empty).  For the empty fragment the combined decision reduces to the free word
problem and does not consult `dl`/`dr` computationally — the honest conservativity: with no crossing law, combination
degenerates to the free pushout word problem (Toyama modularity). -/
def saturatedEmptyRowsPushoutDispatch (comp1 comp2 : ModeComputad)
    (sameModes : comp1.modeCount = comp2.modeCount)
    (inclLeft : ComputadMorphismTwo comp1 (pushoutShared comp1 comp2 sameModes))
    (inclRight : ComputadMorphismTwo comp2 (pushoutShared comp1 comp2 sameModes))
    {baseRel1 : CellRel comp1.toModeSignature} {baseRel2 : CellRel comp2.toModeSignature}
    (rows1Empty : {sourceMode targetMode : comp1.toModeSignature.graph.Mode} →
      {sourcePath targetPath : ModalityPath comp1.toModeSignature.graph sourceMode targetMode} →
      {cellAlpha cellBeta : RawTwoCellExpr comp1.toModeSignature sourcePath targetPath} →
      baseRel1 cellAlpha cellBeta → False)
    (rows2Empty : {sourceMode targetMode : comp2.toModeSignature.graph.Mode} →
      {sourcePath targetPath : ModalityPath comp2.toModeSignature.graph sourceMode targetMode} →
      {cellAlpha cellBeta : RawTwoCellExpr comp2.toModeSignature sourcePath targetPath} →
      baseRel2 cellAlpha cellBeta → False)
    (disjoint :
      computadGeneratorsDisjoint comp1.modalityGenerators.length (pushoutShared comp1 comp2 sameModes) = true)
    (dl : DecidableSaturatedConvForRel comp1.toModeSignature baseRel1)
    (dr : DecidableSaturatedConvForRel comp2.toModeSignature baseRel2) :
    SaturatedDispatchDecidability comp1 comp2 sameModes baseRel1 baseRel2
      (SaturatedConvOverPushout comp1 comp2 sameModes inclLeft inclRight baseRel1 baseRel2) where
  componentOneDecider := dl
  componentTwoDecider := dr
  generatorsDisjoint := disjoint
  combinedDecider :=
    combinedDecidableSaturatedConvForRel comp1 comp2 sameModes inclLeft inclRight rows1Empty rows2Empty

/-! ## Wrapping a REAL walker decider at the generic interface

The shipped walking-monad saturated decision `monadSaturatedTwoCellDecision` (WP-MONAD-4) decides
`MonadSaturatedTwoCellConv`; the INT-SIG-ALIGN iso `monadSaturated_iff_generic` (`SaturatedOver.lean`) identifies
that with the generic `SaturatedConvOver monadModeSignature MonadLawRel`.  Transporting the decision through the iso
(propext-free — the iso's `mp`/`mpr` are structural inductions) presents the real walker at the composable
`DecidableSaturatedConvForRel` interface, closing the r2 interface mismatch operationally (not just
propositionally). -/

/-- ★ **The walking-monad walker decider, at the generic saturated interface.**  The real shipped decision
`monadSaturatedTwoCellDecision` transported through `monadSaturated_iff_generic` — a genuine
`DecidableSaturatedConvForRel monadModeSignature MonadLawRel` that COMPUTES on real monad pairs.  This is a REAL
walker decider inhabiting the composable component-decider interface.  It cannot yet be fed as a `dl`/`dr` of the
computad pushout combinator because it lives over the BESPOKE `monadModeSignature`, not the RECONSTRUCTED
`monadComputad.toModeSignature` — the reconstruction reseat (`DeciderReseat.lean`) is the standing wall for
crossing that boundary. -/
def monadWalkerSaturatedDecider : DecidableSaturatedConvForRel monadModeSignature MonadLawRel :=
  fun cellAlpha cellBeta =>
    match monadSaturatedTwoCellDecision cellAlpha cellBeta with
    | isTrue conv => isTrue ((monadSaturated_iff_generic cellAlpha cellBeta).mp conv)
    | isFalse notConv =>
        isFalse (fun generic => notConv ((monadSaturated_iff_generic cellAlpha cellBeta).mpr generic))

/-! ## The concrete instance at `involution +_M monad`, with a real walker stored as a component -/

/-- The free monad decider over the RECONSTRUCTED `monadComputad.toModeSignature` (empty law relation) — the
component-2 decider of the concrete empty-fragment dispatch.  The monad's `eta`/`mu` 2-generators are present (the
free word problem is nontrivial), only the monad LAWS are excluded (empty relation). -/
def monadComponentFreeDecider :
    DecidableSaturatedConvForRel monadComputad.toModeSignature (emptyCellRel monadComputad.toModeSignature) :=
  decidableSaturatedConvOverReconstructed monadComputad (fun row => row.elim)

/-- ★ **The composable empty-law dispatch at `involution +_M monad`** — a genuine `SaturatedDispatchDecidability`
whose `componentOneDecider` is the REAL walking-involution walker `involutionSaturatedThinDecider` (WP-WALKER-2,
over the reconstructed involution signature — no reseat needed, the involution is thin) and whose
`componentTwoDecider` is the free monad decider.  The combined decider is the free pushout decision.  The base
pushout relation is EXACTLY r7's `crossPairPushoutRel` (the real coprojections, empty component relations), so the
combined decider decides the interleaving pair. -/
def involutionMonadEmptyRowsDispatch :
    SaturatedDispatchDecidability involutionComputad monadComputad involutionMonadSameModes
      (emptyCellRel involutionComputad.toModeSignature)
      (emptyCellRel monadComputad.toModeSignature)
      crossPairPushoutRel :=
  saturatedEmptyRowsPushoutDispatch involutionComputad monadComputad involutionMonadSameModes
    (inclusionLeftTwo involutionComputad monadComputad involutionMonadSameModes rfl)
    (inclusionRightTwoReal involutionComputad monadComputad involutionMonadSameModes)
    (fun row => row.elim) (fun row => row.elim)
    involutionMonadPushout_disjoint
    involutionSaturatedThinDecider
    monadComponentFreeDecider

/-! ## Composability, level 1 — the combined decider inhabits the component-decider interface -/

/-- ★ **Composability, level 0** — the combined decider of the concrete dispatch has EXACTLY the type of a
component-decider input (`DecidableSaturatedConvForRel _ crossPairPushoutRel`), witnessed by a type-preserving
identity.  Together with `saturatedConvOverPushoutRows_empty` (the output relation is provably empty) this is the
n-ary fold enabler: the dispatch output feeds straight back as a component of a further amalgam. -/
def involutionMonadCombinedDeciderIsComposable :
    DecidableSaturatedConvForRel involutionMonadPushout.toModeSignature crossPairPushoutRel :=
  involutionMonadEmptyRowsDispatch.combinedDecider

/-! ## Non-vacuity (P5) — the fragment decider computes isTrue AND isFalse on real pairs -/

/-- The combined decider on the interleaving pair `crossPairAlpha` (`δ₁` whiskered by `s`) vs `crossPairBeta`
(`δ₀` whiskered by `s`), read off as a `Bool`.  Expect `false`: the two `s`-whiskered monad faces fold to DIFFERENT
arity maps (`[0,2]` vs `[0,1]`, r7), so they are NOT free-pushout-convertible; the LIVE combined decider computes
`isFalse`. -/
def crossPairPushoutSeparatingVerdict : Bool :=
  match involutionMonadEmptyRowsDispatch.combinedDecider crossPairAlpha crossPairBeta with
  | isTrue _ => true
  | isFalse _ => false

/-- The combined decider on the reflexive pair `crossPairAlpha` vs `crossPairAlpha`, read off as a `Bool`.  Expect
`true`: a cell is always convertible to itself. -/
def crossPairPushoutReflexiveVerdict : Bool :=
  match involutionMonadEmptyRowsDispatch.combinedDecider crossPairAlpha crossPairAlpha with
  | isTrue _ => true
  | isFalse _ => false

/-- The wrapped REAL walking-monad walker on the associativity foldings `mu ∘ (mu ▷ t)` vs `mu ∘ (t ◁ mu)`, read
off as a `Bool`.  Expect `true`: both fold to the width-3 degeneracy `[0,0,0]`, saturated-convertible through
COMPLETENESS. -/
def monadWalkerAssocVerdict : Bool :=
  match monadWalkerSaturatedDecider monadAssocLeftCell monadAssocRightCell with
  | isTrue _ => true
  | isFalse _ => false

/-- The wrapped REAL walking-monad walker on the two faces `whiskerRight t eta` (`δ₁`) vs `whiskerLeft t eta`
(`δ₀`), read off as a `Bool`.  Expect `false`: distinct monotone maps (`[1]` vs `[0]`), separated by SOUNDNESS. -/
def monadWalkerFacesVerdict : Bool :=
  match monadWalkerSaturatedDecider
      (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT monadUnitTwoCell)
      (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT monadUnitTwoCell) with
  | isTrue _ => true
  | isFalse _ => false

-- The LIVE combined empty-fragment decision separates the interleaving pair: expect `false`.
#eval crossPairPushoutSeparatingVerdict
-- The LIVE combined empty-fragment decision on a reflexive pair: expect `true`.
#eval crossPairPushoutReflexiveVerdict
-- The wrapped real walking-monad walker on the associativity foldings: expect `true`.
#eval monadWalkerAssocVerdict
-- The wrapped real walking-monad walker on the two monad faces: expect `false`.
#eval monadWalkerFacesVerdict

/-! ## §RELFAM — the relation-family ledger (P6)

What a mode-theory / relation-family module must provide to plug into the composable dispatch of this file (the
RELFAM #2213 / MODE-ADMIT #2214 interface contract):

  1. a `ModeComputad` presentation (`comp`), whose reconstructed signature `comp.toModeSignature` carries the free
     `DecidableEq` data automatically (`reconstructedSignature{Mode,Modality,TwoCell}DecEq`);
  2. a `CellRel comp.toModeSignature` law relation (`baseRel`) — the doctrine's generating equations;
  3. EITHER (empty-law fragment, DECIDED HERE) a proof the rows are unfireable
     (`rowsEmpty : baseRel _ _ → False`), which yields a total `DecidableSaturatedConvForRel` via
     `decidableSaturatedConvOverReconstructed`, and — crucially — COMPOSES: the pushout of two such is again
     empty-law (`saturatedConvOverPushoutRows_empty`), so `combinedDecidableSaturatedConvForRel` folds n-ary;
  4. OR (real-law fragment, WALLED) a `DecidableSaturatedConvForRel comp.toModeSignature baseRel` component
     decider — which the pushout combinator can store as `dl`/`dr` at the interface level, but whose CROSSING into
     a computad pushout requires (a) the reconstruction reseat (`DeciderReseat.lean`,
     `fxAmalg_hasReconstructionDecoderReseat = false`, to reseat a bespoke-signature walker onto
     `comp.toModeSignature`) and (b) the Nelson-Oppen / Baader-Tinelli purification completeness for wire-creating
     unit/mult generators (`fxAmalg_hasSaturatedDispatchTheorem = false`).

The empty-law fragment (route 3) is the modular case: the amalgam's word problem IS the free pushout word problem
(Toyama modularity of confluence / the word problem for the disjoint / empty-crossing-law union).  The real-law
fragment (route 4) is the genuine combination wall, and stays open. -/

/-! ## Honesty markers -/

/-- ★ **Honesty marker — the COMPOSABLE empty-law saturated dispatch SHIPS (r9).**  The projection invariant
(`saturatedConvOverEmptyRows_iff_full`: `SaturatedConvOver` over a provably-empty relation reflects EXACTLY to
`TwoCellConvFull`, via `recInto` through the `TwoCellConvFull` target congruence, `ofRelation` = `False.elim` the
sole conservativity boundary), the generic reconstructed-signature decider
(`decidableSaturatedConvOverReconstructed`: free `DecidableEq` data + the FREE-7 decision `decideTwoCellConvFull`
transported through the iff), the composable dispatch (`combinedDecidableSaturatedConvForRel` /
`saturatedEmptyRowsPushoutDispatch`, interface-in/out storing component deciders), the n-ary composability enabler
(`saturatedConvOverPushoutRows_empty`: the pushout relation is provably empty when its components are), a REAL
walker decider wrapped at the generic interface (`monadWalkerSaturatedDecider`, the shipped walking-monad decision
through `monadSaturated_iff_generic`), and the concrete instance at `involution +_M monad`
(`involutionMonadEmptyRowsDispatch`, storing the REAL walking-involution walker as `dl`) with the LIVE combined
decision `#eval`'d isFalse on the interleaving pair (`crossPairPushoutSeparatingVerdict`) and isTrue on a reflexive
pair (`crossPairPushoutReflexiveVerdict`).  This is the FIRST live combined `Decidable` over a mode-theory pushout —
r8's isFalse was conditional-then-unconditional but not a computing decider.  Empty-law fragment ONLY; the general
combination stays walled (`fxAmalg_hasGeneralPushoutDispatch = false`).  Literature: Toyama 1987 (confluence /
word problem modular for the disjoint union); Baader-Tinelli 1998 / Pigozzi 1974 (disjoint-signature word-problem
combination); the empty-crossing-law hypothesis is the 2-categorical analogue of the stably-infinite / no-shared-law
Nelson-Oppen side condition.  `= true`. -/
def fxAmalg_hasComposableFragmentDispatch : Bool := true

end FX1Poly.Polygraph.Amalgam
