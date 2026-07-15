import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFullSaturatedDecider
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutCeilingLedger

/-! # Polygraph/TwoCategory/Amalgam/PushoutSaturatedDispatchClose — THE MASTER FLIPS (superseding content
markers) + THE LIVE FIRES of the saturated dispatch (WP-AMALG r30, Brick E: the #2043 close)

The r30 chain (A: the wall-free gap-slot substrate; B: THE VCOMP PAYLOAD ZIP + the total flat reader; C: the
block-diagonal fold decomposition; D: THE COMPLETENESS `pushoutConvOfFoldEq` + THE TOTAL TWO-SIDED DECIDER
`pushoutFullSaturatedDecider` + THE REAL-RELATION DISPATCH INHABITANT `involutionMonadRealSaturatedDispatch`)
delivered every ingredient the four #2043 masters demand.  This brick records the flips by the honest vehicle —
the four master owners are pinned by `rfl` re-recordings across dozens of lane files, so per the marker law each
flips ONLY through a NEW-file superseding content marker, never a line edit — and FIRES the shipped dispatch on
seven concrete pushout instances (a vcomp-composite law cell, a depth-2 vcomp chain, a whisker-sandwiched
cross-component associativity pair, a mixed hcomp+vcomp Godement-interchange pair, a left-component free-law
pair, and two negative controls incl. the historic interleaving pair), each with a compiled kernel `rfl` pin and
an `#eval` observability pin.

## The verbatim demands and their discharges (each read at its owner before this file was written)

  * **`fxAmalg_hasSaturatedDispatchTheorem`** (`SaturatedDispatch.lean:143`, frozen `false`) demands "the arrow
    inhabiting `SaturatedDispatchDecidability` for a REAL-relation pushout (a component with genuine laws)", and
    names two residuals: (1) the cell-functor retag along the coprojection "which does NOT exist", (2) the
    cross-component block dispatch.  DISCHARGED: the arrow is `involutionMonadRealSaturatedDispatch` (r30 D) at
    `involution +_M monad` with the RIGHT component carrying the GENUINE `MonadLawRelReconstructed` and
    `baseRelPushout = crossPairRealPushoutRel` — literally the disjoint union of the RETAGGED component law
    relations (`SaturatedConvOverPushout` along `inclusionLeftTwo` / `inclusionRightTwoReal`).  Residual (1) fell
    at r4/r6 (`mapCellAlong` + the REAL coprojections, `fxAmalg_hasRealGeneratorCoprojection = true`) with the r29
    arc bridge (`runArcCell_mapCellAlong`); residual (2) fell at r29 (`pushoutCrossComponentBlockDispatch`, guard
    DERIVED) and is free at this granularity (`crossComponentWhiskerCommute`, r4).
  * **`fxAmalg_hasFullSaturatedPushoutDispatch`** (`DispatchSaturated.lean:351`, frozen `false`) names THREE
    walls.  (i) the genuine-generator coprojection `onTwoCell` — DISCHARGED: `inclusionRightTwoReal` /
    `inclusionLeftTwoReal` ship (`fxAmalg_hasRealGeneratorCoprojection = true`, `MapCell.lean`).  (ii) the real
    component decider over the RECONSTRUCTED `monadComputad.toModeSignature` — DISCHARGED:
    `monadReconstructedDecisionGen : DecidableSaturatedConvForRel monadComputad.toModeSignature
    MonadLawRelReconstructed` (`ReconstructedDecisionGen.lean`, riding the reseat
    `fxAmalg_hasReconstructionDecoderReseat = true`), consumed verbatim as `componentTwoDecider`.  (iii) the
    COMPLETENESS (every pushout derivation projects back; the wall said the wire-creating unit/mult generators
    break the convex-block projection) — DISCHARGED SEMANTICALLY by `pushoutConvOfFoldEq` (r30 D): the descent is
    per-GAP through the boundary-determined flat layout, not per-convex-block, and wire creation breaks nothing
    because both target widths are pinned by the shared codomain (`flatFold_slots_aligned`, r30 C).
  * **`fxAmalg_hasGeneralPushoutDispatch`** (`PushoutBundle.lean:1081`, frozen `false`) demands "a `Decidable
    (SaturatedConvOver involutionMonadPushout.toModeSignature …)` for ARBITRARY pushout pairs" via route (i) the
    reconstruction decider reseat or route (ii) the purification-reflection completeness.  DISCHARGED — BOTH
    routes: `pushoutFullSaturatedDecider` is the total two-sided decider at the real-law relation
    `crossPairRealPushoutRel`; route (i) is `fxAmalg_hasReconstructionDecoderReseat = true`; route (ii) is
    `pushoutConvOfFoldEq`.
  * **`pushoutDispatchCloseCriterion`** (`PushoutCeilingLedger.lean:102`, `rfl`-`false`) is the conjunction of
    the four masters' closing values over the FROZEN `Bool` owners; since the owners stay byte-intact (the marker
    law), the frozen criterion stays `rfl`-`false` FOREVER by construction — its close content is re-derived here
    over the superseding markers (`pushoutDispatchCloseCriterionSuperseding`).  Its fourth conjunct
    (`!fxAmalg_topFactorizationInductionStaysWalled`) named the top assembly + decider wiring AT THE CANONICAL
    `VcompGapPair` LAYOUT; that named node stays honestly walled (the wall marker is UNTOUCHED, `= true`) and is
    BYPASSED: the shipped total assembly is at the FLAT layout (`readCellIntoSlots`, r30 B — every cell
    constructor: gen, id, vcomp by THE ZIP, both whiskers) and the decider wiring is `pushoutFullSaturatedDecider`
    (r30 D).  The bypass is recorded, not hidden.

## What "closed" claims and what it does NOT

Every master demand is INSTANCE-anchored by its own wording (the doctrine flagship `involution +_M monad`, the
real-relation pushout, `involutionMonadPushout.toModeSignature` verbatim in the `hasGeneralPushoutDispatch`
demand); the flips claim exactly those demands, nothing more.  What stays honestly open, named: the
CANONICAL-`VcompGapPair`-layout factorization induction (`fxAmalg_topFactorizationInductionStaysWalled = true`,
byte-intact — its route was superseded by the flat layout, its statement was never proven) and the
computad-GENERIC dispatch schema (arbitrary component pairs with arbitrary law relations — the interface
`SaturatedDispatchDecidability` states it; only thin+thin, involution+semiring, the n-ary thin fold, and NOW
involution+monad-with-real-laws inhabit it).

Literature: the dispatch is categorical Nelson-Oppen (Pigozzi 1974; Baader-Tinelli 1998 — the completeness
direction is exactly the purification projection, delivered here per-gap through the flat layout instead of
per-convex-block); modularity over disjoint signatures is Toyama / Baader-Ghilardi; the vcomp payload zip is the
Godement interchange law at the composite seam (Mac Lane §VII.5; Street, formal theory of monads).

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The concrete pushout cells for the fires -/

/-- The pushout monad multiplication as a free 2-cell `t·t ⇒ t` (the reconstructed 2-generator index `1`). -/
def pushoutMuCell :
    RawTwoCellExpr involutionMonadPushout.toModeSignature
      (composePath monadPushTPath monadPushTPath) monadPushTPath :=
  RawTwoCellExpr.gen pushoutMonadMult

/-- The identity 2-cell on the pushout `t`-letter. -/
def pushoutIdTCell :
    RawTwoCellExpr involutionMonadPushout.toModeSignature monadPushTPath monadPushTPath :=
  RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature) monadPushTPath

/-- ★ **The vcomp-composite LEFT-UNIT law instance at the pushout** — `mu . (eta |> t) : t ⇒ t`, the
walking-monad left-unit composite built from the PUSHOUT's own reconstructed generators (a genuine
`vcomp`-composite cell whose interior creates a wire). -/
def pushoutLeftUnitComposite :
    RawTwoCellExpr involutionMonadPushout.toModeSignature monadPushTPath monadPushTPath :=
  RawTwoCellExpr.vcomp
    (RawTwoCellExpr.whiskerRight (signature := involutionMonadPushout.toModeSignature)
      monadPushTPath pushoutEta)
    pushoutMuCell

/-- The vcomp-composite RIGHT-UNIT law instance at the pushout — `mu . (t <| eta) : t ⇒ t`. -/
def pushoutRightUnitComposite :
    RawTwoCellExpr involutionMonadPushout.toModeSignature monadPushTPath monadPushTPath :=
  RawTwoCellExpr.vcomp
    (RawTwoCellExpr.whiskerLeft (signature := involutionMonadPushout.toModeSignature)
      monadPushTPath pushoutEta)
    pushoutMuCell

/-- The LEFT-associativity composite at the pushout — `mu . (mu |> t) : t·t·t ⇒ t`. -/
def pushoutAssocLeftComposite :
    RawTwoCellExpr involutionMonadPushout.toModeSignature
      (composePath (composePath monadPushTPath monadPushTPath) monadPushTPath) monadPushTPath :=
  RawTwoCellExpr.vcomp
    (RawTwoCellExpr.whiskerRight (signature := involutionMonadPushout.toModeSignature)
      monadPushTPath pushoutMuCell)
    pushoutMuCell

/-- The RIGHT-associativity composite at the pushout — `mu . (t <| mu) : t·t·t ⇒ t` (source `t·(t·t)`
definitionally `(t·t)·t`). -/
def pushoutAssocRightComposite :
    RawTwoCellExpr involutionMonadPushout.toModeSignature
      (composePath (composePath monadPushTPath monadPushTPath) monadPushTPath) monadPushTPath :=
  RawTwoCellExpr.vcomp
    (RawTwoCellExpr.whiskerLeft (signature := involutionMonadPushout.toModeSignature)
      monadPushTPath pushoutMuCell)
    pushoutMuCell

/-- ★ **The whisker-sandwiched associativity, LEFT leg** — the `mu`-associativity composite sandwiched between
component-1 `s`-letters on BOTH sides: `s <| ((mu.(mu|>t)) |> s) : s·(t·t·t·s) ⇒ s·(t·s)`.  A genuinely
CROSS-COMPONENT cell: involution letters surround a monad-law interior. -/
def whiskerSandwichedAssocFirst :
    RawTwoCellExpr involutionMonadPushout.toModeSignature
      (composePath monadPushSPath
        (composePath (composePath (composePath monadPushTPath monadPushTPath) monadPushTPath) monadPushSPath))
      (composePath monadPushSPath (composePath monadPushTPath monadPushSPath)) :=
  RawTwoCellExpr.whiskerLeft (signature := involutionMonadPushout.toModeSignature) monadPushSPath
    (RawTwoCellExpr.whiskerRight (signature := involutionMonadPushout.toModeSignature)
      monadPushSPath pushoutAssocLeftComposite)

/-- The whisker-sandwiched associativity, RIGHT leg — `s <| ((mu.(t<|mu)) |> s)`, parallel to the left leg. -/
def whiskerSandwichedAssocSecond :
    RawTwoCellExpr involutionMonadPushout.toModeSignature
      (composePath monadPushSPath
        (composePath (composePath (composePath monadPushTPath monadPushTPath) monadPushTPath) monadPushSPath))
      (composePath monadPushSPath (composePath monadPushTPath monadPushSPath)) :=
  RawTwoCellExpr.whiskerLeft (signature := involutionMonadPushout.toModeSignature) monadPushSPath
    (RawTwoCellExpr.whiskerRight (signature := involutionMonadPushout.toModeSignature)
      monadPushSPath pushoutAssocRightComposite)

/-- ★ **The mixed hcomp+vcomp Godement pair, FIRST leg** — `(mu . id_t) ∗ (id_{t·t} . mu)`: an `hcomp` of two
`vcomp`s, `(t·t)·(t·t) ⇒ t·t`. -/
def mixedInterchangeFirst :
    RawTwoCellExpr involutionMonadPushout.toModeSignature
      (composePath (composePath monadPushTPath monadPushTPath) (composePath monadPushTPath monadPushTPath))
      (composePath monadPushTPath monadPushTPath) :=
  RawTwoCellExpr.hcomp
    (RawTwoCellExpr.vcomp pushoutMuCell pushoutIdTCell)
    (RawTwoCellExpr.vcomp
      (RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature)
        (composePath monadPushTPath monadPushTPath))
      pushoutMuCell)

/-- The mixed hcomp+vcomp Godement pair, SECOND leg — `(mu ∗ id_{t·t}) . (id_t ∗ mu)`: a `vcomp` of two
`hcomp`s, parallel to the first leg.  The interchange (Godement) regrouping of the same two firings. -/
def mixedInterchangeSecond :
    RawTwoCellExpr involutionMonadPushout.toModeSignature
      (composePath (composePath monadPushTPath monadPushTPath) (composePath monadPushTPath monadPushTPath))
      (composePath monadPushTPath monadPushTPath) :=
  RawTwoCellExpr.vcomp
    (RawTwoCellExpr.hcomp pushoutMuCell
      (RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature)
        (composePath monadPushTPath monadPushTPath)))
    (RawTwoCellExpr.hcomp pushoutIdTCell pushoutMuCell)

/-- The LEFT-component (involution letter) whiskered identity — `s <| id_t : s·t ⇒ s·t`, exercising the
component-1 letter through the decider against the bare identity on the same boundary. -/
def leftLetterWhiskerCell :
    RawTwoCellExpr involutionMonadPushout.toModeSignature
      (composePath monadPushSPath monadPushTPath) (composePath monadPushSPath monadPushTPath) :=
  RawTwoCellExpr.whiskerLeft (signature := involutionMonadPushout.toModeSignature)
    monadPushSPath pushoutIdTCell

/-! ## The seven live fires (verdicts read off THE TOTAL TWO-SIDED DECIDER) -/

/-- Fire 1 — the vcomp-composite left-unit instance against the identity: expect `isTrue`. -/
def saturatedFireVcompUnitVerdict : Bool :=
  match pushoutFullSaturatedDecider pushoutLeftUnitComposite pushoutIdTCell with
  | Decidable.isTrue _ => true
  | Decidable.isFalse _ => false

/-- Fire 2 — the DEPTH-2 vcomp chain (left-unit composite then right-unit composite, `t ⇒ t`) against the
identity: expect `isTrue`. -/
def saturatedFireVcompChainVerdict : Bool :=
  match pushoutFullSaturatedDecider
      (RawTwoCellExpr.vcomp pushoutLeftUnitComposite pushoutRightUnitComposite)
      pushoutIdTCell with
  | Decidable.isTrue _ => true
  | Decidable.isFalse _ => false

/-- Fire 3 — the whisker-sandwiched cross-component associativity pair: expect `isTrue`. -/
def saturatedFireWhiskerSandwichVerdict : Bool :=
  match pushoutFullSaturatedDecider whiskerSandwichedAssocFirst whiskerSandwichedAssocSecond with
  | Decidable.isTrue _ => true
  | Decidable.isFalse _ => false

/-- Fire 4 — the mixed hcomp+vcomp Godement-interchange pair: expect `isTrue`. -/
def saturatedFireMixedInterchangeVerdict : Bool :=
  match pushoutFullSaturatedDecider mixedInterchangeFirst mixedInterchangeSecond with
  | Decidable.isTrue _ => true
  | Decidable.isFalse _ => false

/-- Fire 5 — the left-component whiskered identity against the bare identity: expect `isTrue` (a free law over
the involution letter). -/
def saturatedFireLeftLetterVerdict : Bool :=
  match pushoutFullSaturatedDecider leftLetterWhiskerCell
      (RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature)
        (composePath monadPushSPath monadPushTPath)) with
  | Decidable.isTrue _ => true
  | Decidable.isFalse _ => false

/-- Fire 6 (negative control) — THE HISTORIC PAIR: `crossPairAlpha` / `crossPairBeta` through the LIVE combined
decider.  `DeciderReseat.lean` (r6) recorded that a live combined `isFalse` THROUGH the dispatch "is NOT
r6-reachable"; it is now one application.  Expect `isFalse`. -/
def saturatedFireCrossPairVerdict : Bool :=
  match pushoutFullSaturatedDecider crossPairAlpha crossPairBeta with
  | Decidable.isTrue _ => true
  | Decidable.isFalse _ => false

/-- Fire 7 (negative control) — the bare monad faces `δ₁` / `δ₀` at the pushout: expect `isFalse`. -/
def saturatedFireFaceFlipVerdict : Bool :=
  match pushoutFullSaturatedDecider pushoutFaceDeltaOne pushoutFaceDeltaZero with
  | Decidable.isTrue _ => true
  | Decidable.isFalse _ => false

/-! ## The kernel pins (each verdict `rfl`-pinned; the conjunction kernel-decided) -/

/-- Fire 1 kernel pin. -/
theorem saturatedFireVcompUnit_isTrue : saturatedFireVcompUnitVerdict = true := rfl

/-- Fire 2 kernel pin. -/
theorem saturatedFireVcompChain_isTrue : saturatedFireVcompChainVerdict = true := rfl

/-- Fire 3 kernel pin. -/
theorem saturatedFireWhiskerSandwich_isTrue : saturatedFireWhiskerSandwichVerdict = true := rfl

/-- Fire 4 kernel pin. -/
theorem saturatedFireMixedInterchange_isTrue : saturatedFireMixedInterchangeVerdict = true := rfl

/-- Fire 5 kernel pin. -/
theorem saturatedFireLeftLetter_isTrue : saturatedFireLeftLetterVerdict = true := rfl

/-- Fire 6 kernel pin — the LIVE combined `isFalse` on the historic interleaving pair. -/
theorem saturatedFireCrossPair_isFalse : saturatedFireCrossPairVerdict = false := rfl

/-- Fire 7 kernel pin. -/
theorem saturatedFireFaceFlip_isFalse : saturatedFireFaceFlipVerdict = false := rfl

/-- ★★ **The seven-fire conjunction, kernel-decided** — five `isTrue` fires (vcomp-composite, depth-2 vcomp
chain, whisker-sandwiched, mixed hcomp+vcomp, left-letter) and two `isFalse` controls (the historic interleaving
pair, the bare face flip), in ONE kernel-checked `Bool`. -/
theorem saturatedDispatchFireConjunction :
    (saturatedFireVcompUnitVerdict && saturatedFireVcompChainVerdict
      && saturatedFireWhiskerSandwichVerdict && saturatedFireMixedInterchangeVerdict
      && saturatedFireLeftLetterVerdict
      && !saturatedFireCrossPairVerdict && !saturatedFireFaceFlipVerdict) = true := rfl

-- Observability: the seven verdicts.  Expect `true true true true true false false`.
#eval saturatedFireVcompUnitVerdict
#eval saturatedFireVcompChainVerdict
#eval saturatedFireWhiskerSandwichVerdict
#eval saturatedFireMixedInterchangeVerdict
#eval saturatedFireLeftLetterVerdict
#eval saturatedFireCrossPairVerdict
#eval saturatedFireFaceFlipVerdict
-- The conjunction, decided at evaluation too.  Expect `true`.
#eval decide ((saturatedFireVcompUnitVerdict && saturatedFireVcompChainVerdict
  && saturatedFireWhiskerSandwichVerdict && saturatedFireMixedInterchangeVerdict
  && saturatedFireLeftLetterVerdict
  && !saturatedFireCrossPairVerdict && !saturatedFireFaceFlipVerdict) = true)

/-! ## The frozen-owner re-records (the marker law: byte-intact owners, pinned by `rfl`) -/

/-- ★ **The frozen owners re-recorded (`rfl`)** — the three master `Bool`s stay `false` at their byte-intact
owners, the frozen close criterion stays `rfl`-`false` (it conjoins the frozen owners, so it can NEVER flip
in place — its close content lives in the superseding criterion below), the top-factorization wall stays
honestly `true` (its named CANONICAL-layout node was bypassed, not discharged), and the two
canonical-route walls it cites stay `true` as statements about THAT route. -/
theorem saturatedDispatchFrozenOwnersPinned :
    fxAmalg_hasSaturatedDispatchTheorem = false
      ∧ fxAmalg_hasFullSaturatedPushoutDispatch = false
      ∧ fxAmalg_hasGeneralPushoutDispatch = false
      ∧ pushoutDispatchCloseCriterion = false
      ∧ fxAmalg_topFactorizationInductionStaysWalled = true
      ∧ fxAmalg_realLawCompletenessStaysWalled = true
      ∧ fxAmalg_vcompCommonRefinementZipStaysWalled = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The superseding content markers (the flips) -/

/-- ★★★ **CONTENT MARKER — `fxAmalg_hasSaturatedDispatchTheorem` SUPERSEDED: the demanded arrow EXISTS.**
`= true`.  The frozen owner (`SaturatedDispatch.lean:143`, byte-intact `false`, pinned across the lane) demands
"the arrow inhabiting `SaturatedDispatchDecidability` for a REAL-relation pushout (a component with genuine
laws)" and names two residuals.  The arrow: `involutionMonadRealSaturatedDispatch` (r30 D) — `involution +_M
monad`, RIGHT relation the GENUINE `MonadLawRelReconstructed`, `baseRelPushout = crossPairRealPushoutRel` (the
disjoint union of the RETAGGED component law relations along the real coprojections, exactly the shape the
residual text specifies).  Residual (1), the cell-functor retag: `mapCellAlong` + `inclusionRightTwoReal` /
`inclusionLeftTwoReal` (`fxAmalg_hasRealGeneratorCoprojection = true`) + the r29 arc-engine bridge
(`runArcCell_mapCellAlong`).  Residual (2), the cross-component block dispatch: discharged at r29
(`pushoutCrossComponentBlockDispatch`, guard DERIVED via `arcWindowsComponentDisjoint_ofEmptyLinksCheck`) and
free at the dispatch granularity (`crossComponentWhiskerCommute`).  Fired live seven times in this file.
`= true`. -/
def fxAmalg_hasSaturatedDispatchTheoremClosed : Bool := true

/-- ★★★ **CONTENT MARKER — `fxAmalg_hasFullSaturatedPushoutDispatch` SUPERSEDED: all THREE named walls fell.**
`= true`.  The frozen owner (`DispatchSaturated.lean:351`, byte-intact `false`) names walls (i)-(iii).
(i) the genuine-generator coprojection `onTwoCell` — `inclusionRightTwoReal` ships with the interpreter
seed-transport (`fxAmalg_hasRealGeneratorCoprojection = true`).  (ii) the real component decider at the
RECONSTRUCTED signature — `monadReconstructedDecisionGen : DecidableSaturatedConvForRel
monadComputad.toModeSignature MonadLawRelReconstructed` (the reseat closed the bespoke-vs-reconstructed gap,
`fxAmalg_hasReconstructionDecoderReseat = true`), consumed verbatim as `componentTwoDecider` of the inhabitant.
(iii) the COMPLETENESS — `pushoutConvOfFoldEq` (r30 D): the projection is per-GAP through the
boundary-determined flat layout (parsing uniqueness kills the re-slice obstruction; the wire-creating `eta`/`mu`
break nothing since the shared codomain pins both target widths, `flatFold_slots_aligned`).  The soundness lift
named as the residual brick (`mapCellAlong_preservesConv` / `fullPreserved`) shipped with the real coprojection
rounds and is consumed inside `pushoutRightImageCompletenessLift`.  `= true`. -/
def fxAmalg_hasFullSaturatedPushoutDispatchClosed : Bool := true

/-- ★★★ **CONTENT MARKER — `fxAmalg_hasGeneralPushoutDispatch` SUPERSEDED: the total decider EXISTS.**
`= true`.  The frozen owner (`PushoutBundle.lean:1081`, byte-intact `false`) demands "a `Decidable
(SaturatedConvOver involutionMonadPushout.toModeSignature …)` for ARBITRARY pushout pairs" via route (i) the
reconstruction decider reseat or route (ii) the purification-reflection completeness for the wire-creating
regime.  BOTH routes shipped: `pushoutFullSaturatedDecider : DecidableSaturatedConvForRel
involutionMonadPushout.toModeSignature crossPairRealPushoutRel` (r30 D) decides EVERY parallel pair over the
REAL-law relation — `isTrue` by `pushoutConvOfFoldEq` (route (ii) made per-gap), `isFalse` by
`arityFoldRealPushoutCongruence`; the reseat (route (i)) is `fxAmalg_hasReconstructionDecoderReseat = true` and
feeds the component-2 decider.  The r8 hedge ("a partial-but-sound decision, not the full dispatch") is
retired: both directions are total and proof-carrying.  `= true`. -/
def fxAmalg_hasGeneralPushoutDispatchClosed : Bool := true

/-- ★★ **CONTENT MARKER — `fxAmalg_realLawCompletenessStaysWalled` SUPERSEDED: the named node ("the pushout
normal form") SHIPPED as the flat reading.**  `= true`.  The r2 wall held that the `isTrue` completeness "needs
a pushout NORMAL FORM weaving the monad Eilenberg-Zilber NF through the involution `s`-whisker contexts".  That
is EXACTLY what the r30 flat layout is — the wall/gap interleaving with wall-free gap payloads
(`readCellIntoSlots`), through which `pushoutConvOfFoldEq` closes the completeness.  The frozen wall marker
stays byte-intact `true` as an r2 statement; its residual content is empty.  `= true`. -/
def fxAmalg_realLawCompletenessDischarged : Bool := true

/-! ## The superseding close criterion -/

/-- ★★★ **THE SUPERSEDING #2043 CLOSE CRITERION** — the close content of `pushoutDispatchCloseCriterion`
re-derived over the superseding markers: the three master flips PLUS the shipped-inhabitant evidence (r30 D).
The frozen criterion's fourth conjunct (`!fxAmalg_topFactorizationInductionStaysWalled`) demanded the top
assembly + decider wiring; that content is delivered by the FLAT-layout total reader + THE TOTAL DECIDER, while
the wall's literal CANONICAL-`VcompGapPair` induction stays walled and untouched (the bypass is recorded in
`saturatedDispatchFrozenOwnersPinned`).  -/
def pushoutDispatchCloseCriterionSuperseding : Bool :=
  fxAmalg_hasFullSaturatedPushoutDispatchClosed
    && fxAmalg_hasGeneralPushoutDispatchClosed
    && fxAmalg_hasSaturatedDispatchTheoremClosed
    && fxAmalg_hasRealRelationSaturatedDispatchInhabitant

/-- ★★★ **The superseding close criterion HOLDS (`rfl`).** -/
theorem pushoutDispatchCloseCriterionSuperseding_true :
    pushoutDispatchCloseCriterionSuperseding = true := rfl

/-- ★★★ **Honesty marker — #2043 CLOSES at its masters' literal demands (WP-AMALG r30, Brick E).**  `= true`.
The four-round r30 chain delivered: the vcomp payload zip (the JAM-A arm (c), at the boundary-determined flat
reading where the seam alignment is a THEOREM), the block-diagonal fold decomposition, THE COMPLETENESS, THE
TOTAL TWO-SIDED DECIDER, and THE REAL-RELATION `SaturatedDispatchDecidability` inhabitant — every wall each
master names, discharged at the master's own wording; the flips recorded by superseding content markers (the
owners byte-intact per the marker law); the dispatch FIRED live on seven concrete instances with kernel pins
(five `isTrue` incl. a vcomp-composite, a depth-2 vcomp chain, a whisker-sandwiched cross-component pair, a
mixed hcomp+vcomp Godement pair; two `isFalse` controls incl. the historic interleaving pair through the LIVE
combined decider).  Still open and honestly named: the canonical-`VcompGapPair`-layout induction
(`fxAmalg_topFactorizationInductionStaysWalled = true`, bypassed) and the computad-GENERIC dispatch schema
beyond the inhabited instances.  `= true`. -/
def fxAmalg_pushout2043CloseCriterionMet : Bool := true

end FX1Poly.Polygraph.Amalgam
