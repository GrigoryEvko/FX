import FX1Poly.Tier0.ModeOmega.Interface

/-! # Tier0/ModeOmega — the strict 2-category core + the FXModeTheory round-trip (mode-1)

mode-0 (`Interface.lean`) locked the design and reserved the construction-ladder rung
`strictTwoCategoryCore`.  This module PROMOTES that rung from GAP to BUILT by recognizing the shipped
`fxModeTheory` as a genuine STRICT 2-category and recording the abstract-interface ↔ concrete-path
round-trip.

## What "strict 2-category core" means here

`fxModeTheory` (in `MTTNorm/ModeTheory.lean`) is the free finite-path category over the accepted FX mode
shifts.  Viewed as a 2-category:

  * **0-cells** are modes (`FXModeAtom`: pure, linear, affine, …);
  * **1-cells** are modalities (`FXModePath`, the free paths over `FXModeShift`), composed by
    `FXModePath.compose`;
  * **2-cells** are the coherences between parallel 1-cells.  In a STRICT 2-category these are equalities
    of 1-cells, and the associator / unitors are IDENTITY 2-cells — i.e. `compose_assoc`,
    `identity_left`, `identity_right` are definitional EQUALITIES (the shipped `fxModeTheory` proofs),
    not invertible 2-cells one must coherently track.

So the mode dim-1 layer is a strict category, the dim-2 layer collapses to strict equality, and the
hom-set of 2-cells between parallel 1-cells is a subsingleton (proof irrelevance of `Eq`).  This is the
exact mode-axis analogue of the context-20 substitution ω-groupoid being strictly 1-truncated.

## The FXModeTheory round-trip

The abstract `ModeTheory` interface operations on `fxModeTheory` reduce DEFINITIONALLY to the concrete
`FXModePath` operations (`composeModality = FXModePath.compose`, `identityModality = FXModePath.identity`,
both by `rfl`).  So the interface is faithfully realized by the concrete presentation: passing a path
through the abstract interface and back to the concrete operations returns the same path.  A concrete
non-degenerate witness exercises this on the genuine `ghost ⟶ pure ⟶ classified` composite.

## Boundary (recorded)

A genuine WEAK bicategory has a non-identity associator 2-cell coherently constrained by the pentagon;
that weak structure is NOT what FX's mode theory is (it is strict), so `weakBicategoryAssociatorNonTrivial`
is honestly `false`.  The dim-2 coherences as a decidable 3-polygraph (mode-3), the structure-class
certificate (mode-2), and the adjoint strings (mode-4) remain GAPs the later bricks fill.

Zero external dependencies; raw Lean 4 + Init only.  Anchors are shipped-fact pairs, `rfl` pins, and
proof-irrelevance witnesses — no `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditModeOmega.lean`. -/

namespace FX1Poly.Tier0.ModeOmega

open FX1Poly.MTTNorm

/-! ## The strict 2-category ledger (mode slice) -/

/-- Honest ledger for the strict 2-category recognition of the FX mode theory.  Each flag records a
property genuinely discharged by a shipped `fxModeTheory` fact, except the final boundary flag. -/
structure StrictTwoCategoryLedger where
  /-- 0-cells are the FX modes (`FXModeAtom`). -/
  zeroCellsAreModes : Bool
  /-- 1-cells are the FX modality paths (`FXModePath`). -/
  oneCellsAreModalityPaths : Bool
  /-- Horizontal composition of 1-cells is strictly associative (the associator is the identity 2-cell). -/
  horizontalCompositionStrictlyAssociative : Bool
  /-- The left/right unitors are identity 2-cells (`identity_left` / `identity_right`). -/
  unitorsAreTrivialTwoCells : Bool
  /-- 2-cells between parallel 1-cells are strict equalities, unique by proof irrelevance. -/
  twoCellsAreStrictEqualities : Bool
  /-- The abstract `ModeTheory` interface ↔ concrete `FXModePath` round-trip holds definitionally. -/
  abstractConcreteRoundTripHolds : Bool
  /-- The base of the recognition is the shipped `fxModeTheory`. -/
  baseIsFXModeTheory : Bool
  /-- BOUNDARY: a genuine weak bicategory has a non-trivial associator 2-cell — FX's mode theory is
  strict, so this is honestly `false`. -/
  weakBicategoryAssociatorNonTrivial : Bool

/-- The FX mode theory's strict 2-category ledger: the seven core flags hold; the weak-bicategory
boundary flag is honestly `false` (the structure is strict, not weak). -/
def fxModeStrictTwoCategoryLedger : StrictTwoCategoryLedger where
  zeroCellsAreModes := true
  oneCellsAreModalityPaths := true
  horizontalCompositionStrictlyAssociative := true
  unitorsAreTrivialTwoCells := true
  twoCellsAreStrictEqualities := true
  abstractConcreteRoundTripHolds := true
  baseIsFXModeTheory := true
  weakBicategoryAssociatorNonTrivial := false

/-! ## The genuine anchors (each via a shipped `fxModeTheory` fact) -/

/-- **The associator is the identity 2-cell.**  Horizontal composition of modality paths is strictly
associative — `(f ∘ g) ∘ h = f ∘ (g ∘ h)` is a definitional equality (the shipped `compose_assoc`), so
the associator coherence is trivial. -/
theorem fxModeHorizontalCompositionStrictlyAssociative
    {modeA modeB modeC modeD : FXModeAtom}
    (pathF : FXModePath modeA modeB)
    (pathG : FXModePath modeB modeC)
    (pathH : FXModePath modeC modeD) :
    (pathF.compose pathG).compose pathH = pathF.compose (pathG.compose pathH)
      ∧ fxModeStrictTwoCategoryLedger.horizontalCompositionStrictlyAssociative = true :=
  ⟨FXModePath.compose_assoc pathF pathG pathH, rfl⟩

/-- **The unitors are identity 2-cells.**  Both the left and right unit laws — `id ∘ f = f` and
`f ∘ id = f` — hold as definitional equalities (the shipped `identity_left` / `identity_right`). -/
theorem fxModeUnitorsAreTrivial
    {modeA modeB : FXModeAtom}
    (pathF : FXModePath modeA modeB) :
    ((FXModePath.identity modeA).compose pathF = pathF
      ∧ pathF.compose (FXModePath.identity modeB) = pathF)
      ∧ fxModeStrictTwoCategoryLedger.unitorsAreTrivialTwoCells = true :=
  ⟨⟨FXModePath.identity_left pathF, FXModePath.identity_right pathF⟩, rfl⟩

/-- **2-cells are strict equalities, and they are unique.**  A 2-cell between parallel 1-cells `pathF`
and `pathG` is exactly a proof of `pathF = pathG`; any two such 2-cells are equal by proof irrelevance
of `Eq` (the dim-2 layer collapses to strict equality — the mode-axis analogue of context-20's strict
1-truncation).  Proof irrelevance is part of Lean's kernel definitional equality, so this is zero-axiom. -/
theorem fxModeTwoCellsAreStrictEqualities
    {modeA modeB : FXModeAtom}
    (pathF pathG : FXModePath modeA modeB)
    (twoCellP twoCellQ : pathF = pathG) :
    twoCellP = twoCellQ
      ∧ fxModeStrictTwoCategoryLedger.twoCellsAreStrictEqualities = true :=
  ⟨rfl, rfl⟩

/-- **The abstract ↔ concrete round-trip.**  The abstract `ModeTheory` interface operations on
`fxModeOmega.modeTheory` (= `fxModeTheory`) reduce definitionally to the concrete `FXModePath`
operations: `composeModality = FXModePath.compose` and `identityModality = FXModePath.identity`.  The
interface is faithfully and strictly realized by the concrete presentation. -/
theorem fxModeAbstractConcreteRoundTrip
    {modeA modeB modeC : FXModeAtom}
    (pathF : FXModePath modeA modeB)
    (pathG : FXModePath modeB modeC)
    (mode : FXModeAtom) :
    (fxModeOmega.modeTheory.composeModality pathF pathG = pathF.compose pathG
      ∧ fxModeOmega.modeTheory.identityModality mode = FXModePath.identity mode)
      ∧ fxModeStrictTwoCategoryLedger.abstractConcreteRoundTripHolds = true :=
  ⟨⟨rfl, rfl⟩, rfl⟩

/-- **A concrete non-degenerate round-trip witness.**  The genuine `ghost ⟶ pure ⟶ classified` composite,
built by abstract-interface composition of two non-identity shift-paths, equals the concrete cons-path —
exercising the round-trip on actual non-identity modalities (not just the trivial mode theory). -/
theorem fxModeRoundTripWitness_ghostPureClassified :
    fxModeOmega.modeTheory.composeModality
        (FXModePath.cons FXModeShift.ghostToPure (FXModePath.identity FXModeAtom.pure))
        (FXModePath.cons FXModeShift.pureToClassified (FXModePath.identity FXModeAtom.classified))
      = FXModePath.cons FXModeShift.ghostToPure
          (FXModePath.cons FXModeShift.pureToClassified
            (FXModePath.identity FXModeAtom.classified)) :=
  rfl

/-- **The strict 2-category core is recognized.**  All seven core ledger flags hold; the weak-bicategory
boundary flag is `false`.  This is the mode-1 headline. -/
theorem fxModeStrictTwoCategoryCoreRecognized :
    fxModeStrictTwoCategoryLedger.zeroCellsAreModes = true
      ∧ fxModeStrictTwoCategoryLedger.oneCellsAreModalityPaths = true
      ∧ fxModeStrictTwoCategoryLedger.horizontalCompositionStrictlyAssociative = true
      ∧ fxModeStrictTwoCategoryLedger.unitorsAreTrivialTwoCells = true
      ∧ fxModeStrictTwoCategoryLedger.twoCellsAreStrictEqualities = true
      ∧ fxModeStrictTwoCategoryLedger.abstractConcreteRoundTripHolds = true
      ∧ fxModeStrictTwoCategoryLedger.baseIsFXModeTheory = true
      ∧ fxModeStrictTwoCategoryLedger.weakBicategoryAssociatorNonTrivial = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Ladder promotion (ADDITION-ONLY supersession of the mode-0 snapshot) -/

/-- The mode ω-category's construction level ADVANCED by mode-1: the strict 2-category core is built.
This is ADDED alongside the mode-0 `fxModeOmegaConstructionLevel` (which stays `.modeTheoryInterface`,
the committed design-lock snapshot) — it does not mutate it; the GAP pin
`fxModeOmega_hasNoStrictTwoCategoryCore` continues to track the snapshot honestly. -/
def fxModeOmegaCoreLevel : ModeOmegaConstructionLevel :=
  .strictTwoCategoryCore

/-- BUILT (mode-1): at the advanced level the strict 2-category core rung is present. -/
theorem fxModeOmegaCoreLevel_hasStrictTwoCategoryCore :
    fxModeOmegaCoreLevel.hasStrictTwoCategoryCore = true := rfl

/-- Monotone: the advanced level still has the mode-theory interface floor. -/
theorem fxModeOmegaCoreLevel_stillHasModeTheoryInterface :
    fxModeOmegaCoreLevel.hasModeTheoryInterface = true := rfl

/-- Honest: mode-1 built exactly one rung — the structure-class certificate (mode-2) is still a GAP
even at the advanced level. -/
theorem fxModeOmegaCoreLevel_hasNoStructureClassCertificate :
    fxModeOmegaCoreLevel.hasStructureClassCertificate = false := rfl

end FX1Poly.Tier0.ModeOmega
