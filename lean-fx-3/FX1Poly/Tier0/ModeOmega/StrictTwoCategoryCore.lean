import FX1Poly.Tier0.ModeOmega.Interface

/-! # Tier0/ModeOmega — the strict 2-category core + the FXModeTheory round-trip (mode-1)

mode-0 (`Interface.lean`) locked the design.  This module recognizes the shipped `fxModeTheory` as a
genuine STRICT 2-category and records the abstract-interface ↔ concrete-path round-trip.

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
that weak structure is NOT what FX's mode theory is (it is strict).  The dim-2 coherences as a decidable
3-polygraph (mode-3), the structure-class certificate (mode-2), and the adjoint strings (mode-4) remain
RESERVED for the later bricks.

Zero external dependencies; raw Lean 4 + Init only.  Anchors delegate to shipped `fxModeTheory` facts —
no `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, or `omega`.  Per-declaration
gated in `FX1PolyAudit/AuditModeOmega.lean`. -/

namespace FX1Poly.Tier0.ModeOmega

open FX1Poly.MTTNorm

/-! ## The genuine anchors (each via a shipped `fxModeTheory` fact) -/

/-- **The associator is the identity 2-cell.**  Horizontal composition of modality paths is strictly
associative — `(f ∘ g) ∘ h = f ∘ (g ∘ h)` is a definitional equality (the shipped `compose_assoc`), so
the associator coherence is trivial. -/
theorem fxModeHorizontalCompositionStrictlyAssociative
    {modeA modeB modeC modeD : FXModeAtom}
    (pathF : FXModePath modeA modeB)
    (pathG : FXModePath modeB modeC)
    (pathH : FXModePath modeC modeD) :
    (pathF.compose pathG).compose pathH = pathF.compose (pathG.compose pathH) :=
  FXModePath.compose_assoc pathF pathG pathH

/-- **The unitors are identity 2-cells.**  Both the left and right unit laws — `id ∘ f = f` and
`f ∘ id = f` — hold as definitional equalities (the shipped `identity_left` / `identity_right`). -/
theorem fxModeUnitorsAreTrivial
    {modeA modeB : FXModeAtom}
    (pathF : FXModePath modeA modeB) :
    (FXModePath.identity modeA).compose pathF = pathF
      ∧ pathF.compose (FXModePath.identity modeB) = pathF :=
  ⟨FXModePath.identity_left pathF, FXModePath.identity_right pathF⟩

/-- **The abstract ↔ concrete round-trip.**  The abstract `ModeTheory` interface operations on
`fxModeOmega.modeTheory` (= `fxModeTheory`) reduce definitionally to the concrete `FXModePath`
operations: `composeModality = FXModePath.compose` and `identityModality = FXModePath.identity`.  The
interface is faithfully and strictly realized by the concrete presentation. -/
theorem fxModeAbstractConcreteRoundTrip
    {modeA modeB modeC : FXModeAtom}
    (pathF : FXModePath modeA modeB)
    (pathG : FXModePath modeB modeC)
    (mode : FXModeAtom) :
    fxModeOmega.modeTheory.composeModality pathF pathG = pathF.compose pathG
      ∧ fxModeOmega.modeTheory.identityModality mode = FXModePath.identity mode :=
  ⟨rfl, rfl⟩

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

end FX1Poly.Tier0.ModeOmega
