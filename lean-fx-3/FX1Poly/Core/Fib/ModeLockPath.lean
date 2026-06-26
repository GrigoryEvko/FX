import FX1Poly.Tier0.Mode.Mode
import FX1Poly.Typed.Engine.Classifier.DimensionLockAccessibility

/-! # FX1Poly/Core/Fib/ModeLockPath — fib-3b: the bespoke ObligationModality as a mode-axis ModalityPath

fib-3a/3c presented the affine dimension lock in the mode axis's MULTIPLIER form (mode-12 `voidMultiplier`:
unpointable + split, with the kernel's fibrant-inaccessibility DERIVED from unpointedness).  This file presents
the SAME affine modality in the mode axis's POLYGRAPH form (`ModeGraph` / `ModalityPath`, mode-0) and maps the
kernel's bespoke `ObligationModality {fibrant, dimensional}` onto it — the translation that retires the enum
onto the real free-modality 1-cells (the `fib-3d` retirement consumes it).

The affine dimension modality has a minimal POLYGRAPH presentation: ONE mode (the dimension mode) with ONE
generating modality (the affine lock generator — semantically the mode-12 void multiplier of fib-3a).  The
bespoke `ObligationModality` is then two specific 1-cells over this graph:

  * `fibrant`     ↦ the IDENTITY path (no modality — the unlocked / fibrant access);
  * `dimensional` ↦ the affine generator path (one application of the lock generator — the locked / dimensional
    access).

The translation is INJECTIVE (distinct modalities map to distinct-LENGTH paths: `0` vs `1`), so the bespoke
enum embeds FAITHFULLY into the mode-axis `ModalityPath` over the affine dimension graph — the genuine
retirement target for the bespoke `ObligationModality`.

## Zero-axiom

A `ModeGraph` over `Unit`, two `ModalityPath` constructors, `rfl` lengths, and a `cases` + `decide`-length
injectivity.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration audit-gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Core.Fib

open FX1Poly.Tier0 FX1Poly.Typed

/-- The minimal POLYGRAPH presentation of the affine dimension modality: ONE mode (the dimension mode) with ONE
generating modality (the affine lock generator, semantically the mode-12 void multiplier of fib-3a). -/
def affineDimensionModeGraph : ModeGraph where
  Mode := Unit
  Modality := fun _ _ => Unit

/-- The single dimension mode of the affine graph. -/
def affineDimensionMode : affineDimensionModeGraph.Mode := ()

/-- The affine lock generator — the single 1-cell generator of the dimension mode graph (the polygraph face of
the mode-12 void multiplier). -/
def affineLockGenerator : affineDimensionModeGraph.Modality affineDimensionMode affineDimensionMode := ()

/-- ★ **fib-3b: the bespoke `ObligationModality` as a mode-axis `ModalityPath`.**  `fibrant` is the IDENTITY
1-cell (no modality — unlocked / fibrant access); `dimensional` is the affine generator path (one lock
application — dimensional access).  Embeds the kernel's bespoke 2-element enum into the mode axis's
free-modality 1-cells over the affine dimension graph. -/
def obligationModalityToPath :
    ObligationModality → ModalityPath affineDimensionModeGraph affineDimensionMode affineDimensionMode
  | .fibrant => identityPath affineDimensionMode
  | .dimensional => ModalityPath.cons affineLockGenerator (identityPath affineDimensionMode)

/-- The fibrant access mode maps to the IDENTITY path (length `0`). -/
theorem obligationModalityToPath_fibrant_length :
    (obligationModalityToPath .fibrant).length = 0 := rfl

/-- The dimensional access mode maps to the affine generator path (length `1`). -/
theorem obligationModalityToPath_dimensional_length :
    (obligationModalityToPath .dimensional).length = 1 := rfl

/-- ★ The translation is INJECTIVE: distinct `ObligationModality`s map to distinct `ModalityPath`s, refuted by
their distinct path lengths (`0` vs `1`).  So the bespoke enum embeds FAITHFULLY into the mode-axis
`ModalityPath` — the genuine retirement target. -/
theorem obligationModalityToPath_injective {firstModality secondModality : ObligationModality}
    (pathsEqual : obligationModalityToPath firstModality = obligationModalityToPath secondModality) :
    firstModality = secondModality := by
  cases firstModality <;> cases secondModality <;>
    first
      | rfl
      | exact absurd (congrArg ModalityPath.length pathsEqual) (by decide)

end FX1Poly.Core.Fib
