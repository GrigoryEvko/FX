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

/-! ## fib-3d: the decidable DIMENSION-1 word problem for the kernel's affine mode (1-cell equality)

★★ HONESTY (do NOT conflate the two dimensions).  Gratzer's "Conv-dec = mode-dec" keystone is at DIMENSION 2:
modal-type conversion is decidable iff mode **2-cell** equality is decidable (`fxMode_hasDecidableTwoCellEquality`
/ `fxMode_hasModeRelativeConvDecision`, a convergent 3-polygraph deciding `TwoCellConv` modulo the modality's
adjunction triangle identities — still DEFERRED, even for the affine mode).  What THIS file decides is at
DIMENSION 1: equality of 1-cells (modality PATHS) over the affine graph.  Dimension-1 decidability is NECESSARY
for, but NOT SUFFICIENT for, the keystone — and it is moreover ALREADY available generally as the mode axis's
`decidableOneCellEq` (`TwoCategoryCore`); what is below is the affine-graph instance of that dimension-1 fact,
used by the fib-3 fibration capstone, NOT the dimension-2 mode-dec.

The affine dimension polygraph (`affineDimensionModeGraph`): ONE mode, ONE generator, NO 2-cell relations — the
FREE category on a single generator; its 1-cells (`ModalityPath`s) are determined by length, so the
DIMENSION-1 word problem is `DecidableEq Nat` in disguise.  The dimension-2 word problem (deciding the affine
mode's 2-cells) is the genuine remaining keystone work. -/

/-- Length injectivity for the affine mode's 1-cells, over ARBITRARY (mode-)endpoints — the form whose source
and target are variables, so `induction` on the path is legal.  Both endpoints are `Unit` so they are forced to
`()`, but quantifying keeps them free for the recursor.  The hard direction (`length equal → path equal`): the
cross `nil`/`cons` cases are refuted by their `0`-vs-`n+1` lengths (`Nat`-level, propext-free), and the
`cons`/`cons` case strips one generator (both `()` by `Unit` eta, so generators and middle modes coincide
definitionally) and recurses on the tails. -/
theorem affineModalityPath_length_injective_overEndpoints :
    ∀ {sourceMode targetMode : affineDimensionModeGraph.Mode}
      (firstPath secondPath : ModalityPath affineDimensionModeGraph sourceMode targetMode),
      firstPath.length = secondPath.length → firstPath = secondPath := by
  intro sourceMode targetMode firstPath
  induction firstPath with
  | nil _ =>
      intro secondPath lengthsEqual
      cases secondPath with
      | nil _ => rfl
      | cons _ restSecond =>
          exact Nat.noConfusion (show (0 : Nat) = restSecond.length + 1 from lengthsEqual)
  | cons firstGenerator restFirst inductiveHypothesis =>
      intro secondPath lengthsEqual
      cases secondPath with
      | nil _ =>
          exact Nat.noConfusion (show restFirst.length + 1 = (0 : Nat) from lengthsEqual)
      | cons secondGenerator restSecond =>
          have restsEqual : restFirst = restSecond :=
            inductiveHypothesis restSecond (Nat.succ.inj lengthsEqual)
          cases restsEqual
          rfl

/-- ★ **Length injectivity for the affine mode's 1-cells** (the kernel's mode endpoints).  Two `ModalityPath`s
over the affine dimension graph are equal iff they have the same length — the free-category-on-one-generator
word problem.  Specializes `affineModalityPath_length_injective_overEndpoints` to the kernel's single mode. -/
theorem affineModalityPath_length_injective
    (firstPath secondPath :
        ModalityPath affineDimensionModeGraph affineDimensionMode affineDimensionMode)
    (lengthsEqual : firstPath.length = secondPath.length) : firstPath = secondPath :=
  affineModalityPath_length_injective_overEndpoints firstPath secondPath lengthsEqual

/-- ★ **fib-3d: the kernel's affine mode theory has DECIDABLE DIMENSION-1 (1-cell / modality) equality** — the
decidable dimension-1 word problem.  Decided by comparing path lengths (`Nat.decEq`) and transporting along
`affineModalityPath_length_injective`.  Propext-free: `Nat.decEq` plus the length-injectivity recursion.
HONESTY: this is DIMENSION 1, NOT Gratzer's dimension-2 "mode-dec" (`fxMode_hasDecidableTwoCellEquality`, the
decidable 2-CELL equality), which stays deferred; dimension-1 is also generally available as the mode axis's
`decidableOneCellEq`, and this is the affine-graph instance. -/
instance affineModalityPathDecidableEq :
    DecidableEq (ModalityPath affineDimensionModeGraph affineDimensionMode affineDimensionMode) :=
  fun firstPath secondPath =>
    match Nat.decEq firstPath.length secondPath.length with
    | isTrue lengthsEqual =>
        isTrue (affineModalityPath_length_injective firstPath secondPath lengthsEqual)
    | isFalse lengthsDistinct =>
        isFalse (fun pathsEqual => lengthsDistinct (congrArg ModalityPath.length pathsEqual))

end FX1Poly.Core.Fib
