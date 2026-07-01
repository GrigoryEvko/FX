import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.AdjointStrings
import FX1Poly.Tier0.Mode.Mode

/-! # FX1Poly/Core/Fib/ModeAffineAdjunction — A1-MODE-AFFINE: the affine dimension modality μ_affine ⊣ μ_affine†

The A1 lineage's negative bridge `μ_affine◇→A` is fibred over the SINISTER (left) affine dimension modality
`μ_affine`, which has a RIGHT adjoint `μ_affine†`.  This file pins that modality and its adjoint as a genuine
adjunction in the kernel's mode theory, reusing mode-4's adjunction machinery — and names, precisely, the one
deferred piece (the triangle-identity saturation) that is SIMULTANEOUSLY fib-3's dimension-2 keystone.

## The kernel's mode axis already carries this adjunction

`mode-0`'s `fxModeAxis` IS the adjunction seed (`fxModeAxis.signature = adjunctionModeSignature`): two modes
`base`/`tip`, a left modality `base ⟶ tip` and a right modality `tip ⟶ base`, with unit/counit 2-cell
generators between non-trivial parallel paths.  So the affine dimension modality and its right adjoint are NOT
new data — they are the seed's `left` / `right`, and mode-4's `adjunctionSeedAdjunctionData` is their adjunction
DATA (the unit `η : id ⇒ μ_affine ∘ μ_affine†` and counit `ε : μ_affine† ∘ μ_affine ⇒ id`).

  * `affineDimensionModality` (`μ_affine`)        := the left modality `base ⟶ tip`;
  * `affineDimensionModalityDagger` (`μ_affine†`)  := the right modality `tip ⟶ base`;
  * `affineDimensionModalityAdjunction`            := mode-4's `adjunctionSeedAdjunctionData` (unit + counit).

(This also retro-sharpens fib-3: `Core/Fib/ModeLockPath`'s `affineDimensionModeGraph` — one mode, one
generator, NO 2-cells — was a SIMPLIFIED dimension-1 stand-in; the genuine affine mode is THIS adjunction-bearing
seed, whose 2-cell layer is exactly what fib-3's dimension-2 keystone is about.)

## ★★ HONESTY — the one deferred piece, and why it is fib-3's keystone

The adjunction DATA (unit/counit) is realized.  The adjunction LAWS — the two TRIANGLE IDENTITIES (snake
equations) — are NOT satisfied in mode-3's free 3-polygraph: a FREE adjunction does not obey the snake
equations.  Saturating the 3-polygraph with the adjunction 3-cells and re-proving CONVERGENCE is mode-9, marked
`fxMode_hasAdjunctionTriangleSaturation := false`.  That convergent presentation is EXACTLY fib-3's deferred
dimension-2 `hasConvergentTwoCellPresentation`: once it lands, the OmegacE `decidableOfNormalizer` engine decides
`TwoCellConv` for μ_affine's 2-cells (the decidable 2-cell equality), which flips `fxMode_hasDecidableTwoCellEquality`
→ `fxMode_hasModeRelativeConvDecision` → fib-3's genuine Conv-dec=mode-dec keystone.  So A1-MODE-AFFINE ships the
adjunction; its triangle-saturation is the shared remaining node for both the A1 negative bridge and fib-3 dim-2.

## Zero-axiom

Definitions naming the seed's modalities + a re-export of mode-4's `adjunctionSeedAdjunctionData` + `rfl` facts
(the mode-axis identity, the unit/counit generators).  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Core.Fib

open FX1Poly.Tier0

/-- **★ The sinister (left) affine dimension modality `μ_affine`** — the left modality `base ⟶ tip` of the
kernel's mode axis (the adjunction seed).  The modality the A1 negative bridge `μ_affine◇→A` is fibred over. -/
def affineDimensionModality : ModalityPath adjunctionGraph AdjunctionMode.base AdjunctionMode.tip :=
  singletonModalityPath AdjunctionModality.left

/-- **★ The right adjoint `μ_affine†`** — the right modality `tip ⟶ base` of the kernel's mode axis, the
RIGHT-adjoint partner the FitchTT lock `Γ/μ_affine†` (A1-NEG-LOCK) is taken with respect to. -/
def affineDimensionModalityDagger : ModalityPath adjunctionGraph AdjunctionMode.tip AdjunctionMode.base :=
  singletonModalityPath AdjunctionModality.right

/-- **★ A1-MODE-AFFINE: the adjunction `μ_affine ⊣ μ_affine†`** — the unit/counit DATA, reusing mode-4's
canonical non-degenerate `adjunctionSeedAdjunctionData`.  This IS the affine dimension modality's adjunction
(the data; the triangle LAWS are the deferred saturation — see the header / the marker below). -/
def affineDimensionModalityAdjunction :
    FreeAdjunctionData adjunctionModeSignature affineDimensionModality affineDimensionModalityDagger :=
  adjunctionSeedAdjunctionData

/-- The affine dimension modality lives over the kernel's ACTUAL mode axis: `fxModeAxis`'s signature IS the
adjunction seed signature the modality is a 1-cell of.  (So `μ_affine` is the kernel's mode, not a fresh
presentation.) -/
theorem affineDimensionModality_overFxModeAxis :
    fxModeAxis.signature = adjunctionModeSignature := fxModeAxis_signature_isAdjunction

/-- The adjunction's unit IS the seed's unit 2-cell generator `η : id_base ⇒ μ_affine ∘ μ_affine†` — a 2-cell
between genuinely distinct parallel paths (identity vs the length-2 composite), so `μ_affine`'s 2-cell layer is
non-trivial. -/
theorem affineDimensionModalityAdjunction_unit_isSeedUnit :
    affineDimensionModalityAdjunction.unit = adjunctionUnitTwoCell := rfl

/-- The adjunction's counit IS the seed's counit 2-cell generator `ε : μ_affine† ∘ μ_affine ⇒ id_tip`. -/
theorem affineDimensionModalityAdjunction_counit_isSeedCounit :
    affineDimensionModalityAdjunction.counit = adjunctionCounitTwoCell := rfl

/-- **★ HONESTY marker (A1-MODE-AFFINE ↔ fib-3 dim-2).**  The adjunction DATA is realized; the triangle-identity
LAWS are the deferred saturation — `fxMode_hasAdjunctionTriangleSaturation = false`.  That saturation (mode-9's
convergent presentation of the adjunction 3-cells) is the SHARED remaining node: it is both the A1 negative
bridge's modal-law coherence AND fib-3's dimension-2 `hasConvergentTwoCellPresentation` (⟹ decidable 2-cell
equality ⟹ the Conv-dec=mode-dec keystone). -/
theorem affineModalityAdjunction_triangleLawsNeedSaturation :
    fxMode_hasAdjunctionTriangleSaturation = false := rfl

end FX1Poly.Core.Fib
