import FX1Poly.Core.Fib.ModeLockMultiplier
import FX1Poly.Core.Fib.ModeLockPath

/-! # FX1Poly/Core/Fib/ModeFibration — fib-3 (keystone): the MTT fibration `everything ⊣ mode`, realized

This is the assembly that flips `fxFib_hasModeFibration`: the kernel's dimension-lock modal structure IS the
mode axis's structure, realized over the mode the kernel actually uses — the AFFINE dimension polygraph
(`affineDimensionModeGraph`: one mode, one generator, NO 2-cell relations, the free category on a single
generator).  The four legs:

  * **fib-3a** (`Core/Fib/ModeLockMultiplier`) — the lock `lockCons`'s modality is pinned to the mode-12
    UNPOINTABLE `voidMultiplier` (NOT the mode-2 pointed affine structure class — the wrinkle).
  * **fib-3b** (`Core/Fib/ModeLockPath`) — the bespoke `ObligationModality {fibrant, dimensional}` embeds
    FAITHFULLY (injectively) into the mode-axis `ModalityPath` over the affine graph (`fibrant ↦ identity path`,
    `dimensional ↦ the affine-generator path`).
  * **fib-3c** (`Core/Fib/ModeLockMultiplier`) — the lock's fibrant-INACCESSIBILITY is DERIVED from (computed
    as) the multiplier's non-pointedness: `isAccessibleAtModality .fibrant = decide (IsPointed) = false`.
  * **fib-3d** (`Core/Fib/ModeLockPath`) — the mode 1-cell (modality) equality is DECIDABLE
    (`affineModalityPathDecidableEq`, paths determined by length) — the "mode-dec" side of Gratzer's
    "Conv-dec = mode-dec", specialized to the kernel's mode.

Together these realize the MTT fibration over the kernel's mode theory: the syntactic lock and the semantic
mode structure are the two faces of ONE affine-dimension discipline, with a decidable mode-relative conversion.
The GENERAL multi-mode decidable-2-cell-equality (`fxMode_hasDecidableTwoCellEquality`, arbitrary theories via a
convergent 3-polygraph) stays deferred; the PHYSICAL retirement of the `ObligationModality` enum onto
`ModalityPath` is `A1-RETIRE` (the embedding here makes that a faithful no-op refactor, not a soundness step).

## Zero-axiom

Re-bundles the fib-3a/b/c/d witnesses, all already audited zero-axiom.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Core.Fib

open FX1Poly.Core FX1Poly.Tier0 FX1Poly.Typed

/-- **★ fib-3 keystone: the MTT fibration `everything ⊣ mode` is REALIZED over the kernel's affine mode theory.**
For any dimension-locked context, the three Prop legs hold simultaneously: the lock's multiplier is mode-12
UNPOINTABLE (fib-3a), the lock's fibrant-inaccessibility IS the multiplier's non-pointedness, computed (fib-3c),
and the bespoke `ObligationModality` embeds FAITHFULLY into the mode-axis `ModalityPath` (fib-3b).  The fourth
leg — DECIDABLE mode 1-cell equality (the "mode-dec") — is the instance `affineModalityPathDecidableEq`,
re-exposed as `affineModeFibration_modalityEqualityDecidable`. -/
theorem affineModeFibrationRealized {profile : PolyProfile} {scope : Nat}
    (restContext : TypingContext profile scope) (dimensionType : RawTerm scope)
    (isLtZeroSucc : 0 < scope + 1) :
    affineDimensionLockMultiplier.IsUnpointable
    ∧ ((restContext.lockCons dimensionType).isAccessibleAtModality ⟨0, isLtZeroSucc⟩ .fibrant
        = decide affineDimensionLockMultiplier.IsPointed)
    ∧ (∀ firstModality secondModality : ObligationModality,
        obligationModalityToPath firstModality = obligationModalityToPath secondModality →
        firstModality = secondModality) :=
  ⟨affineDimensionLockMultiplier_isUnpointable,
   lockFibrantAccess_eq_multiplierNonPointedness restContext dimensionType isLtZeroSucc,
   fun _ _ => obligationModalityToPath_injective⟩

/-- **★ fib-3d (the mode-dec leg, exposed at the fibration).**  The kernel's mode 1-cell (modality) equality is
DECIDABLE — Gratzer's "mode-dec", the decidable word problem of the affine mode theory.  Re-export of
`affineModalityPathDecidableEq` so the fibration capstone carries all four legs. -/
def affineModeFibration_modalityEqualityDecidable
    (firstPath secondPath :
        ModalityPath affineDimensionModeGraph affineDimensionMode affineDimensionMode) :
    Decidable (firstPath = secondPath) :=
  affineModalityPathDecidableEq firstPath secondPath

end FX1Poly.Core.Fib
