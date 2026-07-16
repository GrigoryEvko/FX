import FX1Poly.Typed.Fib.ModeLockPath
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.TotalWordProblemDecision
import FX1Poly.Polygraph.TwoCategory.Amalgam.ModeAdmit

/-! # FX1Poly/Typed/Fib/KernelBridgeModeTheory — CORE-WP r1 (K2): the kernel mode theory as a 2-polygraph

The A1 dimension lock (`TypingContext.lockCons`, the single affine modality `mu_affine`) is presented in
`ModeLockPath.lean` as a bare `ModeGraph` (`dimensionUsePositionModeGraph`: ONE mode, ONE generating modality, NO
generating 2-cells).  This file lifts that quiver to a full `ModeSignature` (a 2-polygraph) — the form the
generic mode-decision tools consume — and records the two facts the kernel bridge rests on:

  * **the presentation is RELATION-FREE.**  `dimensionUsePositionModeSignature.twoCell` is the EMPTY family
    (`fun _ _ => Empty`): there are no generating 2-cells and hence no relations among the modalities.  This is
    the free strict 2-category on a single generating endo-1-cell.
  * **the free dimension-2 word problem therefore decides OUTRIGHT.**  Instantiating the un-gated free decider
    `decideTwoCellConvFull` (FREE-7, #1983) at the affine signature's decidable-equality data (both `Unit`, the
    2-cell family `Empty`) gives a total `Decidable (TwoCellConvFull ...)` for the kernel's OWN mode theory — the
    "no relations => the free decision applies directly" branch, made literal.

## The cross-arc attempt (`admitByRowAware`) — a stated NON-MATCH, not a headline

The saturated registry (`Amalgam/ModeAdmit`) admits mode theories that are RENAMINGS of registered walkers WITH
relations (the walking monad / idempotent monad, keyed by their reflected law rows).  The affine kernel theory
is fed to `admitByRowAware` below; it returns `none` — an HONEST non-match.  The affine theory shares its PLAIN
base fingerprint (one mode, one endo-generator) with the walking monad, but its EMPTY law rows separate it: it
carries no relations, so it is not a saturated walker, and the row-aware gate correctly refuses to admit it as
one.  The kernel's mode-2-cell decision therefore rides the FREE decider directly, not the saturated registry.
(A match here would have been a headline; a non-match is the expected and correct outcome for a relation-free
theory, and is stated as such.)

## Zero-axiom

A `ModeSignature` over `Unit`/`Empty`, `inferInstance` decidable-equality data, a `.elim` on the empty 2-cell
family, and `rfl`/observation-level facts over the free decider and the registry.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/`.
-/

set_option autoImplicit false

namespace FX1Poly.Core.Fib

open FX1Poly.Polygraph
open FX1Poly.Polygraph.Amalgam

/-! ## K2a — the affine dimension lock as a 2-polygraph (`ModeSignature`) -/

/-- ★ **The kernel's affine dimension mode theory as a 2-POLYGRAPH.**  The `ModeLockPath` quiver
`dimensionUsePositionModeGraph` (one mode, one generating modality — the affine lock generator) lifted to a
`ModeSignature` with the EMPTY generating-2-cell family (`fun _ _ => Empty`): there are NO relations among the
modalities.  This is the free strict 2-category on a single generating endo-1-cell — the presentation the kernel
bridge's mode-decision tools run over. -/
def dimensionUsePositionModeSignature : ModeSignature where
  graph := dimensionUsePositionModeGraph
  twoCell := fun _ _ => Empty

/-- Decidable equality on the affine signature's modes (there is one, `()`), the `Unit` instance. -/
def affineKernelModeDecEq : DecidableEq dimensionUsePositionModeSignature.graph.Mode :=
  inferInstanceAs (DecidableEq Unit)

/-- Decidable equality on the affine signature's modality generators (there is one, `()`), the `Unit`
instance, uniformly over every endpoint pair. -/
def affineKernelModalityDecEq :
    (sourceMode targetMode : dimensionUsePositionModeSignature.graph.Mode) →
      DecidableEq (dimensionUsePositionModeSignature.graph.Modality sourceMode targetMode) :=
  fun _ _ => inferInstanceAs (DecidableEq Unit)

/-- Decidable equality on the affine signature's generating 2-cells — VACUOUSLY, since the family is `Empty`:
any purported 2-cell is refuted by `Empty.elim`.  The relation-freeness made into decidable data. -/
def affineKernelTwoCellDecEq :
    {sourceMode targetMode : dimensionUsePositionModeSignature.graph.Mode} →
      (sourcePath targetPath : ModalityPath dimensionUsePositionModeSignature.graph sourceMode targetMode) →
      DecidableEq (dimensionUsePositionModeSignature.twoCell sourcePath targetPath) :=
  fun _ _ => fun emptyCell _ => emptyCell.elim

/-! ## K2b — the kernel's OWN dimension-2 word problem decides (free, no relations) -/

/-- The identity 2-cell on the affine identity 1-cell — a genuine cell over the kernel's own signature. -/
def kernelAffineIdentityCell :
    RawTwoCellExpr dimensionUsePositionModeSignature
      (identityPath (graph := dimensionUsePositionModeSignature.graph) dimensionUsePositionMode)
      (identityPath (graph := dimensionUsePositionModeSignature.graph) dimensionUsePositionMode) :=
  RawTwoCellExpr.id (identityPath (graph := dimensionUsePositionModeSignature.graph) dimensionUsePositionMode)

/-- A SYNTACTICALLY DISTINCT parallel cell — the vertical composite of two identities on the same 1-cell.
Parallel to `kernelAffineIdentityCell` (same boundary), a different expression, so the decision is non-vacuous. -/
def kernelAffineVcompIdentityCell :
    RawTwoCellExpr dimensionUsePositionModeSignature
      (identityPath (graph := dimensionUsePositionModeSignature.graph) dimensionUsePositionMode)
      (identityPath (graph := dimensionUsePositionModeSignature.graph) dimensionUsePositionMode) :=
  RawTwoCellExpr.vcomp
    (RawTwoCellExpr.id (identityPath (graph := dimensionUsePositionModeSignature.graph) dimensionUsePositionMode))
    (RawTwoCellExpr.id (identityPath (graph := dimensionUsePositionModeSignature.graph) dimensionUsePositionMode))

/-- ★ **The kernel's OWN mode theory's dimension-2 word problem decides.**  The un-gated free decider
`decideTwoCellConvFull` (FREE-7) at the affine signature's decidable-equality data (`Unit`/`Unit`/`Empty`)
decides convertibility of the two parallel cells `id` vs `id . id`.  `true` = convertible (both are the
identity 2-cell modulo the Godement/whisker congruence).  The dimension-2 FREE decision for the relation-free
affine mode theory, applied directly (no saturated registry). -/
def kernelAffineFreeDimTwoDecision : Bool :=
  match decideTwoCellConvFull affineKernelModeDecEq affineKernelModalityDecEq affineKernelTwoCellDecEq
      kernelAffineIdentityCell kernelAffineVcompIdentityCell with
  | isTrue _ => true
  | isFalse _ => false

/-- ★ The kernel's own dimension-2 free decision COMPUTES to `true` by `rfl` — machine-checked, not merely
observed: the un-gated free decider reduces `id` vs `id . id` over the affine signature to a `isTrue` verdict. -/
theorem kernelAffineFreeDimTwoDecision_holds : kernelAffineFreeDimTwoDecision = true := rfl

/-! ## K2c — the `admitByRowAware` cross-arc: an honest NON-MATCH (relation-free => free decision direct) -/

/-- The hand-reflected row-aware fingerprint of the affine kernel mode theory: ONE mode, ONE endo-generator
`(0, 0)`, NO 2-generators, and — the discriminator — NO reflected law rows (`[]`), because the theory is
relation-free.  Hand-built (the affine theory is a `ModeSignature`, not a `ModeComputad`, so there is no
automatic `toRowAwarePresentationData` extraction — an honest caveat: the fingerprint faithfully mirrors the
one-mode/one-endo/no-relation presentation by hand). -/
def affineKernelRowAware : RowAwarePresentationData where
  base :=
    { modeCount := 1
      modalityGenerators := [(0, 0)]
      twoCellGenerators := [] }
  lawRows := []

/-- ★ **The cross-arc NON-MATCH (stated).**  Feeding the affine kernel fingerprint to the saturated registry's
row-aware gate returns `none`: the affine theory is RELATION-FREE (empty law rows), so it matches neither the
walking monad (three law rows) nor the walking idempotent monad (four) despite sharing their one-mode/one-endo
BASE fingerprint.  The row-aware gate correctly declines to admit a relation-free theory as a saturated walker;
its dimension-2 decision rides the FREE decider (`kernelAffineFreeDimTwoDecision`) directly.  A non-match is the
expected, correct outcome — not a headline. -/
theorem affineKernel_admitByRowAware_isNone :
    admitByRowAware affineKernelRowAware = none := rfl

/-! ## Observability -/

-- The affine kernel's dimension-2 free word problem decides `id` = `id . id` as convertible: expect `true`.
#eval kernelAffineFreeDimTwoDecision
-- The saturated registry's row-aware gate declines the relation-free affine theory: expect `false`.
#eval (admitByRowAware affineKernelRowAware).isSome
-- The affine fingerprint does NOT match the walking-monad row-aware fingerprint (empty vs 3 law rows): `false`.
#eval isRowAwarePresentationMatch affineKernelRowAware monadRowAware
-- ... nor the walking idempotent monad (empty vs 4 law rows): `false`.
#eval isRowAwarePresentationMatch affineKernelRowAware idempotentRowAware

/-! ## Marker -/

/-- ★★ **Honesty marker — the kernel's affine dimension mode theory is PRESENTED and FREE-DECIDES (CORE-WP r1
K2).**  The A1 dimension lock is lifted from a bare `ModeGraph` to a `ModeSignature` (`dimensionUsePositionModeSignature`,
one mode, one generating modality, the EMPTY 2-cell family — relation-free), its decidable-equality data ship
(`Unit`/`Unit`/`Empty`), and its OWN dimension-2 word problem decides through the un-gated free decider
(`kernelAffineFreeDimTwoDecision`, FREE-7 at the affine signature).  The `admitByRowAware` cross-arc is a stated
NON-MATCH (`affineKernel_admitByRowAware_isNone`): the relation-free theory is not a saturated walker, so its
decision rides the free decider directly.  `= true`. -/
def fxKernelBridge_hasAffineModeTheoryPresentation : Bool := true

end FX1Poly.Core.Fib
