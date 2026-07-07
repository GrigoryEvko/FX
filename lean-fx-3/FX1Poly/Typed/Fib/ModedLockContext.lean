import FX1Poly.Polygraph.Computad.Signature
import FX1Poly.Typed.Fib.ModeLockPath

/-! # FX1Poly/Typed/Fib/ModedLockContext — fib-3 #3: the MODE-INDEXED lock telescope whose `locks(Δ)` composes
real `ModalityPath`s

The kernel's shipped `TypingContext.lockCons` is HARDCODED to the single affine dimension lock: it carries no
modality field, its ambient mode is implicit and singular, and `locks(Δ)` collapses to the identity (the
`DimensionLockAccessibility` header derives this — FX's `lockCons` is MTT's CX/EXTEND modal variable, transparent
to the suffix-lock).  That mono-modality presentation is exactly what makes the bespoke `ObligationModality`
2-element enum sufficient (retired onto the two staged affine 1-cells in `ModeLockPath`).

This file GENERALIZES the lock telescope to the full mode axis, ADDITIVELY (it does NOT touch the kernel's
`TypingContext`, which is the index of `HasTypeDesc` — a field/parameter change there cascades through the entire
WfContext / SubjectReduction stack).  `ModedContext` is a standalone telescope INDEXED BY ITS AMBIENT MODE (the
MTT `Γ @ m`) where:

  * a context is AT A MODE (the `atMode` / ambient-mode index) — the MTT `Γ @ m`;
  * `cons` is CX/EXTEND: it keeps the ambient mode (a modal variable annotation, transparent to the suffix-lock);
  * `lockCons` is CX/LOCK: it carries a genuine `mu : ModalityPath` and SHIFTS the ambient mode along it (MTT's
    `Γ.{μ} @ n` for `μ : n → m`);
  * `locksOf` accumulates the suffix locks by COMPOSING REAL `ModalityPath`s (`composePath`) — not the collapse to
    identity the affine fragment enjoys — landing at the context's `baseMode` (the outermost mode, computed by
    `baseModeOf`).

The AFFINE SEAL (`affineSingleLockContext_locks`, `affineExtendContext_locks`) instantiates this general telescope
over the one-mode / one-generator affine graph of `ModeLockPath` and shows `locksOf` reproduces the shipped
`obligationModalityToPath` values — so the generalization SPECIALIZES back to the retired affine A1-lock exactly:
a single lock ↦ `dimensional`'s 1-cell, an all-extend context ↦ `fibrant`'s identity 1-cell.

HONESTY: this ships the mode-INDEXED lock STRUCTURE and its dimension-1 lock composition (`composePath` of real
`ModalityPath`s).  It does NOT touch — and does not need — Gratzer's dimension-2 keystone (decidable 2-cell
equality = Conv-decidability, `fxMode_hasDecidableTwoCellEquality` / `fxMode_hasModeRelativeConvDecision`), which
stays walled.

## Zero-axiom

A SINGLE-index (ambient-mode) inductive over the parameter `ModeGraph`'s `Mode`, a structural `baseModeOf` /
`locksOf` recursion (the well-scoped single-index pattern that iota-reduces, so the unfolders are `rfl`), and the
`composePath` category laws (`composePath_assoc`) already proven in `Signature`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Audit-gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Core.Fib

open FX1Poly.Polygraph

/-- ★ **The mode-indexed lock telescope.**  `ModedContext graph Binding ambientMode` is a context whose current
(ambient) mode is `ambientMode` — the MTT `Γ @ ambientMode`.  `empty` starts at a mode.  `cons` is CX/EXTEND: it
appends a binding at the ambient mode and keeps the ambient mode fixed.  `lockCons` is CX/LOCK: it appends a
genuine modality path `mu : newAmbient → ambient` and SHIFTS the ambient mode from `ambient` to `newAmbient`.
Additive generalization of the kernel's mono-modality `TypingContext.lockCons`.  Indexed by ONLY the ambient mode
(the well-scoped single-index pattern); the outermost `baseMode` is computed by `baseModeOf`. -/
inductive ModedContext (graph : ModeGraph) (Binding : graph.Mode → Type) : graph.Mode → Type where
  /-- The empty context at a mode. -/
  | empty : (mode : graph.Mode) → ModedContext graph Binding mode
  /-- CX/EXTEND: append a binding at the ambient mode; the ambient mode is UNCHANGED (the extend is transparent
  to the suffix-lock, `locks(Γ, x :^μ A) = locks(Γ)`). -/
  | cons {ambientMode : graph.Mode}
      (restContext : ModedContext graph Binding ambientMode)
      (binding : Binding ambientMode) : ModedContext graph Binding ambientMode
  /-- CX/LOCK: append a lock carrying a genuine modality path `lockModality : newAmbientMode → ambientMode`,
  SHIFTING the ambient mode to `newAmbientMode` (MTT's `Γ.{μ} @ newAmbientMode`). -/
  | lockCons {ambientMode newAmbientMode : graph.Mode}
      (restContext : ModedContext graph Binding ambientMode)
      (lockModality : ModalityPath graph newAmbientMode ambientMode) :
      ModedContext graph Binding newAmbientMode

namespace ModedContext

/-- The **ambient mode** of a context — the MTT `@ m` index (the mode the context currently sits at).  Names the
`atMode` index the kernel's mono-mode `TypingContext` lacks entirely. -/
def atMode {graph : ModeGraph} {Binding : graph.Mode → Type} {ambientMode : graph.Mode}
    (_context : ModedContext graph Binding ambientMode) : graph.Mode :=
  ambientMode

/-- The **base mode** of a context — the outermost mode (where `empty` sits), the target of the total
`locks(Δ)`.  Computed by walking to the innermost `empty` (both `cons` and `lockCons` recurse into the prefix). -/
def baseModeOf {graph : ModeGraph} {Binding : graph.Mode → Type} {ambientMode : graph.Mode}
    (context : ModedContext graph Binding ambientMode) : graph.Mode :=
  match context with
  | .empty mode => mode
  | .cons restContext _binding => baseModeOf restContext
  | .lockCons restContext _lockModality => baseModeOf restContext

/-- ★ **`locks(Δ)` — the suffix-lock composition.**  The total lock modality of a context, a `ModalityPath` from
the ambient mode UP to the base mode, accumulated by COMPOSING the real `ModalityPath`s stored on each `lockCons`
(`composePath`).  `empty` contributes the identity 1-cell; `cons` (CX/EXTEND) is transparent; `lockCons`
PREPENDS its stored path.  The genuine mode-axis `locks(Δ)`, not the affine collapse-to-identity. -/
def locksOf {graph : ModeGraph} {Binding : graph.Mode → Type} {ambientMode : graph.Mode}
    (context : ModedContext graph Binding ambientMode) :
    ModalityPath graph ambientMode (baseModeOf context) :=
  match context with
  | .empty mode => identityPath mode
  | .cons restContext _binding => locksOf restContext
  | .lockCons restContext lockModality => composePath lockModality (locksOf restContext)

/-- Unfolder: the empty context's `locks` is the identity 1-cell. -/
theorem locksOf_empty {graph : ModeGraph} {Binding : graph.Mode → Type} (mode : graph.Mode) :
    locksOf (Binding := Binding) (.empty mode) = identityPath mode :=
  rfl

/-- ★ **CX/EXTEND transparency.**  A `cons` binding contributes NOTHING to `locks(Δ)`: `locks(Γ, x :^μ A) =
locks(Γ)` (MTT Fig 2).  The mode-axis statement of the affine fragment's "extend is transparent to the
suffix-lock". -/
theorem locksOf_cons {graph : ModeGraph} {Binding : graph.Mode → Type} {ambientMode : graph.Mode}
    (restContext : ModedContext graph Binding ambientMode) (binding : Binding ambientMode) :
    locksOf (.cons restContext binding) = locksOf restContext :=
  rfl

/-- ★ **CX/LOCK composition.**  A `lockCons` PREPENDS its stored modality path to `locks(Δ)`, composing REAL
`ModalityPath`s (`composePath`).  This is the generalization the affine fragment's single hardcoded generator
suppresses. -/
theorem locksOf_lockCons {graph : ModeGraph} {Binding : graph.Mode → Type}
    {ambientMode newAmbientMode : graph.Mode}
    (restContext : ModedContext graph Binding ambientMode)
    (lockModality : ModalityPath graph newAmbientMode ambientMode) :
    locksOf (.lockCons restContext lockModality) = composePath lockModality (locksOf restContext) :=
  rfl

/-- ★ **Two stacked locks compose ASSOCIATIVELY into one real `ModalityPath`.**  Stacking `lockCons`es
accumulates their modality paths as a single `composePath` — `locks` of two locks over `rest` equals the
composite lock `composePath outerLock innerLock` applied to `locks(rest)`.  Direct from `composePath_assoc`
(`Signature`): the mode-axis `locks(Δ)` is a genuine free-category composite of the stored 1-cells, the concrete
witness that `locks(Δ)` COMPOSES real `ModalityPath`s (not the affine identity collapse). -/
theorem locksOf_lockCons_lockCons {graph : ModeGraph} {Binding : graph.Mode → Type}
    {ambientMode midAmbientMode newAmbientMode : graph.Mode}
    (restContext : ModedContext graph Binding ambientMode)
    (innerLock : ModalityPath graph midAmbientMode ambientMode)
    (outerLock : ModalityPath graph newAmbientMode midAmbientMode) :
    locksOf (.lockCons (.lockCons restContext innerLock) outerLock)
      = composePath (composePath outerLock innerLock) (locksOf restContext) := by
  rw [locksOf_lockCons, locksOf_lockCons]
  exact (composePath_assoc outerLock innerLock (locksOf restContext)).symm

/-! ## The AFFINE SEAL — the general telescope specializes to the shipped affine A1-lock

Instantiating `ModedContext` over the one-mode / one-generator affine dimension graph of `ModeLockPath`
reproduces the retired affine `ObligationModality` 1-cells: a single lock's `locks` is `dimensional`'s generator
path; an all-extend context's `locks` is `fibrant`'s identity path.  So the mode-axis generalization of #3
SPECIALIZES back to the retired affine A1-lock (Brick 1) on the nose. -/

/-- The affine one-lock context: an `empty` at the affine mode with a single affine-generator `lockCons` on top.
The mode-axis realization of the bridge dimension's lock zone. -/
def affineSingleLockContext :
    ModedContext affineDimensionModeGraph (fun _ => Unit) affineDimensionMode :=
  .lockCons (.empty affineDimensionMode) (singletonModalityPath affineLockGenerator)

/-- ★ **Affine seal (dimensional).**  Over the affine graph a single lock's `locks(Δ)` is exactly
`dimensional`'s staged 1-cell (`obligationModalityToPath .dimensional`) — the generator path.  The general
`composePath`-based `locksOf` reproduces the shipped affine retirement value. -/
theorem affineSingleLockContext_locks :
    locksOf affineSingleLockContext = obligationModalityToPath .dimensional :=
  rfl

/-- The affine all-extend context: an `empty` at the affine mode with a single `cons` (CX/EXTEND) on top. -/
def affineExtendContext :
    ModedContext affineDimensionModeGraph (fun _ => Unit) affineDimensionMode :=
  .cons (.empty affineDimensionMode) ()

/-- ★ **Affine seal (fibrant).**  Over the affine graph an all-extend context's `locks(Δ)` collapses to
`fibrant`'s staged 1-cell (`obligationModalityToPath .fibrant`) — the identity path.  The CX/EXTEND transparency
reproduces the affine fragment's `locks(Δ) = id`. -/
theorem affineExtendContext_locks :
    locksOf affineExtendContext = obligationModalityToPath .fibrant :=
  rfl

end ModedContext
end FX1Poly.Core.Fib
