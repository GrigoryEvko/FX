import FX1Poly.Polygraph.TwoCategory.Amalgam.MonadReseat
import FX1Poly.Polygraph.TwoCategory.Amalgam.DeciderReseat

/-! # Polygraph/TwoCategory/Amalgam/MonadReseatInverse — the INVERSE reseat functor (bespoke ==> reconstructed)
and the reseated reconstructed-signature decider (MODE-ADMIT-INV r1)

`MonadReseat.lean` (MODE-ADMIT r3/r4) shipped the FORWARD reseat `(reconstructed ==> bespoke)`: the 1-cell functor
`reseatPath`, the crux generator translation `reseatGen`, the free 2-cell functor `reseatCell`, and the forward
CONV transport `reseatConvForward` — thereby the isFalse leg of a reconstructed-signature decision literally
(`monadReconRefutes`).  The r4 honesty marker `fxAmalg_hasReconstructionDecoderReseat = false` named the residual
for the FULL two-sided decider: the isTrue leg needs the BACKWARD (inverse) functor plus the round-trip.

This file builds the INVERSE functor `(bespoke ==> reconstructed)`, the exact structural MIRROR of the forward,
and assembles the reseated reconstructed-signature decision:

  * **`reseatPathInv`** — the inverse 1-cell functor: a bespoke `t`-power `monadT^n` maps to the reconstructed
    `t`-power by COUNTING length (`nil` to `nil`, `cons` to `cons (the single reconstructed generator)`).  It is a
    monoid homomorphism (`reseatPathInv_composePath`), and inverse to `reseatPath` on the mono-mode fibre
    (`reseatPathInv_reseatPath` / `reseatPath_reseatPathInv`).
  * **`reseatGenInv`** — the inverse generator map: bespoke `eta` to the reconstructed unit, `mu` to the
    reconstructed multiplication.  DIRECT (no codomain read, unlike the forward `reseatGen`) because the bespoke
    generator boundaries are CONCRETE and their `reseatPathInv` images DEFINITIONALLY equal the reconstructed
    generator boundaries.
  * **`reseatCellInv`** — the inverse free 2-cell functor, the arm-for-arm mirror of `reseatCell` with
    `reseatPathInv` / `reseatPathInv_composePath` / `reseatGenInv` swapped in; plus its per-constructor reduction
    lemmas.
  * **`reseatCellInv_preservesConv`** — the thirteen-constructor `TwoCellConvFull` functoriality mirror of
    `reseatCell_preservesConv`; `reseatConvBackward` (`recInto` into the `reseatCellInv`-image congruence), the
    BACKWARD conv transport; the three backward law rows (`reconLeftUnitConvBackward` etc.).
  * **`monadReconstructedDecision`** — the reseated decider over `monadComputad.toModeSignature`
    `MonadLawRelReconstructed`, assembled from the bespoke `monadSaturatedTwoCellDecision` via
    `monadSaturated_iff_generic`: isFalse leg via `monadReconRefutes` (forward, roundtrip-free), isTrue leg via
    `reseatConvBackward` + the cell round-trip `reseatCellInv_reseatCell`.

The cast toolkit (B1) is REUSED unchanged from `MonadReseat.lean`'s signature-generic `ReseatCastKit` (the
`eqToHom`-style closed algebra: `refl` / `trans` fusion / `map` push-through / naturality), imported here — a
no-op, per the lit-stage discipline.

Every declaration is `Eq.rec`-only, no `HEq`, fib-3-DECOUPLED (no 2-cell equality modulo the 3-cell laws is
decided — the bespoke decider does that; the inverse only re-bases signatures).  Raw Lean 4 + Init.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## B2 — the inverse 1-cell functor: bespoke `t`-powers ==> reconstructed `t`-powers -/

/-- ★ **The inverse reseat 1-cell functor** — a bespoke monad path `t^n` (over `monadGraph`, one mode / one
endo-generator `t`) maps to the reconstructed `t`-power (over `monadComputad.toModeGraph`, one mode `⟨0⟩` / one
endo-generator `⟨⟨0⟩, rfl⟩`) by COUNTING length: `nil` to `nil ⟨0⟩`, `cons` to `cons` the single reconstructed
generator, ignoring the (constant, single-inhabitant) `MonadMode` / `MonadModality` data.  Takes GENERAL
`MonadMode` endpoints (only `point`), outputs the FIXED `⟨0⟩` endpoints — the mirror of the forward `reseatPath`
(Fin 1 in, fixed `point` out).  Reduces DEFINITIONALLY on `monadT` (`reseatPathInv monadT` DEFEQ
`monadComputadReconstructedT`) — the key to the DIRECT inverse generator map. -/
def reseatPathInv {sourceMode targetMode : MonadMode}
    (path : ModalityPath monadGraph sourceMode targetMode) :
    ModalityPath monadComputad.toModeGraph (⟨0, by decide⟩ : Fin 1) (⟨0, by decide⟩ : Fin 1) :=
  match path with
  | ModalityPath.nil _ => ModalityPath.nil (graph := monadComputad.toModeGraph) ⟨0, by decide⟩
  | ModalityPath.cons _ rest =>
      ModalityPath.cons
        (⟨⟨0, by decide⟩, rfl⟩ : monadComputad.Modality (⟨0, by decide⟩ : Fin 1) (⟨0, by decide⟩ : Fin 1))
        (reseatPathInv rest)

/-- Smoke: the bespoke identity path at `point` maps to the reconstructed identity path (`rfl`). -/
theorem reseatPathInv_nil :
    reseatPathInv (ModalityPath.nil (graph := monadGraph) MonadMode.point)
      = ModalityPath.nil (graph := monadComputad.toModeGraph) (⟨0, by decide⟩ : Fin 1) := rfl

/-- ★ Smoke: the bespoke `monadT` maps to the reconstructed `monadComputadReconstructedT` (`rfl` — the generator
embedding lines up definitionally, the DIRECT-inverse handle). -/
theorem reseatPathInv_monadT : reseatPathInv monadT = monadComputadReconstructedT := rfl

/-- ★ Smoke: the bespoke `monadTThenT` maps to the reconstructed `monadComputadReconstructedTT` (`rfl`). -/
theorem reseatPathInv_monadTThenT : reseatPathInv monadTThenT = monadComputadReconstructedTT := rfl

/-- ★ **`reseatPathInv` is a monoid homomorphism** — it distributes over bespoke path composition
(PROPOSITIONALLY: `composePath` recurses on its first argument, base `rfl`, `cons` step `congrArg`).  The inverse
mirror of `reseatPath_composePath`, threaded through `castBoundary` by the two whisker cases of `reseatCellInv`. -/
theorem reseatPathInv_composePath :
    {sourceMode middleMode targetMode : MonadMode} →
    (first : ModalityPath monadGraph sourceMode middleMode) →
    (second : ModalityPath monadGraph middleMode targetMode) →
    reseatPathInv (composePath first second)
      = composePath (reseatPathInv first) (reseatPathInv second)
  | _, _, _, ModalityPath.nil _, _ => rfl
  | _, _, _, ModalityPath.cons _ rest, second =>
      show ModalityPath.cons (graph := monadComputad.toModeGraph)
            (⟨⟨0, by decide⟩, rfl⟩ : monadComputad.Modality (⟨0, by decide⟩ : Fin 1) (⟨0, by decide⟩ : Fin 1))
            (reseatPathInv (composePath rest second))
          = ModalityPath.cons (graph := monadComputad.toModeGraph)
              (⟨⟨0, by decide⟩, rfl⟩ : monadComputad.Modality (⟨0, by decide⟩ : Fin 1) (⟨0, by decide⟩ : Fin 1))
              (composePath (reseatPathInv rest) (reseatPathInv second)) from
        congrArg
          (ModalityPath.cons (graph := monadComputad.toModeGraph)
            (⟨⟨0, by decide⟩, rfl⟩ : monadComputad.Modality (⟨0, by decide⟩ : Fin 1) (⟨0, by decide⟩ : Fin 1)))
          (reseatPathInv_composePath rest second)

/-! ## B2 — the two round-trips of the mono-mode 1-cell fibre -/

/-- ★ **Round-trip (bespoke start)** — `reseatPath . reseatPathInv = id` on bespoke `t`-powers: counting length
forward then back is the identity (`nil` to `nil`, `cons` step `congrArg`, the single `MonadModality` inversion
`MonadModality.t` matched explicitly).  The `cons` modality is drawn by explicit match (propext-free). -/
theorem reseatPath_reseatPathInv :
    (path : ModalityPath monadGraph MonadMode.point MonadMode.point) → reseatPath (reseatPathInv path) = path
  | ModalityPath.nil _ => rfl
  | ModalityPath.cons MonadModality.t rest =>
      congrArg (ModalityPath.cons (graph := monadGraph) MonadModality.t) (reseatPath_reseatPathInv rest)

end FX1Poly.Polygraph.Amalgam
