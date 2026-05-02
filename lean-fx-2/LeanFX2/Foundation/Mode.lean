/-! # Mode 2-category — foundational MTT infrastructure.

Modes form a 2-category.  Modalities are 1-cells between modes.
2-cells (TwoCell) compose 1-cells with coherence; subsumption is
the partial order on 2-cells.

This file consolidates lean-fx's `Mode/{Defn, Modality, TwoCell,
Composable, Collision}` into a single foundational module.  Mode
infrastructure is **Layer 0** in lean-fx-2 — every Term value carries
a `Mode` parameter, every Modality decoration on Ty carries a 1-cell,
every modal computation rule appeals to 2-cells.

## Why foundational

In lean-fx, modes were added later in the project history; the kernel
was built mode-naive then retrofitted.  This left `mode : Mode` as
an implicit-binding parameter on most theorems but never load-bearing
on the architecture.  In lean-fx-2, modes are first-class from day 1:
Layer 6 (Modal) doesn't bolt onto a mode-blind kernel — it crystallises
infrastructure that's been present at the foundation.

## What this file will contain

* `Mode` — finite enumeration of modes (or open universe?  TBD)
  reference: BiSikkel's mode theory (`~/Downloads/fx-refs/BiSikkel/`)
* `Modality m₁ m₂` — 1-cell from mode `m₁` to mode `m₂`
* `Modality.id`, `Modality.comp` — identity and composition of 1-cells
* `TwoCell μ ν` — 2-cell between two parallel 1-cells `μ ν : Modality m₁ m₂`
* `TwoCell.id`, `TwoCell.vcomp`, `TwoCell.hcomp` — vertical and horizontal composition
* `Composable` — predicate witnessing two 1-cells compose without collision
* `Collision` — collision lattice for cross-dimension soundness
  (per `fx_design.md` §6.8 — 21 dimensions are not orthogonal)

## Design decisions

* **Modes are finite**: pick a fixed enumeration (e.g., {Software, Hardware, Wire,
  Ghost, Bridge}).  Open mode universe complicates Term's mode index without
  apparent gain.
* **Modalities form a strict 2-category, not bi-2-category**: composition is
  associative on the nose, not up to coherence.  Avoids coherence-cycle proof debt.
* **2-cells form a poset, not a category**: `TwoCell.vcomp` is partial-order
  composition (subsumption transitivity), not category composition.  Simplifies the
  layer.
* **Collision is data, not Prop**: stored as a `Decidable` table of (modality₁, modality₂)
  pairs that are forbidden to compose.  Decidability lets type checker reject collisions
  at elab time.

## Dependencies

Layer 0 of Layer 0 — depends only on Lean core (`Nat`, `Fin`, `Decidable`).

## Downstream

* `Foundation/Ty.lean` — `Ty.modal` constructor takes a `Modality`
* `Foundation/Context.lean` — `Ctx` carries a `Mode`
* `Term.lean` — every `Term` has a `Mode` parameter
* `Modal/Foundation.lean` — Term.modIntro/modElim/subsume use TwoCell
* `Graded/Modal.lean` — modality interaction with grade vector
-/

namespace LeanFX2.Mode

-- TODO: Mode enumeration
-- TODO: Modality 1-cells with id/comp
-- TODO: TwoCell 2-cells with id/vcomp/hcomp
-- TODO: Composable predicate
-- TODO: Collision lattice + Decidable instance

end LeanFX2.Mode
