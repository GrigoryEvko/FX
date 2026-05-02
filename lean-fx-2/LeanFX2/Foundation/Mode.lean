/-! # Mode — Layer 0 foundational mode enum.

The 5 FX modes per `fx_design.md` §6.3.  Modal infrastructure
(Modality 1-cells, TwoCell 2-cells, Composable predicate, Collision
lattice) is added in Layer 6 (`Modal/Foundation.lean`) when modal
types come online.  This minimal version provides what's needed for
Ctx to carry a Mode parameter from day 1.

## Design notes

* Mode is a closed enum (not an open universe).  Adding modes requires
  recompilation; this is acceptable and avoids the type-index
  explosion that an open universe would cause on Term.
* DecidableEq derives clean (non-dep enum, propext-free per
  `feedback_lean_zero_axiom_match.md` Rule 2).
* Modality + TwoCell live in `Modal/Foundation.lean` (Layer 6).
  Defining them here would force Term to carry modality data
  prematurely.  The Ctx-level Mode parameter is sufficient for
  Layer 0–5 reasoning.
-/

namespace LeanFX2

/-- The modes FX supports per `fx_design.md` §6.3.

* `software` — default; runtime computation, full effects allowed
* `hardware` — synthesizable to gates; restricted effect set
* `wire` — bit-level wire / serialization mode
* `ghost` — compile-time only; erased at runtime
* `bridge` — parametricity zone (Bridge modality target)
-/
inductive Mode : Type
  | software
  | hardware
  | wire
  | ghost
  | bridge
  deriving DecidableEq, Repr

end LeanFX2
