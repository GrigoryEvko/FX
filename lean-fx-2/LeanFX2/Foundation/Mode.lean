/-! # Mode — Layer 0 foundational mode enum.

The 5 FX modes per `fx_design.md` §6.3.  Modal infrastructure
(Modality 1-cells, TwoCell 2-cells, Composable predicate, Collision
lattice) is added in Layer 6 (`Modal/Foundation.lean`) when modal
types come online.  This minimal version provides what's needed for
Ctx to carry a Mode parameter from day 1.

## Design notes

* Mode is a closed enum (not an open universe).  Adding modes requires
  recompilation; this is acceptable and avoids the type-index explosion
  that an open universe would cause on Term.
* DecidableEq derives clean (non-dep enum, propext-free per
  `feedback_lean_zero_axiom_match.md` Rule 2).
* Modality + TwoCell live in `Modal/Foundation.lean` (Layer 6).
  Defining them here would force Term to carry modality data
  prematurely.  The Ctx-level Mode parameter is sufficient for
  Layer 0–5 reasoning.
-/

namespace LeanFX2

/-- The modes lean-fx-2 supports.

* `software` — default; runtime computation, full effects allowed
* `hardware` — synthesizable to gates; restricted effect set
* `wire` — bit-level wire / serialization mode
* `ghost` — compile-time only; erased at runtime
* `bridge` — parametricity zone (Bridge modality target)
* `strict` — outer 2LTT / strict identity fragment
* `observational` — HOTT observational equality fragment
* `univalent` — observational fragment plus path/univalence reasoning
* `cohesiveFlat` — cohesive flat-mode placeholder
* `cohesiveSharp` — cohesive sharp-mode placeholder
-/
inductive Mode : Type
  | software
  | hardware
  | wire
  | ghost
  | bridge
  | strict
  | observational
  | univalent
  | cohesiveFlat
  | cohesiveSharp
  deriving DecidableEq, Repr

namespace Mode

/-- Whether this mode admits cubical path constructors directly. -/
def canHavePath : Mode → Bool
  | .software => false
  | .hardware => false
  | .wire => false
  | .ghost => false
  | .bridge => false
  | .strict => false
  | .observational => false
  | .univalent => true
  | .cohesiveFlat => false
  | .cohesiveSharp => false

/-- Whether this mode admits observational equality reductions. -/
def canHaveOEq : Mode → Bool
  | .software => false
  | .hardware => false
  | .wire => false
  | .ghost => false
  | .bridge => false
  | .strict => false
  | .observational => true
  | .univalent => true
  | .cohesiveFlat => false
  | .cohesiveSharp => false

/-- Whether this mode is the strict outer fragment. -/
def isStrict : Mode → Bool
  | .software => false
  | .hardware => false
  | .wire => false
  | .ghost => false
  | .bridge => false
  | .strict => true
  | .observational => false
  | .univalent => false
  | .cohesiveFlat => false
  | .cohesiveSharp => false

end Mode

end LeanFX2
