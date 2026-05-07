/-! # Mode — Layer 0 foundational mode enum (10 ctors, 2 axes).

`Mode` is a closed enum unifying TWO ORTHOGONAL CONCERNS into a
single Ctx-level parameter (per tracker #1512 reformulation):

| Axis                | Ctors                                      | Semantic role                       |
|---------------------|--------------------------------------------|-------------------------------------|
| **Runtime layer**   | `software`, `hardware`, `wire`             | runtime-target / synthesis class    |
| **Erasure**         | `ghost`                                    | compile-time only, erased at runtime |
| **Parametricity**   | `bridge`                                   | parametricity zone (Bridge modality) |
| **Modal fragment**  | `strict`, `observational`, `univalent`     | MLTT / OEq / Path-bearing tiers     |
| **Cohesive fragm.** | `cohesiveFlat`, `cohesiveSharp`            | discrete + codiscrete subspace tiers |

The first 5 ctors (software/hardware/wire/ghost/bridge) were
added in pre-D1.4 to give Ctx a Mode parameter from day 1; the
last 5 (strict/observational/univalent/cohesiveFlat/cohesiveSharp)
were added in D1.4 (#1297) to support the modal-fragment ladder.
Both groups remain because:

1. The 5 runtime-layer/erasure/parametricity ctors are LOAD-BEARING
   in `Modal/TwoLevel.lean`'s `IsStatic`/`IsDynamic`/`RespectsLayerSeparation`
   predicates (39+ call sites), distinguishing static (compile-time:
   `ghost`) from dynamic (runtime: `software`/`hardware`/`wire`/`bridge`).
2. The 5 modal-fragment ctors are LOAD-BEARING in HoTT/cubical
   (`canHavePath`/`canHaveOEq`/`isStrict` predicates below).

A future v1.x cleanup may split into `Mode × Layer` product type;
for now a closed 10-ctor enum is acceptable and KEEPS the
architectural commitment from CLAUDE.md ("Mode lives at Ctx
level") — splitting Mode into a product would force Term ctors
to thread two indices instead of one.

## fx_design.md cross-reference

§6.3 "21 dimensions" has Mode as one slice; the modal-fragment
half (strict/observational/univalent + cohesives) maps to the
fragment ladder discussed there.  The runtime-layer half maps to
§19 (Systems Programming) execution-context hierarchy.

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

## Tracker

* #1297 D1.4 (completed) — added strict/observational/univalent/
  cohesiveFlat/cohesiveSharp.
* #1512 MODE-LEGACY-CLEANUP (this advisory) — formalizes the
  two-axis nature, replaces "remove vs formalize" question with
  documented orthogonality.  Both axes stay; the closed enum
  unifies them at the Ctx-level commitment.
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
