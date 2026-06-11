import FX1Poly.Core.ConsistencyStrength
import FX1Poly.Universe.UniverseFlag
import FX1Poly.Tier0.AxisObligation
/-! # FX1Poly/Core/StrengthCalibration — ONE strength enum, two calibrations

Reconciles the tree's consistency-strength vocabulary (polycell.md
§11.7.1 drift): the tree carried two strength-flavored enums and one
flag ladder with no stated relationship.

**The canonical strength enum is `FX1Poly.Core.ConsistencyStrength`**
(6 ctors, total `toRank`, decidable `LE` — the `.fx0c` certificate
ABI and the `ProfileExtension` monotonicity carrier).  The other two
types are calibrated INTO it here:

* `FX1Poly.Universe.UniverseFlag` (the 10-ctor Setzer-Rathjen
  admission ladder) gets `ladderRank` (declaration-order position,
  parameter-blind) and `consistencyStrengthBound` (a LOWER-BOUND
  calibration into the canonical enum), with monotonicity proved:
  higher ladder rung never calibrates lower.

* `FX1Poly.Tier0.ConsistencyStrength` (the 5-ctor ledger tag used in
  Tier-0 obligation bookkeeping) gets `rank` and `toCoreStrength`
  (the same lower-bound calibration shape), with monotonicity proved.
  It is NOT an embedding — `leanCore` and `zfc` share the
  `impredicative` lower bound; the Tier-0 enum is a coarser ledger
  vocabulary, not a second source of truth.

## Honesty notes

* The calibrations are LOWER BOUNDS, matching the canonical enum's
  own semantics ("the tag is a lower bound on what the profile can
  prove about weaker systems").  The canonical enum cannot order the
  large-cardinal rungs above `mahlo` against each other — every flag
  from `hyperMahlo` to `vopenka` calibrates to `custom 0` ("above
  mahlo").  Distinguishing them would require either named upper
  tiers on the canonical enum or per-flag large-cardinal admission
  proofs; neither is shipped, and the calibration does not pretend
  otherwise.
* A STRICTLY monotone total calibration of the full ladder is
  impossible into any Nat-ranked enum: the `nMahlo n` and
  `indescribable n` rungs are unbounded families that later
  parameter-free rungs must dominate.  The lower-bound reading
  sidesteps this honestly (families collapse to their floor).
* polycell.md §11.7.1's 11-ctor sketch (setzerHierarchy /
  reflectingHierarchy / ... / reinhardtOpen) remains TARGET: those
  named upper tiers live in the `custom`-tag space until a task
  lands them as ctors with real admission content.

Zero-axiom; audit-gated in `FX1PolyAudit/AuditProfile.lean`.
-/

namespace FX1Poly.Universe

open FX1Poly.Core

/-- Ladder position of a universe flag: the declaration-order rung,
parameter-blind (`nMahlo n` occupies one rung for every `n`, as does
`indescribable n`).  This is the order polycell.md §11.8 declares
("consistency strength increases monotonically along the ctor
declaration order"), made computable. -/
@[reducible] def UniverseFlag.ladderRank : UniverseFlag → Nat
  | .standard        => 0
  | .inaccessible    => 1
  | .mahlo           => 2
  | .superMahlo      => 3
  | .nMahlo _        => 4
  | .hyperMahlo      => 5
  | .weaklyCompact   => 6
  | .indescribable _ => 7
  | .reflecting      => 8
  | .vopenka         => 9

/-- The flag → strength calibration: each universe flag's LOWER BOUND
in the canonical `ConsistencyStrength` enum.

* `standard` (Mahlo-free MLTT) bounds below by `predicative`.
* `inaccessible` / `mahlo` map to their named tiers.
* `superMahlo` and the `nMahlo` family are `≥ mahlo` — the canonical
  enum has no finer named tier, so `mahlo` is the honest floor.
* Everything from `hyperMahlo` up calibrates to `custom 0`
  ("above mahlo"); the canonical enum cannot separate these rungs. -/
@[reducible] def UniverseFlag.consistencyStrengthBound :
    UniverseFlag → ConsistencyStrength
  | .standard        => .predicative
  | .inaccessible    => .inaccessible
  | .mahlo           => .mahlo
  | .superMahlo      => .mahlo
  | .nMahlo _        => .mahlo
  | .hyperMahlo      => .custom 0
  | .weaklyCompact   => .custom 0
  | .indescribable _ => .custom 0
  | .reflecting      => .custom 0
  | .vopenka         => .custom 0

/-- The calibration is monotone along the ladder: a flag higher on
the Setzer-Rathjen ladder never calibrates to a LOWER canonical
strength.  This is the coherence fact tying the flag ladder to the
canonical strength order. -/
theorem UniverseFlag.consistencyStrengthBound_monotone
    (flagA flagB : UniverseFlag)
    (rankLe : flagA.ladderRank ≤ flagB.ladderRank) :
    flagA.consistencyStrengthBound ≤ flagB.consistencyStrengthBound := by
  cases flagA <;> cases flagB <;>
    (try dsimp only [UniverseFlag.ladderRank,
        UniverseFlag.consistencyStrengthBound] at rankLe ⊢) <;>
    first
      | decide
      | exact absurd rankLe (by decide)

/-- Spot-pins of the calibration at the three named-tier rungs. -/
theorem UniverseFlag.standard_calibratesTo_predicative :
    UniverseFlag.standard.consistencyStrengthBound =
      ConsistencyStrength.predicative := rfl

theorem UniverseFlag.mahlo_calibratesTo_mahlo :
    UniverseFlag.mahlo.consistencyStrengthBound =
      ConsistencyStrength.mahlo := rfl

theorem UniverseFlag.vopenka_calibratesTo_customZero :
    UniverseFlag.vopenka.consistencyStrengthBound =
      ConsistencyStrength.custom 0 := rfl

end FX1Poly.Universe

namespace FX1Poly.Tier0

/-- Declaration-order rank of the Tier-0 ledger tags. -/
@[reducible] def ConsistencyStrength.rank :
    ConsistencyStrength → Nat
  | .leanCore         => 0
  | .zfc              => 1
  | .zfcInaccessible  => 2
  | .zfcMahlo         => 3
  | .zfcLargeCardinal => 4

/-- Calibration of the Tier-0 ledger tags into the CANONICAL strength
enum (`FX1Poly.Core.ConsistencyStrength`), as lower bounds:

* `leanCore` and `zfc` both bound below by `impredicative` (Lean's
  kernel and ZFC are impredicative; the canonical enum does not
  separate them — this is a calibration, NOT an embedding).
* `zfcInaccessible` / `zfcMahlo` map to their named tiers.
* `zfcLargeCardinal` calibrates to `custom 0` ("above mahlo").

The Tier-0 enum stays as the coarse obligation-ledger vocabulary;
any ORDERED reasoning about strength goes through this map into the
canonical enum's decidable `LE`. -/
@[reducible] def ConsistencyStrength.toCoreStrength :
    ConsistencyStrength → Core.ConsistencyStrength
  | .leanCore         => .impredicative
  | .zfc              => .impredicative
  | .zfcInaccessible  => .inaccessible
  | .zfcMahlo         => .mahlo
  | .zfcLargeCardinal => .custom 0

/-- The Tier-0 → canonical calibration is monotone along the Tier-0
declaration order. -/
theorem ConsistencyStrength.toCoreStrength_monotone
    (tagA tagB : ConsistencyStrength)
    (rankLe : tagA.rank ≤ tagB.rank) :
    tagA.toCoreStrength ≤ tagB.toCoreStrength := by
  cases tagA <;> cases tagB <;>
    first
      | decide
      | exact absurd rankLe (by decide)

/-- The calibration is deliberately NOT injective: `leanCore` and
`zfc` share the `impredicative` floor.  Pinned so nobody later
mistakes the calibration for an order-embedding. -/
theorem ConsistencyStrength.toCoreStrength_not_injective :
    ConsistencyStrength.leanCore.toCoreStrength =
      ConsistencyStrength.zfc.toCoreStrength := rfl

end FX1Poly.Tier0
