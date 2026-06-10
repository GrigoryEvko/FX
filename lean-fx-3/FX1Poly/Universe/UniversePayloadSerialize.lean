import FX1Poly.Universe.LevelExprSerialize
import FX1Poly.Universe.UniverseFlagSerialize

/-! # Foundation/PolyCell/Universe/UniversePayloadSerialize
   — prefix-code serializer for the `LevelExpr × UniverseFlag` payload

Composes the `LevelExprSerialize` and `UniverseFlagSerialize` serializers
into the serializer for the `LevelExpr × UniverseFlag` universe payload,
with a round-trip proof.

## Format

The payload `(level, flag)` encodes as the level's prefix code followed by
the flag's tag code: `encodeOnto (level, flag) acc =
level.encodeOnto (flag.encodeOnto acc)`.  Decoding peels the LevelExpr
(consuming a `LevelExpr.decodeOnto`-bounded prefix), then the UniverseFlag
from the residue.

## Fuel

Only the LevelExpr half is recursive, so the decoder takes the LevelExpr's
decoding fuel; `level.nodeCount` suffices.  The UniverseFlag half is
fuel-free.

## Propext discipline

Same recipe as the component serializers: `simp` on the nested-match
decoder leaks `propext`, so the round-trip rewrites a `rfl` combined
reduction lemma (`decodeOnto_encodeOnto_reduce`), discharges the two halves
by `rw` with their round-trips, and collapses the residual match-on-`some`
by `dsimp only []` (pure iota).  Audit-gated zero-axiom in
`FX1PolyAudit/AuditUniverse.lean`.
-/

namespace FX1Poly.Universe

/-- Encode a universe payload `(level, flag)` onto an accumulator: the
LevelExpr prefix code, then the UniverseFlag tag code, then `acc`. -/
def UniversePayload.encodeOnto (payload : LevelExpr × UniverseFlag) (acc : List Nat) : List Nat :=
  payload.1.encodeOnto (payload.2.encodeOnto acc)

/-- Top-level payload encoder: `encodePrefix p = encodeOnto p []`. -/
def UniversePayload.encodePrefix (payload : LevelExpr × UniverseFlag) : List Nat :=
  UniversePayload.encodeOnto payload []

/-- Decode a universe payload at the given LevelExpr fuel: decode the level
expression, then the flag from its residue. -/
def UniversePayload.decodeOnto (fuel : Nat) (input : List Nat) :
    Option ((LevelExpr × UniverseFlag) × List Nat) :=
  match LevelExpr.decodeOnto fuel input with
  | some (level, rest1) =>
    match UniverseFlag.decode rest1 with
    | some (flag, rest2) => some ((level, flag), rest2)
    | none               => none
  | none               => none

/-- Combined definitional reduction: decoding a payload-encoding peels into
the level-decode-then-flag-decode nested match.  `rfl` (both `encodeOnto`
and `decodeOnto` unfold definitionally), so it is the propext-free rewrite
the round-trip uses in place of `simp`. -/
theorem UniversePayload.decodeOnto_encodeOnto_reduce
    (fuel : Nat) (level : LevelExpr) (flag : UniverseFlag) (acc : List Nat) :
    UniversePayload.decodeOnto fuel (UniversePayload.encodeOnto (level, flag) acc) =
      (match LevelExpr.decodeOnto fuel (level.encodeOnto (flag.encodeOnto acc)) with
       | some (decodedLevel, rest1) =>
         match UniverseFlag.decode rest1 with
         | some (decodedFlag, rest2) => some ((decodedLevel, decodedFlag), rest2)
         | none                      => none
       | none                      => none) := rfl

/-- The fuel-parameterized payload round-trip: with fuel covering the
level's node count, decoding the payload-encoding recovers `(level, flag)`
and returns the accumulator unchanged as residue. -/
theorem UniversePayload.decodeOnto_encodeOnto
    (level : LevelExpr) (flag : UniverseFlag) (fuel : Nat) (acc : List Nat)
    (hFuel : level.nodeCount ≤ fuel) :
    UniversePayload.decodeOnto fuel (UniversePayload.encodeOnto (level, flag) acc) =
      some ((level, flag), acc) := by
  rw [UniversePayload.decodeOnto_encodeOnto_reduce,
    LevelExpr.decodeOnto_encodeOnto level fuel (flag.encodeOnto acc) hFuel]
  dsimp only []
  rw [UniverseFlag.decode_encodeOnto flag acc]

/-- Headline payload round-trip: decoding `encodePrefix (level, flag)` at
fuel `level.nodeCount` recovers the payload exactly, with empty residue. -/
theorem UniversePayload.decodeOnto_nodeCount_encodePrefix
    (level : LevelExpr) (flag : UniverseFlag) :
    UniversePayload.decodeOnto level.nodeCount (UniversePayload.encodePrefix (level, flag)) =
      some ((level, flag), []) := by
  dsimp only [UniversePayload.encodePrefix]
  exact UniversePayload.decodeOnto_encodeOnto level flag level.nodeCount [] (Nat.le_refl _)

end FX1Poly.Universe
