import LeanFX2.Term
import LeanFX2.FX1.Core.HasType

/-! # FX1Bridge/Universe

Root status: Bridge.

Same-level universe-code bridge fragment.  Unlike the staged Bool/Nat
fragments, this maps rich universe codes to native FX1 sorts:

* rich `RawTerm.universeCode level.toNat` encodes as `FX1.Expr.sort level`
* rich `Ty.universe level` encodes as the successor FX1 sort

This file intentionally handles only the same-level case.  Rich cumulativity
allows an inner universe code to inhabit a higher outer universe, but FX1/Core
does not yet have universe-level cumulativity in `DefEq`, so the bridge does
not claim that cross-level fragment.
-/

namespace LeanFX2
namespace FX1Bridge

/-- Encode finite rich universe levels into the matching FX1 level syntax. -/
def encodeUniverseLevel : UniverseLevel -> FX1.Level
  | UniverseLevel.zero => FX1.Level.zero
  | UniverseLevel.succ lowerLevel =>
      FX1.Level.succ (encodeUniverseLevel lowerLevel)
  | UniverseLevel.max leftLevel rightLevel =>
      FX1.Level.max
        (encodeUniverseLevel leftLevel)
        (encodeUniverseLevel rightLevel)
  | UniverseLevel.imax leftLevel rightLevel =>
      FX1.Level.imax
        (encodeUniverseLevel leftLevel)
        (encodeUniverseLevel rightLevel)

/-- Rich raw universe code at the same inner and outer universe level. -/
def universeCodeSameLevelRaw (universeLevel : UniverseLevel) : RawTerm 0 :=
  RawTerm.universeCode universeLevel.toNat

/-- FX1 encoding of a rich same-level universe code term. -/
def encodeRawTerm_universeCodeSameLevel
    (universeLevel : UniverseLevel) : FX1.Expr :=
  FX1.Expr.sort (encodeUniverseLevel universeLevel)

/-- FX1 encoding of the rich universe type inhabited by a same-level universe
code. -/
def encodeTy_universeSameLevel
    (universeLevel : UniverseLevel) : FX1.Expr :=
  FX1.Expr.sort (FX1.Level.succ (encodeUniverseLevel universeLevel))

/-- Same-level universe-code encoding computes to the native FX1 sort. -/
theorem encodeRawTerm_universeCodeSameLevel_eq_sort
    (universeLevel : UniverseLevel) :
    Eq
      (encodeRawTerm_universeCodeSameLevel universeLevel)
      (FX1.Expr.sort (encodeUniverseLevel universeLevel)) :=
  Eq.refl (FX1.Expr.sort (encodeUniverseLevel universeLevel))

/-- Same-level universe-type encoding computes to the successor FX1 sort. -/
theorem encodeTy_universeSameLevel_eq_successor_sort
    (universeLevel : UniverseLevel) :
    Eq
      (encodeTy_universeSameLevel universeLevel)
      (FX1.Expr.sort
        (FX1.Level.succ (encodeUniverseLevel universeLevel))) :=
  Eq.refl
    (FX1.Expr.sort
      (FX1.Level.succ (encodeUniverseLevel universeLevel)))

/-- Canonical rich term for a universe code inhabiting its own universe level.

The ambient rich level is still explicit because `Ty.universe` is cumulative at
the rich layer: a code for universe `level` may be placed in any ambient level
that is at least its successor. -/
def universeCodeSameLevelTerm
    {mode : Mode}
    {ambientLevel : Nat}
    (universeLevel : UniverseLevel)
    (levelLe : universeLevel.toNat + 1 <= ambientLevel) :
    Term
      (Ctx.empty mode ambientLevel)
      (Ty.universe universeLevel levelLe)
      (universeCodeSameLevelRaw universeLevel) :=
  Term.universeCode
    universeLevel
    universeLevel
    (Nat.le_refl universeLevel.toNat)
    levelLe

/-- FX1 typing derivation for the encoded same-level universe code. -/
theorem encodedUniverseCodeSameLevel_has_type
    (universeLevel : UniverseLevel) :
    FX1.HasType
      FX1.Environment.empty
      FX1.Context.empty
      (encodeRawTerm_universeCodeSameLevel universeLevel)
      (encodeTy_universeSameLevel universeLevel) :=
  FX1.HasType.sort
    FX1.Context.empty
    (encodeUniverseLevel universeLevel)

/-- Soundness of the same-level universe-code bridge fragment.

The theorem is intentionally exact-fragment: the rich term must be a universe
code whose inner and outer level coincide.  Cross-level rich cumulativity is
left out until FX1/Core exposes a matching universe-cumulativity conversion. -/
theorem encodeTermSound_universeCodeSameLevel
    {mode : Mode}
    {ambientLevel : Nat}
    (universeLevel : UniverseLevel)
    {levelLe : universeLevel.toNat + 1 <= ambientLevel}
    (_codeTerm :
      Term
        (Ctx.empty mode ambientLevel)
        (Ty.universe universeLevel levelLe)
        (universeCodeSameLevelRaw universeLevel)) :
    FX1.HasType
      FX1.Environment.empty
      FX1.Context.empty
      (encodeRawTerm_universeCodeSameLevel universeLevel)
      (encodeTy_universeSameLevel universeLevel) :=
  encodedUniverseCodeSameLevel_has_type universeLevel

end FX1Bridge
end LeanFX2
