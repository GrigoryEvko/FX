import FX1Poly.Universe.UniverseFlag

/-! # Foundation/PolyCell/Universe/UniverseFlagSerialize
   — prefix-code serializer for `UniverseFlag` + round-trip

The `UniverseFlag → List Nat` serializer feeding the FX0 certificate
format (polycell.md §3.16.17 / §12.6.4), with a `decode ∘ encode = id`
round-trip proof.  Companion to `LevelExprSerialize.lean`; together they
are the propext-clean foundation for the universe-payload
(`LevelExpr × UniverseFlag`) serializer.

## Design — flat tag code, no fuel

`UniverseFlag` is a flat closed enum (no recursion), so the serializer is
a direct tag map and the decoder needs NO fuel.  `encodeOnto flag acc`
prepends the flag's prefix code onto `acc`; the two `Nat`-carrying
constructors (`nMahlo`, `indescribable`) emit their level after the tag.

| ctor                 | code                |
| -------------------- | ------------------- |
| `standard`           | `0 :: acc`          |
| `inaccessible`       | `1 :: acc`          |
| `mahlo`              | `2 :: acc`          |
| `superMahlo`         | `3 :: acc`          |
| `nMahlo level`       | `4 :: level :: acc` |
| `hyperMahlo`         | `5 :: acc`          |
| `weaklyCompact`      | `6 :: acc`          |
| `indescribable level`| `7 :: level :: acc` |
| `reflecting`         | `8 :: acc`          |
| `vopenka`            | `9 :: acc`          |

Tags `≥ 10`, the empty list, and a truncated `nMahlo`/`indescribable`
(tag with no level) decode to `none`.

## Propext discipline

`decode`'s match carries partial (`4 :: []`) and `≥ 10` arms, so its
equation lemmas leak `propext` under `simp`/`unfold`.  The round-trip
avoids them entirely: there is no recursion, so `cases flag` (the clean
constant-motive recursor) followed by `rfl` per branch closes everything
by pure kernel reduction — the encoder's tag and the decoder's matching
arm reduce definitionally.  All declarations audit-gated zero-axiom in
`FX1PolyAudit/AuditUniverse.lean`.
-/

namespace FX1Poly.Universe

/-- Prefix encoder in accumulator form: `encodeOnto flag acc` is `flag`'s
tag code (plus its level for the `Nat`-carrying flags) followed by `acc`. -/
def UniverseFlag.encodeOnto : UniverseFlag → List Nat → List Nat
  | .standard,            acc => 0 :: acc
  | .inaccessible,        acc => 1 :: acc
  | .mahlo,               acc => 2 :: acc
  | .superMahlo,          acc => 3 :: acc
  | .nMahlo level,        acc => 4 :: level :: acc
  | .hyperMahlo,          acc => 5 :: acc
  | .weaklyCompact,       acc => 6 :: acc
  | .indescribable level, acc => 7 :: level :: acc
  | .reflecting,          acc => 8 :: acc
  | .vopenka,             acc => 9 :: acc

/-- Top-level prefix encoder: `encodePrefix flag = encodeOnto flag []`. -/
def UniverseFlag.encodePrefix (flag : UniverseFlag) : List Nat :=
  flag.encodeOnto []

/-- Prefix decoder.  Returns the decoded flag paired with the unconsumed
suffix, or `none` on malformed input.  No fuel: `UniverseFlag` is flat. -/
def UniverseFlag.decode : List Nat → Option (UniverseFlag × List Nat)
  | []                  => none
  | 0 :: rest           => some (.standard, rest)
  | 1 :: rest           => some (.inaccessible, rest)
  | 2 :: rest           => some (.mahlo, rest)
  | 3 :: rest           => some (.superMahlo, rest)
  | 4 :: level :: rest  => some (.nMahlo level, rest)
  | 4 :: []             => none
  | 5 :: rest           => some (.hyperMahlo, rest)
  | 6 :: rest           => some (.weaklyCompact, rest)
  | 7 :: level :: rest  => some (.indescribable level, rest)
  | 7 :: []             => none
  | 8 :: rest           => some (.reflecting, rest)
  | 9 :: rest           => some (.vopenka, rest)
  | (_ + 10) :: _       => none

/-- The fuel-free round-trip: decoding `flag`'s accumulator-encoding
recovers `flag` and returns the accumulator unchanged as residue.  One
`cases` (constant-motive recursor) + per-branch `rfl` (definitional). -/
theorem UniverseFlag.decode_encodeOnto (flag : UniverseFlag) (acc : List Nat) :
    UniverseFlag.decode (flag.encodeOnto acc) = some (flag, acc) := by
  cases flag <;> rfl

/-- Headline serializer round-trip: decoding `encodePrefix flag` recovers
`flag` exactly, with empty residue. -/
theorem UniverseFlag.decode_encodePrefix (flag : UniverseFlag) :
    UniverseFlag.decode (flag.encodePrefix) = some (flag, []) := by
  dsimp only [UniverseFlag.encodePrefix]
  exact UniverseFlag.decode_encodeOnto flag []

end FX1Poly.Universe
