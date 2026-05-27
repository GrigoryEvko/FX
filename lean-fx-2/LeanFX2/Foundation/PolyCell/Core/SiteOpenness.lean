/-! # Foundation/PolyCell/Core/SiteOpenness — open/closed spectrum tag

V2-L1.13 (2026-05-27).  Discharges polycell.md §11.7.3 "The
open/closed spectrum -> SiteOpenness as a profile parameter".
Completes the per-profile-metadata triplet alongside V2-L1.11
(TotalityClass) and V2-L1.12 (ConsistencyStrength).

## What this file ships

* `SiteOpenness` -- 4-ctor inductive over the openness tower:
  sealed / extensible / reflective / oracle.
* DecidableEq via deriving.
* `@[reducible] toRank` -- mapping to Nat for decidable comparison
  (sealed=0, extensible=1, reflective=2, oracle=3).
* `@[reducible] le` plus `LE` and `Decidable LE` instances.
* Five witness theorems pinning the ordering chain and one
  antisymmetry case.

## The openness spectrum

Per polycell.md:5762-5775, each level is strictly weaker in
internal guarantees and strictly stronger in expressivity:

* sealed     -- no extensions admitted; strongest internal
                reasoning (fixed Generator table; full quartet
                provable).
* extensible -- extensions via ProfileExtension with admission
                contract (new Generators admitted if STRICT-35/36/37
                pass; quartet holds for Tot fragment of each
                extension).  The fxProfile default.
* reflective -- extensions plus self-reference via Era R ReflTerm
                (kernel can manipulate its own terms as data; Tarski
                hierarchy prevents paradox via partiality of
                ReflTerm.elaborate).
* oracle     -- external oracle calls (SMT, ML model, hardware RNG)
                with explicit trust boundaries (oracle results enter
                as partial Generator entries with explicit
                fallibility).

The ordering `sealed <= extensible <= reflective <= oracle`
captures progression toward greater expressivity (and weaker
guarantees).

## ProfileExtension monotonicity rule

Per the spec at polycell.md:5792-5793:

```
opennessCompatible :
  extension.openness ≤ base.openness
```

An extension's openness MUST NOT EXCEED the base profile's
openness.  Concretely: a sealed base only admits sealed extensions
(by the inequality plus a separate "no extensions" semantics
deferred to phase B); an extensible base admits sealed or
extensible extensions; a reflective base admits up to reflective;
an oracle base admits any openness level.

This is the OPPOSITE direction of the ConsistencyStrength
monotonicity rule (`strengthAfter >= strengthBefore`).  The two
ordering disciplines reflect different concerns:

* Consistency strength: extensions can only INCREASE strength
  (you cannot conservatively extend a strong system with a
  weaker axiom).
* Site openness: extensions can only PRESERVE or NARROW openness
  (you cannot make a sealed base more open via an extension).

## Why list-free this time

V2-L1.11 (TotalityClass) and V2-L1.12 (ConsistencyStrength) used
list-based exclusion when the underlying domain was big (194
generators).  SiteOpenness is parameterised over PROFILES (not
generators), with only 4 inhabitants.  The total `toRank` function
handles all 4 cases directly in a propext-safe match (4 arms, no
wildcard).

The architectural family is preserved: every per-profile-metadata
inductive ships with a Nat rank + decidable LE, same as
ConsistencyStrength.  Lists are an optimization for sparse-domain
defaults; small finite enums use full enumeration.

## Forward-compat: phase B (ProfileExtension integration)

This commit ships the OBSERVATIONAL layer.  Phase B threads the
openness field through ProfileExtension:

```
structure ProfileExtension (base : AdmissibleProfile) where
  openness : SiteOpenness
  opennessCompatible : openness ≤ base.openness
  -- ... existing fields ...
```

Plus a separate well-formedness check enforcing "sealed admits no
extensions" (the inequality alone allows `sealed ≤ sealed`, but
the semantic rule forbids any extension on a sealed base).  The
exact form of this check (special construction-time refusal vs
hypothesis-level constraint) is a phase B design choice.

## FX0-PolyCell discipline

Per polycell.md §11.7.3:

> The `.fx0c` certificate header carries the `SiteOpenness` tag.
> The external verifier checks that the tag is consistent with the
> Generator table (a sealed certificate cannot reference Generators
> not in the original table; an oracle certificate must mark
> oracle-derived cells with a trust boundary tag).

This file's Nat encoding via toRank is the cross-verifier ABI:
the external verifier reads a single Nat from the .fx0c header
and applies the same numeric comparison.

## What's NOT shipped here

* ProfileExtension openness field + opennessCompatible (phase B).
* The "sealed cannot admit any extension" semantic refusal
  (phase B; the inequality alone allows `sealed ≤ sealed`).
* Per-Generator openness requirements (whether a Generator
  REQUIRES a particular openness level to be admissible; phase B).

## Zero-axiom verification

All 9 declarations pass `#assert_no_axioms`.  Audit-gated in
`Tools/AuditAll/AuditPolyCell.lean`.

## Architectural-family summary

After V2-L1.11/12/13:

| File                          | Domain     | Pattern              |
| ----------------------------- | ---------- | -------------------- |
| GeneratorTotalityClass      | 194 gens   | list-based exclusion |
| ConsistencyStrength         | profiles   | Nat rank + LE        |
| SiteOpenness (THIS FILE)    | profiles   | Nat rank + LE        |

The triplet shares the cross-verifier-ABI discipline (Nat tag
serialization) and the `@[reducible]` + `Decidable LE`
construction for `decide`-closable witnesses.
-/

namespace LeanFX2.Foundation.PolyCell.Core

/-- How open a profile is to external content.

Each level is strictly weaker in internal guarantees and strictly
stronger in expressivity.  Four tiers from polycell.md §11.7.3:

* `sealed`     -- no extensions admitted; strongest internal
                  reasoning.
* `extensible` -- extensions via ProfileExtension with admission
                  contract (fxProfile default).
* `reflective` -- extensions plus self-reference via Era R
                  ReflTerm.
* `oracle`     -- external oracle calls with explicit trust
                  boundaries.

The ordering captures progression toward greater expressivity:
`sealed <= extensible <= reflective <= oracle`. -/
inductive SiteOpenness where
  | sealed
  | extensible
  | reflective
  | oracle
  deriving DecidableEq, Repr

namespace SiteOpenness

/-- Numeric rank for decidable comparison.  Smaller rank means
stronger internal guarantees and narrower expressivity. -/
@[reducible] def toRank : SiteOpenness → Nat
  | .sealed     => 0
  | .extensible => 1
  | .reflective => 2
  | .oracle     => 3

/-- Ordering on site openness: `left ≤ right` iff
`left.toRank ≤ right.toRank` (Nat ordering).  Used by the
ProfileExtension opennessCompatible check (V2-L1.13 phase B):
an extension's openness must be ≤ the base's openness. -/
@[reducible] def le (left right : SiteOpenness) : Prop :=
  left.toRank ≤ right.toRank

end SiteOpenness

instance : LE SiteOpenness := ⟨SiteOpenness.le⟩

/-- Decidable `≤` on site openness via `Nat.decLe` on the ranks.
Lets every concrete comparison close by `decide`. -/
instance (left right : SiteOpenness) : Decidable (left ≤ right) :=
  Nat.decLe left.toRank right.toRank

/-! ## Witness theorems (5 pins across the openness tower)

These theorems witness the chain of monotonic comparisons across
the openness tower.  Each closes by `decide`. -/

theorem sealed_le_extensible :
    SiteOpenness.sealed ≤ SiteOpenness.extensible := by decide

theorem extensible_le_reflective :
    SiteOpenness.extensible ≤ SiteOpenness.reflective := by decide

theorem reflective_le_oracle :
    SiteOpenness.reflective ≤ SiteOpenness.oracle := by decide

/-- Antisymmetry witness: extensible is strictly above sealed, so
the reverse comparison fails. -/
theorem not_extensible_le_sealed :
    ¬ (SiteOpenness.extensible ≤ SiteOpenness.sealed) := by decide

/-- Antisymmetry witness on the other end: oracle is strictly
above reflective, so the reverse comparison fails. -/
theorem not_oracle_le_reflective :
    ¬ (SiteOpenness.oracle ≤ SiteOpenness.reflective) := by decide

end LeanFX2.Foundation.PolyCell.Core
