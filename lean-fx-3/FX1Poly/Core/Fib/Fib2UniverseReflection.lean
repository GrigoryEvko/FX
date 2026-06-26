import FX1Poly.Tier0.Type.TypeAxis
import FX1Poly.Typed.Cell.CellConstructors

/-! # FX1Poly/Core/Fib/Fib2UniverseReflection — fib-2a: the type ↔ term universe-code bridge

The first concrete fib-2 gluing (the `type ↔ term` connection point of the fib-0 design-lock).  The type axis
(`Tier0/Type`) packages the universe as a STANDALONE Tarski structure whose codes are the abstract carrier
`StandaloneTarskiUniverse.Code`; the FX witness pins that carrier to `UniverseCode = { level : LevelExpr,
flag : UniverseFlag }`.  The running kernel represents a universe AS A TERM: `universeCodeCell levelExpr flag =
.mkGen .gen_universeCode (levelExpr, flag) .childNil`, backed by the generator `gen_universeCode` whose payload
is EXACTLY `LevelExpr × UniverseFlag`.  So the type axis's abstract code and the kernel's term-level code carry
IDENTICAL DATA — fib-2 is, at its core, that on-the-nose identification (term IS type: there is one `RawTerm`,
the `.type`/`.term` distinction is only a `CellSort` tag).

This file ships the bridge and the data-level round-trip, both `rfl`-level (no term-head pattern match, hence no
propext risk), plus the SUCCESSOR COHERENCE: the type axis's `successor` (`Type@e ↝ Type@(succ e)`) maps under
the bridge to the kernel's level-bump `universeCodeCell e.lsucc` — which is precisely the classifier the kernel's
`HasTypeUnion.universeFormation` produces (`Type@L : Type@(L+1)`).  fib-2b installs the El decode (tying the bridge
to the shipped Tarski roundtrip `tarskiDecode`/`universeMembership_iff`); fib-2c flips
`fxFib_hasTypeTermUniverseReflection` and closes the type-20 Tarski↔Russell coherence.

## Zero-axiom

The forward bridge is a `universeCodeCell` application; the round-trip and successor coherence are `rfl` (struct
eta + the `fxTarskiUniverse.successor` projection).  No term-head partial match, no `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Core.Fib

open FX1Poly.Core FX1Poly.Tier0 FX1Poly.Typed FX1Poly.Universe

/-- **The forward bridge: a type-axis universe code becomes the kernel's term-level universe cell.**  Maps the
standalone Tarski code `{ level, flag }` to `universeCodeCell level flag`, the `.type`-sorted kernel term. -/
def axisCodeToCell {scope : Nat} (code : UniverseCode) : RawTerm scope :=
  universeCodeCell code.level code.flag

/-- **The on-the-nose payload coincidence.**  The bridged cell IS `gen_universeCode` applied to the axis code's
`(level, flag)` payload — the abstract Tarski code and the kernel's `gen_universeCode` payload are the same data. -/
theorem axisCodeToCell_unfold {scope : Nat} (code : UniverseCode) :
    (axisCodeToCell code : RawTerm scope)
      = .mkGen .gen_universeCode (code.level, code.flag) .childNil :=
  rfl

/-- The reverse map at the DATA level — recover a type-axis code from a `gen_universeCode` payload (no term-head
pattern match needed; the kernel cell exposes its payload `(level, flag)` directly). -/
def payloadToAxisCode (payload : LevelExpr × UniverseFlag) : UniverseCode :=
  { level := payload.1, flag := payload.2 }

/-- **The round-trip (data level).**  Recovering a type-axis code from the payload the bridge emits returns the
original code — the bridge loses nothing.  `rfl` by structure eta. -/
theorem payloadToAxisCode_roundTrip (code : UniverseCode) :
    payloadToAxisCode (code.level, code.flag) = code :=
  rfl

/-- **★ The successor coherence.**  The type axis's `successor` (`Type@e ↝ Type@(succ e)`) maps under the bridge to
the kernel's level-bump `universeCodeCell e.lsucc flag` — which is EXACTLY the classifier the kernel's
`HasTypeUnion.universeFormation` assigns to `universeCodeCell e flag` (`Type@L : Type@(L+1)`).  So the standalone
Tarski successor and the kernel universe-formation rule agree on the nose at the code level. -/
theorem axisSuccessor_eq_levelBump {scope : Nat} (code : UniverseCode) :
    (axisCodeToCell (fxTarskiUniverse.successor code) : RawTerm scope)
      = universeCodeCell code.level.lsucc code.flag :=
  rfl

/-- The bridge sends the axis level/flag projections to the kernel cell's payload components — the projections
commute with the bridge.  `rfl`. -/
theorem axisCodeToCell_preserves_level {scope : Nat} (code : UniverseCode) :
    (axisCodeToCell code : RawTerm scope) = universeCodeCell code.level code.flag :=
  rfl

end FX1Poly.Core.Fib
