import FX1Poly.Typed.HasTypeDescPi

/-! # FX1Poly/Typed/NullaryFormerFormation
    — the engine-side formation primitive for NULLARY type-formers (CON-A2, parametric)

The Π/Σ formation reconstructions (`hasTypeDesc_piFormation_viaGenArm`,
`hasTypeDesc_sigmaFormation_viaGenArm`) witness the BINARY type-formers through the generic
`genFormation`/`genFormationPi` arm.  This file ships the NULLARY twin: any generator carrying the
shared `universeFormerOutput` row, with ZERO children, types as `Type@0` through the SAME generic
arm — no new `HasTypeDescPi` arm, one `typingRuleDescOf` row (P13 cascade-freedom, extended to the
nullary shape).

## Why this is exactly the consistency-FORMATION primitive (engine-side CON-A2)

The empty type `Empty` is a nullary type-former: `⊢ Empty : Type@0`, no formation premises, no
value generators.  fx_design §3.9 (the bottom type `never`) and the codebase's existing
bespoke-per-data-type discipline (value generators `gen_boolTrue` / `gen_natZero` / `gen_unit`,
NOT a general `Ind` former) make `Empty` a future bespoke nullary generator `gen_emptyCode`
(arity 0, `binderShifts = []`, `Unit` payload).  Once that generator lands carrying the
`universeFormerOutput` row, THIS lemma instantiates — with `children := .childNil` and
`premise := DescTelescopePi.nil context flag`, both discharged by `rfl` — to the concrete
`⊢ Empty : Type@0`, the formation half of SN-050.

The lemma is the honest PARAMETRIC target signature for CON-A2 (the twin of
`consistencyFromEmptyCandidateBridge` for CON-A0): it is proven NOW, over the engine, abstracted
over the not-yet-added generator, so the final `Empty : Type@0` wire is a one-line instantiation —
the genuine remaining work is the substrate generator addition (the bounded ~12-16-arm Core
extension) and the candidate bridge CON-A3 (`gen_emptyCode`'s reducibility candidate IS the empty
candidate), NOT the formation, which is settled here.

It generalizes beyond `Empty`: it is the formation rule for EVERY nullary base type-former (a unit
type, a future closed base type, …) carrying the universe-former output — one lemma, all nullary
formers.

## The load-bearing computation

`universeFormerOutput scope levels flag = universeCodeCell (lmaxAll levels) flag`, and
`lmaxAll [] = LevelExpr.lzero` (the empty fold's base) — so the nullary output is `Type@0` by
`rfl`.  `universeFormerOutput_nil` names that fact; the formation lemma rides it through
`genFormationPi` (whose conclusion `rule.outputType scope [] flag` reduces to `universeCodeCell
lzero flag` definitionally, so no cast / no `▸` is needed).

## Scope of consistency vs this lemma

This is the FORMATION half (`Empty` IS a type — establishing SN-050's NON-VACUITY: there genuinely
is a closed empty type once the generator lands).  The consistency PROOF itself routes through the
candidate bridge (closed membership ⟹ `False`), shipped abstractly as
`consistencyFromEmptyCandidateBridge`; it does not consume formation.  The two halves together pin
SN-050's complete residual.

## Zero-axiom verification

Both declarations are `rfl`-grade: `universeFormerOutput_nil` is `rfl`, and the formation lemma is
a direct `genFormationPi` application whose output classifier reduces to `Type@0` definitionally.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration audit-gated.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The nullary universe-former output is `Type@0`.**  The shared `universeFormerOutput` rule
sends a former to a universe code at the iterated `lmax` of its children's levels; with NO children
(`levels = []`) the fold bottoms out at `LevelExpr.lzero` (`lmaxAll [] = lzero`), so the output is
`Type@0`.  The load-bearing computation behind nullary-former formation — `rfl`. -/
theorem universeFormerOutput_nil (scope : Nat) (flag : UniverseFlag) :
    universeFormerOutput scope [] flag = universeCodeCell LevelExpr.lzero flag := rfl

/-- **Nullary type-former formation via the generic arm (engine-side CON-A2, parametric).**  For
ANY generator carrying the shared `universeFormerOutput` row, a cell with no children — witnessed
by the nil premise telescope `DescTelescopePi … [] flag children` (which forces `children =
.childNil`) — inhabits `Type@0`.  A direct `genFormationPi` application: its conclusion
`rule.outputType scope [] flag` is `universeFormerOutput scope [] flag`, which reduces to
`universeCodeCell LevelExpr.lzero flag` definitionally (`universeFormerOutput_nil`), so no transport
is needed.  Instantiating at the future `gen_emptyCode` (`binderShifts = []`, `children :=
.childNil`, `premise := DescTelescopePi.nil context flag`, all by `rfl`) gives `⊢ Empty : Type@0` —
the formation half of SN-050.  The nullary twin of `hasTypeDesc_piFormation_viaGenArm`; ZERO new
arms (P13). -/
theorem hasTypeDescPi_nullaryFormation_viaGenArm
    {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (generator : Generator) (flag : UniverseFlag)
    (payload : generator.payload scope)
    (children : RawTermChildren generator.binderShifts scope)
    (isFormation :
      typingRuleDescOf generator = some { outputType := universeFormerOutput })
    (premise :
      DescTelescopePi profile (currentDepth := 0) context [] flag children) :
    HasTypeDescPi profile context (.mkGen generator payload children)
      (universeCodeCell LevelExpr.lzero flag) :=
  HasTypeDescPi.genFormationPi context generator payload children []
    flag { outputType := universeFormerOutput } isFormation premise

end FX1Poly.Typed
