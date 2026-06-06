import FX1Poly.Typed.IsTypeDescDecidableGeneric

/-! # FX1Poly/Typed/IsTypeDescGenericSmoke
    — non-vacuity + definitional-computation smoke corpus for the cascade-free decider

The cascade-free `IsTypeDesc.decideTypeGeneric` (`IsTypeDescDecidableGeneric.lean`) is a
GENUINE total decision procedure — but a `PSum`-valued decider could in principle be vacuous (always `.inr`) or
fail to COMPUTE (block on a `by`-tactic-generated term).  This file closes both gaps with closed-cell fixtures,
each proved `by rfl` — so the kernel actually REDUCES the whole structural mutual recursion to the right
constructor (`decideTypeGeneric` is a computable function, not merely a proof-carrying existence):

  * Π / Σ / nested-Π type codes ⇒ `.inl` (a type) — exercising the cascade-free former dispatch +
    `decideSynthGeneric` flag synthesis + the telescope spine recursion (and, for nested Π, recursion UNDER a
    binder via `WfContextDesc.cons`).
  * `universeCodeCell` ⇒ `.inl` — the universe leaf.
  * `unitCell` (`gen_unit`, a VALUE former, never a type) ⇒ `.inr` — a stable negative.
  * `emptyTypeCell` (`gen_emptyCode`, NOT yet in `typingRuleDescOf`) ⇒ `.inr` — the GTL-11-deferred data-type
    row: the decider HONESTLY refuses it today and will FLIP to `.inl` zero-touch once the `typingRuleDescOf`
    row lands (the FRAME-2 demonstration), so this fixture doubles as the GTL-11 regression marker.

`decidesAsTypeBool` is the Boolean projection of the decision (the constructor tag), the readable smoke target.

## Zero-axiom verification

Each smoke is `by rfl` (kernel `decide`-free definitional reduction of `decideTypeGeneric`); `rfl` introduces no
axioms and reduction is pure unfolding of the zero-axiom structural recursion.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- The Boolean projection of the cascade-free decision: `true` iff `decideTypeGeneric` finds a universe witness
(`.inl`), `false` iff it refutes (`.inr`).  The readable target of the smoke corpus. -/
def IsTypeDesc.decidesAsTypeBool {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} (wellFormed : WfContextDesc context)
    (classifier : RawTerm scope) : Bool :=
  match IsTypeDesc.decideTypeGeneric wellFormed classifier with
  | .inl _ => true
  | .inr _ => false

/-- A `universeCodeCell` is a type (the universe leaf, `.inl`). -/
theorem decideTypeGeneric_smoke_universeCode {profile : PolyProfile} :
    IsTypeDesc.decidesAsTypeBool (profile := profile) WfContextDesc.emptyIsWellFormed
      (universeCodeCell LevelExpr.lzero UniverseFlag.standard) = true := by rfl

/-- A closed `Π` type code is a type — the cascade-free former dispatch + telescope synthesis compute `.inl`. -/
theorem decideTypeGeneric_smoke_pi {profile : PolyProfile} :
    IsTypeDesc.decidesAsTypeBool (profile := profile) WfContextDesc.emptyIsWellFormed
      (piTyCodeCell (universeCodeCell LevelExpr.lzero UniverseFlag.standard)
        (universeCodeCell LevelExpr.lzero UniverseFlag.standard)) = true := by rfl

/-- A closed `Σ` type code is a type — same dispatch, only the head generator differs (no new arm). -/
theorem decideTypeGeneric_smoke_sigma {profile : PolyProfile} :
    IsTypeDesc.decidesAsTypeBool (profile := profile) WfContextDesc.emptyIsWellFormed
      (sigmaTyCodeCell (universeCodeCell LevelExpr.lzero UniverseFlag.standard)
        (universeCodeCell LevelExpr.lzero UniverseFlag.standard)) = true := by rfl

/-- A NESTED `Π` (domain is itself a `Π`) is a type — exercising recursion under the binder
(`WfContextDesc.cons`) and deeper telescope synthesis. -/
theorem decideTypeGeneric_smoke_nestedPi {profile : PolyProfile} :
    IsTypeDesc.decidesAsTypeBool (profile := profile) WfContextDesc.emptyIsWellFormed
      (piTyCodeCell
        (piTyCodeCell (universeCodeCell LevelExpr.lzero UniverseFlag.standard)
          (universeCodeCell LevelExpr.lzero UniverseFlag.standard))
        (universeCodeCell LevelExpr.lzero UniverseFlag.standard)) = true := by rfl

/-- `unitCell` (`gen_unit`, a VALUE former) is NOT a type — a stable negative (`.inr`). -/
theorem decideTypeGeneric_smoke_unit {profile : PolyProfile} :
    IsTypeDesc.decidesAsTypeBool (profile := profile) WfContextDesc.emptyIsWellFormed
      (unitCell : RawTerm 0) = false := by rfl

/-- `emptyTypeCell` (`gen_emptyCode`, not yet a `typingRuleDescOf` row) is refused TODAY (`.inr`) — the
GTL-11-deferred data-type row; this fixture FLIPS to `.inl` zero-touch when the row lands. -/
theorem decideTypeGeneric_smoke_emptyCodeDeferred {profile : PolyProfile} :
    IsTypeDesc.decidesAsTypeBool (profile := profile) WfContextDesc.emptyIsWellFormed
      (emptyTypeCell : RawTerm 0) = false := by rfl

end FX1Poly.Typed
