import FX1Poly.Typed.DenoteKeyedBoundedFundamentalMotive
import FX1Poly.Typed.DenoteKeyedBoundedAssemblyBridge

/-! # FX1Poly/Typed/BoundedFormationLeafArms
    — the +1-closing bounded formation leaf arms (BFT-7 var + BFT-9 universeFormation)

The bounded FORMATION fundamental theorem (the `HasTypeDesc.rec` dispatch, BFT-11) needs every arm in the
`+1`-closing `FundamentalConclusionAtBoundedSucc` shape (the recursor's `motive_1`).  Two of the four `HasTypeDesc`
constructors — `var` and `universeFormation` — are LEAVES whose arbitrary-scope bounded arms are already shipped
(`fundamentalVarAtBounded`, `fundamentalUniverseFormationAtBounded`, `DenoteKeyedBoundedFundamentalMotive.lean`).
Neither introduces a binder, so each lifts to the `+1` motive for free by `FundamentalConclusionAtBounded.toSucc`
(the down-cast in `DenoteKeyedBoundedAssemblyBridge.lean`).  This file ships the two named `+1` leaf arms; the
`conv` arm is already shipped as `fundamentalConvArmBoundedSucc` (BFT-8), and `genFormation` reuses BFT-4 + the
Σ-twin (BFT-10).

## The universeFormation `belowBound` gate (the bounded route's per-term fuel)

`fundamentalUniverseFormationAtBoundedSucc` threads `belowBound : denote (lsucc levelExpr) env < bound` — the
member side of no-Type-in-Type at the bounded layer (`Type@levelExpr : Type@(lsucc levelExpr)` requires the
classifier's decoded level below the bound).  The DENOTE formation FT (`formationFundamentalUniverseFormationArm`)
needs NO such gate (the denote universe candidate is level-unbounded), but the bounded universe member CARRIES the
gate — which is exactly the per-term "fuel" the eventual dispatch (BFT-11) + bound-choice (BFT-12) supply: pick
`bound` to exceed every universe level appearing in the derivation.  The `var` arm is gate-free (it reads the
environment, touching no universe level).

## Zero-axiom verification

Each arm is `FundamentalConclusionAtBounded.toSucc` applied to the shipped arbitrary-scope arm (called by full
name, not dot-projection — `FundamentalConclusionAtBounded` is a `def`, not a structure).  No induction, no
`funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega` (checked:
depends on no axioms).  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation
open StepStar

/-- **BFT-7: the +1-closing bounded `var` arm.**  A variable is a `+1`-closing bound-reducible member of its
looked-up type — the `FundamentalConclusionAtBounded.toSucc` lift of the leaf `fundamentalVarAtBounded` (no
binder, bound-independent: the environment lookup IS the goal). -/
theorem fundamentalVarAtBoundedSucc {profile : PolyProfile} {scope : Nat} (env : Nat → Nat) (bound : Nat)
    (context : TypingContext profile scope) (index : Fin scope) :
    FundamentalConclusionAtBoundedSucc env bound context (variableCell index) (context.lookup index) :=
  FundamentalConclusionAtBounded.toSucc (fundamentalVarAtBounded env bound context index)

/-- **BFT-9: the +1-closing bounded `universeFormation` arm.**  `Type@levelExpr` is a `+1`-closing bound-reducible
member of `Type@(lsucc levelExpr)` — the `FundamentalConclusionAtBounded.toSucc` lift of
`fundamentalUniverseFormationAtBounded`, threading the per-term gate `belowBound : denote (lsucc levelExpr) env <
bound` (the member side of no-Type-in-Type at the bounded layer; the dispatch supplies it from the bound-choice
fuel). -/
theorem fundamentalUniverseFormationAtBoundedSucc {profile : PolyProfile} {scope : Nat} (env : Nat → Nat)
    (bound : Nat) (context : TypingContext profile scope) (levelExpr : LevelExpr) (flag : UniverseFlag)
    (belowBound : LevelExpr.denote (LevelExpr.lsucc levelExpr) env < bound) :
    FundamentalConclusionAtBoundedSucc env bound context
      (universeCodeCell levelExpr flag) (universeCodeCell levelExpr.lsucc flag) :=
  FundamentalConclusionAtBounded.toSucc
    (fundamentalUniverseFormationAtBounded env bound context levelExpr flag belowBound)

end FX1Poly.Typed
