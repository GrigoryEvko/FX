import FX1Poly.Typed.HasTypeDescPiFormerCongruence

/-! # FX1Poly/Typed/ListFormationSmoke
    — the data type-code formation reconstruction + a concrete `List (Type@0) : Type@1` witness (GTL-14)

GTL-11 added `gen_listCode` to `typingRuleDescOf`, so the grown engine `HasTypeDescPi` types the `listCode`
data former.  This file is the honest verification of that landing: a REUSABLE one-child formation
reconstruction (`listFormationViaGenArm`, the data-former twin of `piFormationViaGenArm`/`sigmaFormation-
ViaGenArm`) and a CONCRETE, NON-VACUOUS witness that a real closed `List` term is typed — not merely that the
row "compiles".

## The reconstruction

`HasTypeDescPi.listFormationViaGenArm`: from `elementCode : Type@elementLevel`, the data former
`List elementCode` is typed at `Type@elementLevel`.  Routed through the generic `genFormationPi` arm over the
ONE-element premise telescope `DescTelescopePi.cons … (DescTelescopePi.nil …)` — the exact recipe of the
shipped Π/Σ `…ViaGenArm`, one child shorter (no codomain binder, no `lmax`: `lmaxAll [elementLevel] =
elementLevel` by `rfl`, since `lmaxFold acc [] = acc`).  This is the grown-engine analogue of the formation
`hasTypeDesc_*Formation_viaGenArm` family and the introduction a future data-constructor typing rule reads.

## The smoke

`listFormationSmoke`: `List (Type@0) : Type@1` in the empty context — the element `Type@0`
(`universeCodeCell lzero`) is typed at `Type@1` (`ofFormation` of `HasTypeDesc.universeFormation`), and
`listFormationViaGenArm` lifts it to the former at `Type@1`.  A genuine closed `HasTypeDescPi` derivation: the
GTL-11 payoff exhibited concretely, locked into the audit as regression protection.

## Zero-axiom verification

The reconstruction: one `refine HasTypeDescPi.genFormationPi …` over `typingRuleDescOf_listCode` (`rfl`) +
two `DescTelescopePi` constructors (`cons` then `nil`).  The smoke: a single applied term over the
reconstruction + `ofFormation`/`universeFormation`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Grown-engine `listCode` data-former formation via the generic arm.**  From `elementCode :
Type@elementLevel`, the data former `List elementCode` is typed at `Type@elementLevel`.  The one-child
data-former twin of `piFormationViaGenArm` / `sigmaFormationViaGenArm`: routed through the generic
`genFormationPi` arm over the single-element premise telescope (`lmaxAll [elementLevel] = elementLevel` by
`rfl`).  The reusable grown reconstruction the GTL-11 landing makes available — and the introduction a future
`List`-constructor typing rule consumes. -/
theorem HasTypeDescPi.listFormationViaGenArm {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (elementCode : RawTerm scope)
    (elementLevel : LevelExpr) (flag : UniverseFlag)
    (elementTyped :
      HasTypeDescPi profile context elementCode (universeCodeCell elementLevel flag)) :
    HasTypeDescPi profile context
      (.mkGen .gen_listCode () (.childCons elementCode .childNil))
      (universeCodeCell elementLevel flag) := by
  refine HasTypeDescPi.genFormationPi context .gen_listCode ()
    (.childCons elementCode .childNil) [elementLevel]
    flag { outputType := universeFormerOutput } typingRuleDescOf_listCode ?_
  exact DescTelescopePi.cons (currentDepth := 0) context elementCode elementLevel
    [] flag .childNil elementTyped
    (DescTelescopePi.nil (currentDepth := 1) (context.cons elementCode) flag)

/-- **`List (Type@0) : Type@1` — the concrete GTL-11 typing witness.**  A genuine closed `HasTypeDescPi`
derivation that the grown engine types a real `List` data former: the element `Type@0` is a type
(`ofFormation` of `HasTypeDesc.universeFormation` gives `Type@0 : Type@1`), and `listFormationViaGenArm` lifts
it to `List (Type@0) : Type@1`.  Non-vacuous — exhibits the landing, not merely its compilation. -/
theorem listFormationSmoke {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0)
      (.mkGen .gen_listCode () (.childCons (universeCodeCell LevelExpr.lzero flag) .childNil))
      (universeCodeCell LevelExpr.lzero.lsucc flag) :=
  HasTypeDescPi.listFormationViaGenArm TypingContext.empty
    (universeCodeCell LevelExpr.lzero flag) LevelExpr.lzero.lsucc flag
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.universeFormation TypingContext.empty LevelExpr.lzero flag))

end FX1Poly.Typed
