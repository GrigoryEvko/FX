import FX1Poly.Typed.HasTypeDescPiFormerCongruence

/-! # FX1Poly/Typed/OptionFormationSmoke
    — the optionCode data type-code formation reconstruction + a concrete `Option (Type@0) : Type@1` witness (GTL-13)

GTL-13 added `gen_optionCode` to `typingRuleDescOf`, so the grown engine `HasTypeDescPi` types the `optionCode`
data former.  This file is the honest verification of that landing: the reusable one-child option-former
formation reconstruction (`optionFormationViaGenArm`, the option twin of `listFormationViaGenArm`) and a
CONCRETE, NON-VACUOUS witness that a real closed `Option` term is typed — not merely that the row "compiles".

## The reconstruction

`HasTypeDescPi.optionFormationViaGenArm`: from `elementCode : Type@elementLevel`, the data former
`Option elementCode` is typed at `Type@elementLevel`.  Routed through the generic `genFormationPi` arm over the
ONE-element premise telescope (`lmaxAll [elementLevel] = elementLevel` by `rfl`), exactly the shape of
`listFormationViaGenArm`.

## The smoke

`optionFormationSmoke`: `Option (Type@0) : Type@1` in the empty context — the element `Type@0` is typed at
`Type@1` (`ofFormation` of `HasTypeDesc.universeFormation`), and `optionFormationViaGenArm` lifts it to the
former at `Type@1`.  A genuine closed `HasTypeDescPi` derivation: the GTL-13 payoff exhibited concretely,
locked into the audit as regression protection.

## Zero-axiom verification

The reconstruction: one `refine HasTypeDescPi.genFormationPi …` over `typingRuleDescOf_optionCode` (`rfl`) + two
`DescTelescopePi` constructors (`cons` then `nil`).  The smoke: a single applied term over the reconstruction +
`ofFormation`/`universeFormation`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Grown-engine `optionCode` data-former formation via the generic arm.**  From `elementCode :
Type@elementLevel`, the data former `Option elementCode` is typed at `Type@elementLevel`.  The one-child option
twin of `listFormationViaGenArm`: routed through the generic `genFormationPi` arm over the single-element premise
telescope (`lmaxAll [elementLevel] = elementLevel` by `rfl`). -/
theorem HasTypeDescPi.optionFormationViaGenArm {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (elementCode : RawTerm scope)
    (elementLevel : LevelExpr) (flag : UniverseFlag)
    (elementTyped :
      HasTypeDescPi profile context elementCode (universeCodeCell elementLevel flag)) :
    HasTypeDescPi profile context
      (.mkGen .gen_optionCode () (.childCons elementCode .childNil))
      (universeCodeCell elementLevel flag) := by
  refine HasTypeDescPi.genFormationPi context .gen_optionCode ()
    (.childCons elementCode .childNil) [elementLevel]
    flag { outputType := universeFormerOutput } typingRuleDescOf_optionCode ?_
  exact DescTelescopePi.cons (currentDepth := 0) context elementCode elementLevel
    [] flag .childNil elementTyped
    (DescTelescopePi.nil (currentDepth := 1) (context.cons elementCode) flag)

/-- **`Option (Type@0) : Type@1` — the concrete GTL-13 typing witness.**  A genuine closed `HasTypeDescPi`
derivation that the grown engine types a real `Option` data former: the element `Type@0` is a type
(`ofFormation` of `HasTypeDesc.universeFormation` gives `Type@0 : Type@1`), and `optionFormationViaGenArm` lifts
it to `Option (Type@0) : Type@1`.  Non-vacuous — exhibits the landing, not merely its compilation. -/
theorem optionFormationSmoke {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0)
      (.mkGen .gen_optionCode () (.childCons (universeCodeCell LevelExpr.lzero flag) .childNil))
      (universeCodeCell LevelExpr.lzero.lsucc flag) :=
  HasTypeDescPi.optionFormationViaGenArm TypingContext.empty
    (universeCodeCell LevelExpr.lzero flag) LevelExpr.lzero.lsucc flag
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.universeFormation TypingContext.empty LevelExpr.lzero flag))

end FX1Poly.Typed
