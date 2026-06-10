import FX1Poly.Typed.HasTypeDescPiContextConversion
import FX1Poly.Typed.HasTypeDescContextConversion

/-! Probe: the GENERIC genFormationPi former step (covering ALL genFormationPi type-code formers — Π, Σ, list,
    option, id, equiv — in ONE theorem), built on the telescope-transport primitive. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

theorem DescTelescopePi.convTelescopeFromChildIH {profile : PolyProfile}
    (childConverts : ∀ {childScope : Nat}
        {childSource childTarget : TypingContext profile childScope}
        {childCode : RawTerm childScope} {childLevel : LevelExpr} {childFlag : UniverseFlag},
        HasTypeDescPi profile childSource childCode (universeCodeCell childLevel childFlag) →
        (∀ index : Fin childScope, Conv (childSource.lookup index) (childTarget.lookup index)) →
        HasTypeDescPi profile childTarget childCode (universeCodeCell childLevel childFlag))
    {baseScope currentDepth : Nat} {binderShifts : List Nat}
    {sourceContext : TypingContext profile (baseScope + currentDepth)}
    {levels : List LevelExpr} {flag : UniverseFlag}
    {children : RawTermChildren binderShifts baseScope}
    (telescope : DescTelescopePi profile sourceContext levels flag children) :
    ∀ (targetContext : TypingContext profile (baseScope + currentDepth)),
      (∀ index : Fin (baseScope + currentDepth),
        Conv (sourceContext.lookup index) (targetContext.lookup index)) →
      DescTelescopePi profile targetContext levels flag children :=
  match telescope with
  | .nil _sourceContext flag => fun targetContext _contextConv =>
      DescTelescopePi.nil targetContext flag
  | .cons _sourceContext head headLevel restLevels flag rest headTyped restTyped =>
      fun targetContext contextConv =>
        DescTelescopePi.cons targetContext head headLevel restLevels flag rest
          (childConverts headTyped contextConv)
          (DescTelescopePi.convTelescopeFromChildIH childConverts restTyped
            (targetContext.cons head) (convContextCondition_cons head contextConv))

/-- The generic genFormationPi former step: re-form a genFormationPi former under a context-converted target by
transporting its premise telescope via the per-child IH and re-firing genFormationPi.  Covers ALL genFormationPi
type-code formers (Π, Σ, list, option, id, equiv) in ONE theorem. -/
theorem HasTypeDescPi.genFormerValidityContextConversion {profile : PolyProfile}
    (childConverts : ∀ {childScope : Nat}
        {childSource childTarget : TypingContext profile childScope}
        {childCode : RawTerm childScope} {childLevel : LevelExpr} {childFlag : UniverseFlag},
        HasTypeDescPi profile childSource childCode (universeCodeCell childLevel childFlag) →
        (∀ index : Fin childScope, Conv (childSource.lookup index) (childTarget.lookup index)) →
        HasTypeDescPi profile childTarget childCode (universeCodeCell childLevel childFlag))
    {scope : Nat} {sourceContext targetContext : TypingContext profile scope}
    (generator : Generator) (payload : generator.payload scope)
    (children : RawTermChildren generator.binderShifts scope)
    (levels : List LevelExpr) (flag : UniverseFlag)
    (rule : TypingRuleDesc) (isFormation : typingRuleDescOf generator = some rule)
    (premises : DescTelescopePi profile (currentDepth := 0) sourceContext levels flag children)
    (contextConv : ∀ index : Fin scope,
      Conv (sourceContext.lookup index) (targetContext.lookup index)) :
    HasTypeDescPi profile targetContext (.mkGen generator payload children)
      (rule.outputType scope levels flag) :=
  HasTypeDescPi.genFormationPi targetContext generator payload children levels flag rule isFormation
    (DescTelescopePi.convTelescopeFromChildIH childConverts premises targetContext contextConv)

end FX1Poly.Typed

#print axioms FX1Poly.Typed.DescTelescopePi.convTelescopeFromChildIH
#print axioms FX1Poly.Typed.HasTypeDescPi.genFormerValidityContextConversion
