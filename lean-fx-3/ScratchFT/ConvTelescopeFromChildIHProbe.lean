import FX1Poly.Typed.HasTypeDescPiContextConversion
import FX1Poly.Typed.HasTypeDescContextConversion

/-! Probe: the telescope-validity transport gated on an ABSTRACT per-child type-code-validity IH — the
    reusable primitive the generic genFormationPi former step needs.  Mirrors convTelescopeOfPiElimArm
    (GrownCtxConv-3) but parameterized on the recursive type-code IH (`childConverts`, universe-code-PRESERVING)
    instead of the general `piElimArm`.  Structural recursion over the telescope: each head re-types via the IH,
    each tail recurses under the cons-lifted context-conversion. -/

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

end FX1Poly.Typed

#print axioms FX1Poly.Typed.DescTelescopePi.convTelescopeFromChildIH
