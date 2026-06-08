import FX1Poly.Typed.MetatheoryFuzz
import FX1Poly.Typed.UniverseCodeConversion

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

theorem metatheoryFuzzFamily_convToType0 (n : Nat) :
    Conv (metatheoryFuzzFamily n) (universeCodeCell LevelExpr.lzero UniverseFlag.standard) :=
  Conv.fromStepStar (metatheoryFuzzFamily_reducesToType0 n)

theorem metatheoryFuzzConstantFamily_convToType0 (n : Nat) :
    Conv (metatheoryFuzzConstantFamily n) (universeCodeCell LevelExpr.lzero UniverseFlag.standard) :=
  Conv.fromStepStar (metatheoryFuzzConstantFamily_reducesToType0 n)

theorem metatheoryFuzzFamily_intraConvertible (firstDepth secondDepth : Nat) :
    Conv (metatheoryFuzzFamily firstDepth) (metatheoryFuzzFamily secondDepth) :=
  Conv.trans (metatheoryFuzzFamily_convToType0 firstDepth)
    (Conv.sym (metatheoryFuzzFamily_convToType0 secondDepth))

theorem metatheoryFuzz_crossFamilyConvertible (identityDepth constantDepth : Nat) :
    Conv (metatheoryFuzzFamily identityDepth) (metatheoryFuzzConstantFamily constantDepth) :=
  Conv.trans (metatheoryFuzzFamily_convToType0 identityDepth)
    (Conv.sym (metatheoryFuzzConstantFamily_convToType0 constantDepth))

theorem metatheoryFuzzFamily_notConvToType1 (n : Nat) :
    ¬ Conv (metatheoryFuzzFamily n)
        (universeCodeCell LevelExpr.lzero.lsucc UniverseFlag.standard) := by
  intro convToType1
  have type0ConvType1 : Conv (universeCodeCell LevelExpr.lzero UniverseFlag.standard)
      (universeCodeCell LevelExpr.lzero.lsucc UniverseFlag.standard) :=
    Conv.trans (Conv.sym (metatheoryFuzzFamily_convToType0 n)) convToType1
  obtain ⟨levelEq, _flagEq⟩ := universeCodeCell_inj_of_conv type0ConvType1
  exact LevelExpr.noConfusion levelEq

end FX1Poly.Typed

#print axioms FX1Poly.Typed.metatheoryFuzz_crossFamilyConvertible
#print axioms FX1Poly.Typed.metatheoryFuzzFamily_notConvToType1
