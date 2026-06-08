import FX1Poly.Typed.MetatheoryFuzz
import FX1Poly.Typed.TypedNormalizer

/-! Probe: the verified SN-normalizer (HasTypeDescPi.normalForm, SN-112) COMPUTES every member of both
    §27.3-L2 fuzz families to the canonical value Type@0, and the two families' normal forms coincide. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

theorem metatheoryFuzzFamily_normalizesToType0 {profile : PolyProfile} (n : Nat) :
    (metatheoryFuzzFamily_typed (profile := profile) n).normalForm
      = universeCodeCell LevelExpr.lzero UniverseFlag.standard :=
  ((metatheoryFuzzFamily_typed (profile := profile) n).reachedNormalForm_eq_normalForm
    (metatheoryFuzzFamily_reducesToType0 n) (by decide)).symm

theorem metatheoryFuzzConstantFamily_normalizesToType0 {profile : PolyProfile} (n : Nat) :
    (metatheoryFuzzConstantFamily_typed (profile := profile) n).normalForm
      = universeCodeCell LevelExpr.lzero UniverseFlag.standard :=
  ((metatheoryFuzzConstantFamily_typed (profile := profile) n).reachedNormalForm_eq_normalForm
    (metatheoryFuzzConstantFamily_reducesToType0 n) (by decide)).symm

theorem metatheoryFuzz_normalFormsAgree {profile : PolyProfile} (identityDepth constantDepth : Nat) :
    (metatheoryFuzzFamily_typed (profile := profile) identityDepth).normalForm
      = (metatheoryFuzzConstantFamily_typed (profile := profile) constantDepth).normalForm :=
  (metatheoryFuzzFamily_normalizesToType0 identityDepth).trans
    (metatheoryFuzzConstantFamily_normalizesToType0 constantDepth).symm

end FX1Poly.Typed

#print axioms FX1Poly.Typed.metatheoryFuzzFamily_normalizesToType0
#print axioms FX1Poly.Typed.metatheoryFuzz_normalFormsAgree
