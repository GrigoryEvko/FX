import FX1Poly.Tier0.RepresentableMapCategory
import FX1Poly.Foundation.RawSubst.RenameDefs

/-! Scratch probe: the first concrete RawCategory instance for FX — the renaming (thinning) category,
    objects = scopes, morphisms = positional renamings. Category laws are rfl (function comp + eta). -/

namespace FX1Poly.Tier0

open FX1Poly.Foundation

/-- The FX renaming category: objects are scopes (`Nat`), morphisms are positional renamings
(`RawRenaming source target = Fin source → Fin target`). -/
def fxRenamingCategory : RawCategory.{0, 0} where
  Object := Nat
  Morphism := RawRenaming
  identity := fun _scope => RawRenaming.identity
  compose := fun firstRenaming secondRenaming => RawRenaming.compose firstRenaming secondRenaming
  composeAssoc := fun _firstRenaming _secondRenaming _thirdRenaming => rfl
  identityLeft := fun _renaming => rfl
  identityRight := fun _renaming => rfl

/-- The identity renaming is the categorical identity (sanity sample). -/
theorem fxRenamingCategory_identity_eq {scope : Nat} :
    fxRenamingCategory.identity scope = RawRenaming.identity (scope := scope) := rfl

/-- Categorical composition is renaming composition (sanity sample). -/
theorem fxRenamingCategory_compose_eq {scopeA scopeB scopeC : Nat}
    (firstRenaming : RawRenaming scopeA scopeB) (secondRenaming : RawRenaming scopeB scopeC) :
    fxRenamingCategory.compose firstRenaming secondRenaming =
      RawRenaming.compose firstRenaming secondRenaming := rfl

end FX1Poly.Tier0

#print axioms FX1Poly.Tier0.fxRenamingCategory
#print axioms FX1Poly.Tier0.fxRenamingCategory_identity_eq
#print axioms FX1Poly.Tier0.fxRenamingCategory_compose_eq
