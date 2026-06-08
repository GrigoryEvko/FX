import FX1Poly.Tier0.RepresentableMapCategory

/-! Scratch probe: generic categorical isomorphism infrastructure for any RawCategory — the building blocks
    the CwR iso-class axioms (closedUnderComposition + closedUnderPullback) consume. Zero-axiom (equational). -/

namespace FX1Poly.Tier0

universe u v

/-- The identity morphism is an isomorphism (its own inverse). -/
def IsIsomorphism.identity {category : RawCategory.{u, v}} (objectA : category.Object) :
    IsIsomorphism category (category.identity objectA) where
  inverse := category.identity objectA
  leftInverse := category.identityLeft _
  rightInverse := category.identityRight _

/-- Isomorphisms are closed under composition: the inverse of `f ∘ g` is `g⁻¹ ∘ f⁻¹`. -/
def IsIsomorphism.comp {category : RawCategory.{u, v}} {objectA objectB objectC : category.Object}
    {morphismF : category.Morphism objectA objectB} {morphismG : category.Morphism objectB objectC}
    (isoF : IsIsomorphism category morphismF) (isoG : IsIsomorphism category morphismG) :
    IsIsomorphism category (category.compose morphismF morphismG) where
  inverse := category.compose isoG.inverse isoF.inverse
  leftInverse := by
    rw [category.composeAssoc, ← category.composeAssoc isoF.inverse morphismF morphismG,
      isoF.leftInverse, category.identityLeft, isoG.leftInverse]
  rightInverse := by
    rw [category.composeAssoc, ← category.composeAssoc morphismG isoG.inverse isoF.inverse,
      isoG.rightInverse, category.identityLeft, isoF.rightInverse]

/-- **The pullback of an isomorphism along any morphism exists, with its universal property.**  For an iso
`f : A → C` and any `g : B → C`, the square with apex `B`, right projection the identity, and left projection
`g ∘ f⁻¹` is a pullback.  The construction the CwR `closedUnderPullback` axiom uses for the isomorphism class:
the right projection is the identity, itself an isomorphism (hence representable). -/
def IsIsomorphism.pullbackAlong {category : RawCategory.{u, v}}
    {objectA objectB objectC : category.Object}
    {morphismF : category.Morphism objectA objectC} {morphismG : category.Morphism objectB objectC}
    (isoF : IsIsomorphism category morphismF) :
    PullbackSquare category morphismF morphismG where
  pullbackObject := objectB
  projectionLeft := category.compose morphismG isoF.inverse
  projectionRight := category.identity objectB
  commutes := by
    rw [category.composeAssoc, isoF.leftInverse, category.identityRight, category.identityLeft]
  isUniversal := by
    intro candidateObject candidateLeft candidateRight commuteSquare
    refine ⟨candidateRight, ?_, ?_⟩
    · rw [← category.composeAssoc, ← commuteSquare, category.composeAssoc, isoF.rightInverse,
        category.identityRight]
    · rw [category.identityRight]

end FX1Poly.Tier0

#print axioms FX1Poly.Tier0.IsIsomorphism.identity
#print axioms FX1Poly.Tier0.IsIsomorphism.comp
#print axioms FX1Poly.Tier0.IsIsomorphism.pullbackAlong
