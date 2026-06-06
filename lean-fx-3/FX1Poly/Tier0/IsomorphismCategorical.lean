import FX1Poly.Tier0.RepresentableMapCategory

/-! # FX1Poly/Tier0/IsomorphismCategorical
    — generic categorical isomorphism infrastructure for the CwR axioms

`RepresentableMapCategory.lean` defines `IsIsomorphism` and `PullbackSquare` but proves nothing about them.
`FxRenamingCategory.lean` builds the first concrete `RawCategory` for FX (the renaming category).  The next
step toward a concrete `RepresentableMapCategory` (`fxBaseRMC`) is its three CwR axioms:
`isomorphismsRepresentable`, `closedUnderComposition`, `closedUnderPullback`.

For the SMALLEST valid representable-map class — the isomorphisms — those axioms reduce to three generic
categorical facts, BASE-INDEPENDENT (they hold in any `RawCategory`, so they are reusable whether `fxBaseRMC`
ends up over the renaming category or the richer substitution category):

  * `isomorphismsRepresentable` ⟸ trivial (an iso is an iso).
  * `closedUnderComposition` ⟸ `IsIsomorphism.comp` (isomorphisms compose).
  * `closedUnderPullback` ⟸ `IsIsomorphism.pullbackAlong` (the pullback of an iso along any morphism exists,
    with its universal property, and its right projection is the identity — itself an iso, hence representable).

This file proves those three generic facts (plus `IsIsomorphism.identity`).  Each is pure equational reasoning
through the category's own law fields (`composeAssoc`, `identityLeft`, `identityRight`) and the given inverse
laws — no `funext` (morphism-equality by extensionality would pull `Quot.sound`), so all zero-axiom.

## What lands here (all zero-axiom)

  * `IsIsomorphism.identity` — the identity morphism is an isomorphism (its own inverse).
  * `IsIsomorphism.comp` — isomorphisms are closed under composition (`(f ∘ g)⁻¹ = g⁻¹ ∘ f⁻¹`).
  * `IsIsomorphism.pullbackAlong` — the pullback of an isomorphism `f` along any `g` is the square with apex
    the domain of `g`, right projection the identity, left projection `g ∘ f⁻¹`, together with its universal
    property.  The construction the iso-class `closedUnderPullback` axiom consumes.

## Zero-axiom verification

`rfl`/`rw` chains over the `RawCategory` law fields and the `IsIsomorphism` inverse laws, plus one record
literal per declaration.  No induction, no `funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Tier0

universe u v

/-- **The identity morphism is an isomorphism** (its own two-sided inverse). -/
def IsIsomorphism.identity {category : RawCategory.{u, v}} (objectA : category.Object) :
    IsIsomorphism category (category.identity objectA) where
  inverse := category.identity objectA
  leftInverse := category.identityLeft _
  rightInverse := category.identityRight _

/-- **Isomorphisms are closed under composition.**  The inverse of `f ∘ g` is `g⁻¹ ∘ f⁻¹`; the two-sided
inverse laws follow by reassociating and cancelling the inner inverse pair.  Discharges the `closedUnderComposition`
CwR axiom for the isomorphism class. -/
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
`g ∘ f⁻¹` is a pullback (it commutes, and any cone factors uniquely through `B` via its own right leg).  The
construction the iso-class `closedUnderPullback` CwR axiom consumes: the right projection is the identity, an
isomorphism, hence representable. -/
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
