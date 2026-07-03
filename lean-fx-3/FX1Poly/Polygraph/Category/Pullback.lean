import FX1Poly.Polygraph.Category.RawCategory
/-!
# Morphism Classes, Pullback Squares, and Isomorphisms (generic limit core)

The generic limit-theoretic core over an ARBITRARY `RawCategory`: a
distinguished `MorphismClass`, the `PullbackSquare` (weakly-universal cone) with
its strictness predicate `IsStrict`, the leg-swap and pasting constructions
(with their strictness preservation), and the `IsIsomorphism` predicate.

Pure category theory — nothing here mentions contexts or representable maps.
The pasting lemma (`PullbackSquare.paste`) is the categorical content behind
Uemura's "representable maps closed under composition and stable under pullback"
axiom, but the construction itself is context-free.

Zero external dependencies. Raw Lean 4 + Init + the sibling `RawCategory`.
-/

namespace FX1Poly.Polygraph

universe u v

/-- A distinguished class of morphisms in a category. -/
structure MorphismClass (category : RawCategory.{u, v}) where
  member : {objectA objectB : category.Object} →
           category.Morphism objectA objectB → Prop
  memberDecidable : {objectA objectB : category.Object} →
                    (morphism : category.Morphism objectA objectB) →
                    Decidable (member morphism)

/-- A pullback square in a category:
```
  pullbackObject ---projRight--→ objectB
       |                           |
    projLeft                    morphismG
       |                           |
       ↓                           ↓
    objectA -----morphismF----→ objectC
```
-/
structure PullbackSquare (category : RawCategory.{u, v})
    {objectA objectB objectC : category.Object}
    (morphismF : category.Morphism objectA objectC)
    (morphismG : category.Morphism objectB objectC) where
  pullbackObject : category.Object
  projectionLeft : category.Morphism pullbackObject objectA
  projectionRight : category.Morphism pullbackObject objectB
  commutes : category.compose projectionLeft morphismF =
             category.compose projectionRight morphismG
  isUniversal : ∀ (candidateObject : category.Object)
    (candidateLeft : category.Morphism candidateObject objectA)
    (candidateRight : category.Morphism candidateObject objectB),
    category.compose candidateLeft morphismF =
    category.compose candidateRight morphismG →
    ∃ (mediator : category.Morphism candidateObject pullbackObject),
      category.compose mediator projectionLeft = candidateLeft ∧
      category.compose mediator projectionRight = candidateRight

/-- A `PullbackSquare` is a GENUINE (strict) pullback — an actual limit, not merely a weak one — when its
mediator is UNIQUE: any two morphisms into the pullback object that agree with both projections coincide.

`PullbackSquare.isUniversal` records only mediator EXISTENCE (`∃`), so a bare `PullbackSquare` is a WEAK
pullback (a weakly-universal cone).  `IsStrict` supplies the missing uniqueness half; a `PullbackSquare`
together with an `IsStrict` witness IS a genuine categorical pullback.  (The distinction is faithful to the
mathematics: only the strict version makes reindexing a functor / the universal property a limit.) -/
def PullbackSquare.IsStrict {category : RawCategory.{u, v}}
    {objectA objectB objectC : category.Object}
    {morphismF : category.Morphism objectA objectC} {morphismG : category.Morphism objectB objectC}
    (square : PullbackSquare category morphismF morphismG) : Prop :=
  ∀ {candidateObject : category.Object}
    (mediatorOne mediatorTwo : category.Morphism candidateObject square.pullbackObject),
    category.compose mediatorOne square.projectionLeft
      = category.compose mediatorTwo square.projectionLeft →
    category.compose mediatorOne square.projectionRight
      = category.compose mediatorTwo square.projectionRight →
    mediatorOne = mediatorTwo

/-- The SWAP of a pullback square — exchanging the two cospan legs.  A `PullbackSquare f g` (cospan
`A --f--> C <--g-- B`) becomes a `PullbackSquare g f`, with the two projections exchanged.  Pullbacks are
symmetric in their legs. -/
def PullbackSquare.swap {category : RawCategory.{u, v}}
    {objectA objectB objectC : category.Object}
    {morphismF : category.Morphism objectA objectC} {morphismG : category.Morphism objectB objectC}
    (square : PullbackSquare category morphismF morphismG) :
    PullbackSquare category morphismG morphismF where
  pullbackObject := square.pullbackObject
  projectionLeft := square.projectionRight
  projectionRight := square.projectionLeft
  commutes := square.commutes.symm
  isUniversal := fun candidateObject candidateLeft candidateRight cone =>
    let ⟨mediator, factLeft, factRight⟩ :=
      square.isUniversal candidateObject candidateRight candidateLeft cone.symm
    ⟨mediator, factRight, factLeft⟩

/-- The swap of a STRICT pullback is strict. -/
theorem PullbackSquare.swap_isStrict {category : RawCategory.{u, v}}
    {objectA objectB objectC : category.Object}
    {morphismF : category.Morphism objectA objectC} {morphismG : category.Morphism objectB objectC}
    {square : PullbackSquare category morphismF morphismG} (strict : square.IsStrict) :
    square.swap.IsStrict :=
  fun mediatorOne mediatorTwo projLeftEq projRightEq => strict mediatorOne mediatorTwo projRightEq projLeftEq

/-- ★ **The PASTING lemma for pullbacks (one direction): pullbacks compose.**  Given an OUTER pullback of
`f₂` along `g` and an INNER pullback of `f₁` along the outer's left projection, the pasted square — same
apex as the inner, left projection the inner's, right projection the composite of the two right projections
— is a pullback of the COMPOSITE `f₁ ∘ f₂` along `g`.  This is the categorical content of Uemura AXIOM 3
(representable maps closed under composition AND stable under pullback): a composite of representables, pulled
back, is again (a composite of) representables. -/
def PullbackSquare.paste {category : RawCategory.{u, v}}
    {objectA₁ objectA₂ objectB objectC : category.Object}
    {morphismF₁ : category.Morphism objectA₁ objectA₂}
    {morphismF₂ : category.Morphism objectA₂ objectC}
    {morphismG : category.Morphism objectB objectC}
    (outer : PullbackSquare category morphismF₂ morphismG)
    (inner : PullbackSquare category morphismF₁ outer.projectionLeft) :
    PullbackSquare category (category.compose morphismF₁ morphismF₂) morphismG where
  pullbackObject := inner.pullbackObject
  projectionLeft := inner.projectionLeft
  projectionRight := category.compose inner.projectionRight outer.projectionRight
  commutes :=
    calc category.compose inner.projectionLeft (category.compose morphismF₁ morphismF₂)
        = category.compose (category.compose inner.projectionLeft morphismF₁) morphismF₂ :=
          (category.composeAssoc inner.projectionLeft morphismF₁ morphismF₂).symm
      _ = category.compose (category.compose inner.projectionRight outer.projectionLeft) morphismF₂ :=
          congrArg (fun morphism => category.compose morphism morphismF₂) inner.commutes
      _ = category.compose inner.projectionRight (category.compose outer.projectionLeft morphismF₂) :=
          category.composeAssoc inner.projectionRight outer.projectionLeft morphismF₂
      _ = category.compose inner.projectionRight (category.compose outer.projectionRight morphismG) :=
          congrArg (fun morphism => category.compose inner.projectionRight morphism) outer.commutes
      _ = category.compose (category.compose inner.projectionRight outer.projectionRight) morphismG :=
          (category.composeAssoc inner.projectionRight outer.projectionRight morphismG).symm
  isUniversal := fun candidateObject candidateLeft candidateRight cone => by
    have outerCone : category.compose (category.compose candidateLeft morphismF₁) morphismF₂
        = category.compose candidateRight morphismG :=
      (category.composeAssoc candidateLeft morphismF₁ morphismF₂).trans cone
    obtain ⟨mediatorOuter, mediatorOuterLeft, mediatorOuterRight⟩ :=
      outer.isUniversal candidateObject (category.compose candidateLeft morphismF₁) candidateRight outerCone
    obtain ⟨mediatorInner, mediatorInnerLeft, mediatorInnerRight⟩ :=
      inner.isUniversal candidateObject candidateLeft mediatorOuter mediatorOuterLeft.symm
    refine ⟨mediatorInner, mediatorInnerLeft, ?_⟩
    calc category.compose mediatorInner (category.compose inner.projectionRight outer.projectionRight)
        = category.compose (category.compose mediatorInner inner.projectionRight) outer.projectionRight :=
          (category.composeAssoc mediatorInner inner.projectionRight outer.projectionRight).symm
      _ = category.compose mediatorOuter outer.projectionRight :=
          congrArg (fun morphism => category.compose morphism outer.projectionRight) mediatorInnerRight
      _ = candidateRight := mediatorOuterRight

/-- The pasting of two STRICT pullbacks is strict. -/
theorem PullbackSquare.paste_isStrict {category : RawCategory.{u, v}}
    {objectA₁ objectA₂ objectB objectC : category.Object}
    {morphismF₁ : category.Morphism objectA₁ objectA₂}
    {morphismF₂ : category.Morphism objectA₂ objectC}
    {morphismG : category.Morphism objectB objectC}
    {outer : PullbackSquare category morphismF₂ morphismG}
    {inner : PullbackSquare category morphismF₁ outer.projectionLeft}
    (outerStrict : outer.IsStrict) (innerStrict : inner.IsStrict) :
    (outer.paste inner).IsStrict := by
  intro candidateObject mediatorOne mediatorTwo projLeftEq projRightEq
  have innerRightEq : category.compose mediatorOne inner.projectionRight
      = category.compose mediatorTwo inner.projectionRight := by
    apply outerStrict
    · calc category.compose (category.compose mediatorOne inner.projectionRight) outer.projectionLeft
          = category.compose mediatorOne (category.compose inner.projectionRight outer.projectionLeft) :=
            category.composeAssoc mediatorOne inner.projectionRight outer.projectionLeft
        _ = category.compose mediatorOne (category.compose inner.projectionLeft morphismF₁) :=
            congrArg (fun morphism => category.compose mediatorOne morphism) inner.commutes.symm
        _ = category.compose (category.compose mediatorOne inner.projectionLeft) morphismF₁ :=
            (category.composeAssoc mediatorOne inner.projectionLeft morphismF₁).symm
        _ = category.compose (category.compose mediatorTwo inner.projectionLeft) morphismF₁ :=
            congrArg (fun morphism => category.compose morphism morphismF₁) projLeftEq
        _ = category.compose mediatorTwo (category.compose inner.projectionLeft morphismF₁) :=
            category.composeAssoc mediatorTwo inner.projectionLeft morphismF₁
        _ = category.compose mediatorTwo (category.compose inner.projectionRight outer.projectionLeft) :=
            congrArg (fun morphism => category.compose mediatorTwo morphism) inner.commutes
        _ = category.compose (category.compose mediatorTwo inner.projectionRight) outer.projectionLeft :=
            (category.composeAssoc mediatorTwo inner.projectionRight outer.projectionLeft).symm
    · calc category.compose (category.compose mediatorOne inner.projectionRight) outer.projectionRight
          = category.compose mediatorOne (category.compose inner.projectionRight outer.projectionRight) :=
            category.composeAssoc mediatorOne inner.projectionRight outer.projectionRight
        _ = category.compose mediatorTwo (category.compose inner.projectionRight outer.projectionRight) :=
            projRightEq
        _ = category.compose (category.compose mediatorTwo inner.projectionRight) outer.projectionRight :=
            (category.composeAssoc mediatorTwo inner.projectionRight outer.projectionRight).symm
  exact innerStrict mediatorOne mediatorTwo projLeftEq innerRightEq

/-- A morphism is an isomorphism if it has a two-sided inverse. -/
structure IsIsomorphism (category : RawCategory.{u, v})
    {objectA objectB : category.Object}
    (morphism : category.Morphism objectA objectB) where
  inverse : category.Morphism objectB objectA
  leftInverse : category.compose inverse morphism = category.identity objectB
  rightInverse : category.compose morphism inverse = category.identity objectA

end FX1Poly.Polygraph
