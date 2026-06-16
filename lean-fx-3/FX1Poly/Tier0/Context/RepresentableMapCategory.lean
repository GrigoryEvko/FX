import FX1Poly.Tier0.Context.AxisObligation
/-!
# Representable Map Categories (Uemura 2023)

A representable map category (CwR) is a category C equipped with a
distinguished class of morphisms R ⊆ Mor(C) — the "representable maps" —
satisfying: closed under pullback, contains all isos, closed under
composition. Objects of CwR ARE type theories; morphisms are extensions.

Type formers (Π, Σ, Id, etc.) are representable natural transformations
in the slice C/U over the universe object.

This is the categorical substrate that ALL PolyCell axes plug into.
The eventual FX generator table should interpret its term and type former
entries as representable maps in the FX CwR.

Reference: Uemura, "A general framework for the semantics of type theory",
MSCS 33(3), 2023, arXiv:1904.04097 §2-3.

Zero external dependencies. Raw Lean 4 + Init only.
-/

namespace FX1Poly.Tier0

universe u v

/-- A category: objects + morphisms + composition + identity + laws.
Raw encoding without universe polymorphism issues — we keep it simple. -/
structure RawCategory where
  Object : Type u
  Morphism : Object → Object → Type v
  identity : (objectA : Object) → Morphism objectA objectA
  compose : {objectA objectB objectC : Object} →
            Morphism objectA objectB → Morphism objectB objectC →
            Morphism objectA objectC
  composeAssoc : ∀ {objectA objectB objectC objectD : Object}
    (morphismF : Morphism objectA objectB)
    (morphismG : Morphism objectB objectC)
    (morphismH : Morphism objectC objectD),
    compose (compose morphismF morphismG) morphismH =
    compose morphismF (compose morphismG morphismH)
  identityLeft : ∀ {objectA objectB : Object}
    (morphismF : Morphism objectA objectB),
    compose (identity objectA) morphismF = morphismF
  identityRight : ∀ {objectA objectB : Object}
    (morphismF : Morphism objectA objectB),
    compose morphismF (identity objectB) = morphismF

/-- A **functor** between two raw categories — maps objects and morphisms,
preserving identity and composition.  This is THE generic functor of the context
axis: `RawEndofunctor` (the lock carrier, `Context.lean`), the renaming ⊂
substitution inclusion (`RenamingInclusion.lean`), and the model functors all
specialise it rather than re-spelling these four fields. -/
structure RawFunctor (sourceCategory targetCategory : RawCategory.{u, v}) where
  /-- Action on objects. -/
  mapObject : sourceCategory.Object → targetCategory.Object
  /-- Action on morphisms. -/
  mapMorphism : {objectA objectB : sourceCategory.Object} →
                sourceCategory.Morphism objectA objectB →
                targetCategory.Morphism (mapObject objectA) (mapObject objectB)
  /-- Preserves identity. -/
  preservesIdentity : ∀ (objectA : sourceCategory.Object),
    mapMorphism (sourceCategory.identity objectA) =
      targetCategory.identity (mapObject objectA)
  /-- Preserves composition. -/
  preservesComposition :
    ∀ {objectA objectB objectC : sourceCategory.Object}
      (morphismF : sourceCategory.Morphism objectA objectB)
      (morphismG : sourceCategory.Morphism objectB objectC),
    mapMorphism (sourceCategory.compose morphismF morphismG) =
      targetCategory.compose (mapMorphism morphismF) (mapMorphism morphismG)

/-- The identity functor on a category — maps objects and morphisms to themselves. -/
def RawFunctor.identity (category : RawCategory.{u, v}) : RawFunctor category category where
  mapObject := fun object => object
  mapMorphism := fun morphism => morphism
  preservesIdentity := fun _ => rfl
  preservesComposition := fun _ _ => rfl

/-- **Composition of functors** (DIAGRAMMATIC order, matching `RawCategory.compose`):
`firstFunctor.compose secondFunctor` applies `firstFunctor` then `secondFunctor`.
Both functor laws are PROVED from the two factors'. -/
def RawFunctor.compose {sourceCategory midCategory targetCategory : RawCategory.{u, v}}
    (firstFunctor : RawFunctor sourceCategory midCategory)
    (secondFunctor : RawFunctor midCategory targetCategory) :
    RawFunctor sourceCategory targetCategory where
  mapObject := fun object => secondFunctor.mapObject (firstFunctor.mapObject object)
  mapMorphism := fun morphism => secondFunctor.mapMorphism (firstFunctor.mapMorphism morphism)
  preservesIdentity := fun objectA => by
    rw [firstFunctor.preservesIdentity, secondFunctor.preservesIdentity]
  preservesComposition := fun morphismF morphismG => by
    rw [firstFunctor.preservesComposition, secondFunctor.preservesComposition]

/-- The identity functor is a LEFT unit for composition — strict (`RawFunctor` eta). -/
theorem RawFunctor.identity_compose {sourceCategory targetCategory : RawCategory.{u, v}}
    (functor : RawFunctor sourceCategory targetCategory) :
    (RawFunctor.identity sourceCategory).compose functor = functor := rfl

/-- The identity functor is a RIGHT unit for composition. -/
theorem RawFunctor.compose_identity {sourceCategory targetCategory : RawCategory.{u, v}}
    (functor : RawFunctor sourceCategory targetCategory) :
    functor.compose (RawFunctor.identity targetCategory) = functor := rfl

/-- Functor composition is associative — strict.  With the two unit laws, raw
categories and `RawFunctor`s form a (large) category. -/
theorem RawFunctor.compose_assoc {categoryA categoryB categoryC categoryD : RawCategory.{u, v}}
    (firstFunctor : RawFunctor categoryA categoryB)
    (secondFunctor : RawFunctor categoryB categoryC)
    (thirdFunctor : RawFunctor categoryC categoryD) :
    (firstFunctor.compose secondFunctor).compose thirdFunctor
      = firstFunctor.compose (secondFunctor.compose thirdFunctor) := rfl

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

/-- A Representable Map Category (CwR): a category with a distinguished
class of "representable maps" satisfying three closure conditions.

This is Uemura's Definition 2.1 (arXiv:1904.04097 §2). -/
structure RepresentableMapCategory where
  /-- The underlying category. -/
  underlying : RawCategory.{u, v}

  /-- The distinguished class R of representable maps. -/
  representableMaps : MorphismClass underlying

  /-- AXIOM 1: Representable maps are closed under pullback.
  If f : A → C is representable and g : B → C is any morphism,
  the pullback of f along g exists and f* is representable. -/
  closedUnderPullback :
    ∀ {objectA objectB objectC : underlying.Object}
      (morphismF : underlying.Morphism objectA objectC)
      (morphismG : underlying.Morphism objectB objectC),
      representableMaps.member morphismF →
      ∃ (square : PullbackSquare underlying morphismF morphismG),
        representableMaps.member square.projectionRight

  /-- AXIOM 2: All isomorphisms are representable. -/
  isomorphismsRepresentable :
    ∀ {objectA objectB : underlying.Object}
      (morphism : underlying.Morphism objectA objectB),
      IsIsomorphism underlying morphism →
      representableMaps.member morphism

  /-- AXIOM 3: Representable maps are closed under composition. -/
  closedUnderComposition :
    ∀ {objectA objectB objectC : underlying.Object}
      (morphismF : underlying.Morphism objectA objectB)
      (morphismG : underlying.Morphism objectB objectC),
      representableMaps.member morphismF →
      representableMaps.member morphismG →
      representableMaps.member (underlying.compose morphismF morphismG)

/-- A CwR-morphism (functor preserving representable maps) — the generic
`RawFunctor` between the two underlying categories PLUS preservation of the
representable class.  Inheriting `RawFunctor`'s four functor fields (rather than
re-spelling them) means the `mapObject` / `mapMorphism` / `preservesIdentity` /
`preservesComposition` projections and the generic functor API apply directly. -/
structure CwRMorphism (sourceCwR targetCwR : RepresentableMapCategory.{u, v})
    extends RawFunctor sourceCwR.underlying targetCwR.underlying where
  /-- PRESERVES REPRESENTABILITY: maps representable to representable. -/
  preservesRepresentable :
    ∀ {objectA objectB : sourceCwR.underlying.Object}
      (morphism : sourceCwR.underlying.Morphism objectA objectB),
    sourceCwR.representableMaps.member morphism →
    targetCwR.representableMaps.member (mapMorphism morphism)

/-- Identity CwR-morphism. -/
def CwRMorphism.identity (cwrCategory : RepresentableMapCategory.{u, v}) :
    CwRMorphism cwrCategory cwrCategory where
  mapObject := id
  mapMorphism := id
  preservesIdentity := fun _ => rfl
  preservesComposition := fun _ _ => rfl
  preservesRepresentable := fun _ memberWitness => memberWitness

/-- A CwR-morphism is conservative (= faithful + essentially surjective
on representable maps) when it reflects representable maps. -/
def CwRMorphism.isConservative
    {sourceCwR targetCwR : RepresentableMapCategory.{u, v}}
    (morphism : CwRMorphism sourceCwR targetCwR) : Prop :=
  ∀ {objectA objectB : sourceCwR.underlying.Object}
    (sourceMorphism : sourceCwR.underlying.Morphism objectA objectB),
    targetCwR.representableMaps.member (morphism.mapMorphism sourceMorphism) →
    sourceCwR.representableMaps.member sourceMorphism

end FX1Poly.Tier0
